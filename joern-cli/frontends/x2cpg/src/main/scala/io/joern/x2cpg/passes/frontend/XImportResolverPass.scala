package io.joern.x2cpg.passes.frontend

import io.joern.x2cpg.passes.frontend.ImportsPass.ResolvedImport
import io.joern.x2cpg.passes.frontend.ImportsPass.ResolvedImport.*
import io.shiftleft.codepropertygraph.Cpg
import io.shiftleft.codepropertygraph.generated.nodes.{Call, Import, Tag}
import io.shiftleft.passes.ConcurrentWriterCpgPass
import io.shiftleft.semanticcpg.language.*
import org.slf4j.{Logger, LoggerFactory}

import java.io.File as JFile
import java.nio.charset.StandardCharsets
import java.util.Base64

abstract class XImportResolverPass(cpg: Cpg) extends ConcurrentWriterCpgPass[Import](cpg) {

  protected val logger: Logger   = LoggerFactory.getLogger(this.getClass)
  protected val codeRoot: String = cpg.metaData.root.headOption.getOrElse(JFile.separator)

  override def generateParts(): Array[Import] = cpg.imports.toArray

  override def runOnPart(builder: DiffGraphBuilder, part: Import): Unit = for {
    call <- part.call
    fileName = call.file.name.headOption.getOrElse("<unknown>").stripPrefix(codeRoot)
    importedAs     <- part.importedAs
    importedEntity <- part.importedEntity
  } {
    optionalResolveImport(fileName, call, importedEntity, importedAs, builder)
  }

  protected def optionalResolveImport(
    fileName: String,
    importCall: Call,
    importedEntity: String,
    importedAs: String,
    diffGraph: DiffGraphBuilder
  ): Unit

  protected def resolvedImportToTag(x: ResolvedImport, importCall: Call, diffGraph: DiffGraphBuilder): Unit =
    importCall.start.newTagNodePair(x.label, x.serialize).store()(diffGraph)

}

object ImportsPass {

  private val sep = ","

  sealed trait ResolvedImport {
    def label: String

    def serialize: String

    def alias: String
  }

  implicit class CallToResolvedImportExt(traversal: Iterator[Call]) {

    def toResolvedImport: Iterator[ResolvedImport] =
      traversal
        .flatMap(c =>
          c.referencedImports.flatMap(i =>
            for {
              alias <- i.importedAs
            } yield c.tag.toResolvedImport(alias)
          )
        )
        .flatten
        .distinct

  }

  implicit class TagToResolvedImportExt(traversal: Iterator[Tag]) {
    def toResolvedImport(alias: String): Iterator[ResolvedImport] =
      traversal.flatMap(ResolvedImport.tagToResolvedImport(_, alias))
  }

  object ResolvedImport {

    val RESOLVED_METHOD    = "RESOLVED_METHOD"
    val RESOLVED_TYPE_DECL = "RESOLVED_TYPE_DECL"
    val RESOLVED_MEMBER    = "RESOLVED_MEMBER"
    val UNKNOWN_METHOD     = "UNKNOWN_METHOD"
    val UNKNOWN_TYPE_DECL  = "UNKNOWN_TYPE_DECL"
    val UNKNOWN_IMPORT     = "UNKNOWN_IMPORT"

    val OPT_FULL_NAME = "FULL_NAME"
    val OPT_ALIAS     = "ALIAS"
    val OPT_RECEIVER  = "RECEIVER"
    val OPT_BASE_PATH = "BASE_PATH"
    val OPT_NAME      = "NAME"

    def tagToResolvedImport(tag: Tag, alias: String): Option[ResolvedImport] = Option(tag.name match {
      case RESOLVED_METHOD =>
        val opts = valueToOptions(tag.value)
        ResolvedMethod(opts(OPT_FULL_NAME), opts(OPT_ALIAS), opts.get(OPT_RECEIVER))
      case RESOLVED_TYPE_DECL => ResolvedTypeDecl(tag.value, alias)
      case RESOLVED_MEMBER =>
        val opts = valueToOptions(tag.value)
        ResolvedMember(opts(OPT_BASE_PATH), opts(OPT_NAME), alias)
      case UNKNOWN_METHOD =>
        val opts = valueToOptions(tag.value)
        UnknownMethod(opts(OPT_FULL_NAME), opts(OPT_ALIAS), opts.get(OPT_RECEIVER))
      case UNKNOWN_TYPE_DECL => UnknownTypeDecl(tag.value, alias)
      case UNKNOWN_IMPORT    => UnknownImport(tag.value, alias)
      case _                 => null
    })

    private def valueToOptions(x: String): Map[String, String] =
      x.split(sep).grouped(2).map(xs => xs(0) -> xs(1).decode).toMap

  }

  implicit class Base64StringExt(str: String) {

    def encode: String = Base64.getEncoder.encodeToString(str.getBytes(StandardCharsets.UTF_8))

    def decode: String = new String(Base64.getDecoder.decode(str.getBytes), StandardCharsets.UTF_8)

  }

  case class ResolvedMethod(
    fullName: String,
    alias: String,
    receiver: Option[String] = None,
    override val label: String = RESOLVED_METHOD
  ) extends ResolvedImport {
    override def serialize: String =
      (Seq(OPT_FULL_NAME, fullName.encode, OPT_ALIAS, alias.encode) ++ receiver
        .map(r => Seq(OPT_RECEIVER, r.encode))
        .getOrElse(Seq.empty))
        .mkString(sep)
  }

  case class ResolvedTypeDecl(
    fullName: String,
    override val alias: String,
    override val label: String = RESOLVED_TYPE_DECL
  ) extends ResolvedImport {
    override def serialize: String = fullName
  }

  case class ResolvedMember(
    basePath: String,
    memberName: String,
    override val alias: String,
    override val label: String = RESOLVED_MEMBER
  ) extends ResolvedImport {
    override def serialize: String = Seq(OPT_BASE_PATH, basePath.encode, OPT_NAME, memberName.encode).mkString(sep)
  }

  case class UnknownMethod(
    fullName: String,
    alias: String,
    receiver: Option[String] = None,
    override val label: String = UNKNOWN_METHOD
  ) extends ResolvedImport {
    override def serialize: String =
      (Seq(OPT_FULL_NAME, fullName.encode, OPT_ALIAS, alias.encode) ++ receiver
        .map(r => Seq(OPT_RECEIVER, r.encode))
        .getOrElse(Seq.empty))
        .mkString(sep)
  }

  case class UnknownTypeDecl(
    fullName: String,
    override val alias: String,
    override val label: String = UNKNOWN_TYPE_DECL
  ) extends ResolvedImport {
    override def serialize: String = fullName
  }

  case class UnknownImport(path: String, override val alias: String, override val label: String = UNKNOWN_IMPORT)
      extends ResolvedImport {
    override def serialize: String = path
  }
}
