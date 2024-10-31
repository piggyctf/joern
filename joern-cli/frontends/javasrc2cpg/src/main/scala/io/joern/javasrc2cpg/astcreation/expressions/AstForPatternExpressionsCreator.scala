package io.joern.javasrc2cpg.astcreation.expressions

import com.github.javaparser.ast.expr.{InstanceOfExpr, NameExpr, PatternExpr, RecordPatternExpr, TypePatternExpr}
import io.joern.javasrc2cpg.astcreation.{AstCreator, ExpectedType}
import io.joern.javasrc2cpg.jartypereader.model.Model.TypeConstants
import io.joern.x2cpg.Ast
import io.joern.x2cpg.utils.AstPropertiesUtil.*
import io.shiftleft.codepropertygraph.generated.nodes.{AstNodeNew, NewIdentifier}
import io.joern.x2cpg.utils.NodeBuilders.*
import io.shiftleft.codepropertygraph.generated.Operators

import scala.jdk.CollectionConverters.*

trait AstForPatternExpressionsCreator { this: AstCreator =>

  private[astcreation] def astForInstanceOfWithPattern(instanceOfExpr: InstanceOfExpr, pattern: PatternExpr): Ast = {
    val expression = instanceOfExpr.getExpression
    // TODO: handle multiple ASTs
    val exprAst = astsForExpression(expression, ExpectedType.empty).head

    val (lhsAst, lhsIdentifier) = exprAst.nodes.toList match {
      case (identifier: NewIdentifier) :: Nil => (exprAst, identifier)

      case _ =>
        val tmpName       = tempNameProvider.next
        val tmpType       = exprAst.rootType.getOrElse(TypeConstants.Object)
        val tmpLocal      = localNode(expression, tmpName, tmpName, tmpType)
        val tmpIdentifier = identifierNode(expression, tmpName, tmpName, tmpType)

        val tmpAssignmentNode =
          newOperatorCallNode(
            Operators.assignment,
            s"$tmpName = ${exprAst.rootCodeOrEmpty}",
            Option(tmpType),
            line(expression),
            column(expression)
          )

        // TODO Handle patterns in field initializers
        // Don't need to add the local to the block scope since the only identifiers referencing it are created here
        // (so a lookup for the local will never be done)
        scope.enclosingMethod.foreach(_.addTemporaryLocal(tmpLocal))

        (
          callAst(tmpAssignmentNode, Ast(tmpIdentifier) :: exprAst :: Nil).withRefEdge(tmpIdentifier, tmpLocal),
          tmpIdentifier
        )
    }

    val patternTypeFullName =
      tryWithSafeStackOverflow(typeInfoCalc.fullName(pattern.getType)).toOption.flatten.getOrElse(TypeConstants.Any)

    val patternTypeRef = typeRefNode(pattern.getType, patternTypeFullName, patternTypeFullName)

    // TODO Create pattern variable local + initializer and add to scope
    // TODO Make sure names are mangled where necessary
    val typePatterns = getTypePatterns(pattern)

    typePatterns.foreach { typePatternExpr =>
      val variableName = typePatternExpr.getNameAsString
      val variableType = tryWithSafeStackOverflow(typeInfoCalc.fullName(typePatternExpr.getType)).toOption.flatten
        .getOrElse(TypeConstants.Any)
      val variableTypeCode = tryWithSafeStackOverflow(code(typePatternExpr.getType)).getOrElse(variableType)

      val patternLocal      = localNode(typePatternExpr, variableName, code(typePatternExpr), variableType)
      val patternIdentifier = identifierNode(typePatternExpr, variableName, code(typePatternExpr), variableType)
      // TODO Handle record pattern initializers
      val patternInitializerCastType = typeRefNode(typePatternExpr, variableTypeCode, variableType)
      val patternInitializerCastRhs  = lhsIdentifier.copy
      val patternInitializerCast = newOperatorCallNode(
        Operators.cast,
        s"($variableTypeCode) ${lhsIdentifier.code}",
        Option(variableType),
        line(typePatternExpr),
        column(typePatternExpr)
      )

      val initializerCastAst =
        callAst(patternInitializerCast, Ast(patternInitializerCastType) :: Ast(patternInitializerCastRhs) :: Nil)
          .withRefEdge(patternInitializerCastRhs, patternLocal)

      val initializerAssignmentCall = newOperatorCallNode(
        Operators.assignment,
        s"$variableName = ${patternInitializerCast.code}",
        Option(variableType),
        line(typePatternExpr),
        column(typePatternExpr)
      )
      val initializerAssignmentAst = callAst(
        initializerAssignmentCall,
        Ast(patternIdentifier) :: initializerCastAst :: Nil
      ).withRefEdge(patternIdentifier, patternLocal)

      scope.enclosingMethod.foreach { methodScope =>
        methodScope.putPatternVariableInfo(typePatternExpr, patternLocal, initializerAssignmentAst)
      }
    }

    val instanceOfCall = newOperatorCallNode(
      Operators.instanceOf,
      s"${code(instanceOfExpr.getExpression)} instanceof $patternTypeFullName",
      Option(TypeConstants.Boolean)
    )

    callAst(instanceOfCall, lhsAst :: Ast(patternTypeRef) :: Nil)
  }

  private def getTypePatterns(expr: PatternExpr): List[TypePatternExpr] = {
    expr match {
      case typePatternExpr: TypePatternExpr => typePatternExpr :: Nil

      case recordPatternExpr: RecordPatternExpr =>
        recordPatternExpr.getPatternList.asScala.toList.flatMap(getTypePatterns)
    }
  }
}
