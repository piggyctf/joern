package io.joern.javasrc2cpg.astcreation.statements

import com.github.javaparser.ast.expr.TypePatternExpr
import com.github.javaparser.ast.stmt.{
  AssertStmt,
  BlockStmt,
  BreakStmt,
  CatchClause,
  ContinueStmt,
  DoStmt,
  ExplicitConstructorInvocationStmt,
  IfStmt,
  LabeledStmt,
  ReturnStmt,
  Statement,
  SwitchEntry,
  SwitchStmt,
  SynchronizedStmt,
  ThrowStmt,
  TryStmt,
  WhileStmt
}
import com.github.javaparser.symbolsolver.javaparsermodel.contexts.{
  DoStatementContext,
  IfStatementContext,
  WhileStatementContext
}
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver
import io.joern.javasrc2cpg.astcreation.{AstCreator, ExpectedType}
import io.joern.javasrc2cpg.typesolvers.TypeInfoCalculator.TypeConstants
import io.joern.javasrc2cpg.util.NameConstants
import io.joern.x2cpg.Ast
import io.joern.x2cpg.utils.NodeBuilders.{newIdentifierNode, newModifierNode}
import io.shiftleft.codepropertygraph.generated.nodes.{NewBlock, NewCall, NewControlStructure, NewJumpTarget, NewReturn}
import io.shiftleft.codepropertygraph.generated.{ControlStructureTypes, DispatchTypes, EdgeTypes}

import scala.jdk.CollectionConverters.*
import scala.jdk.OptionConverters.RichOptional
import io.joern.javasrc2cpg.scope.JavaScopeElement.PartialInit
import org.slf4j.LoggerFactory

// TODO proper comment, but `body` means `then` for if stmt
private case class PatternAstPartition(
  patternsIntroducedToBody: List[TypePatternExpr],
  patternsIntroducedToElse: List[TypePatternExpr],
  patternsIntroducedByStatement: List[TypePatternExpr],
  astsAddedBeforeStatement: List[Ast],
  astsAddedToBody: List[Ast],
  astsAddedToElse: List[Ast],
  astsAddedAfterStatement: List[Ast]
)

trait AstForSimpleStatementsCreator { this: AstCreator =>
  private val logger = LoggerFactory.getLogger(this.getClass)

  def astForBlockStatement(
    stmt: BlockStmt,
    codeStr: String = "<empty>",
    prefixAsts: Seq[Ast] = Seq.empty,
    includeTemporaryLocals: Boolean = false
  ): Ast = {
    val block = NewBlock()
      .code(codeStr)
      .lineNumber(line(stmt))
      .columnNumber(column(stmt))

    scope.pushBlockScope()

    val stmtAsts = stmt.getStatements.asScala.flatMap(astsForStatement)

    val temporaryLocalAsts =
      if (includeTemporaryLocals)
        scope.enclosingMethod.map(_.getTemporaryLocals).getOrElse(Nil).map(Ast(_))
      else
        Nil

    scope.popBlockScope()
    Ast(block)
      .withChildren(temporaryLocalAsts)
      .withChildren(prefixAsts)
      .withChildren(stmtAsts)
  }

  private[statements] def astForExplicitConstructorInvocation(stmt: ExplicitConstructorInvocationStmt): Ast = {
    // TODO Handle super
    val maybeResolved = tryWithSafeStackOverflow(stmt.resolve())
    val args          = argAstsForCall(stmt, maybeResolved, stmt.getArguments)
    val argTypes      = argumentTypesForMethodLike(maybeResolved)

    val typeFullName = maybeResolved.toOption
      .map(_.declaringType())
      .flatMap(typ => scope.lookupType(typ.getName).orElse(typeInfoCalc.fullName(typ)))

    val callRoot = initNode(
      typeFullName.orElse(Some(TypeConstants.Any)),
      argTypes,
      args.size,
      stmt.toString,
      line(stmt),
      column(stmt)
    )

    val thisNode = newIdentifierNode(NameConstants.This, typeFullName.getOrElse(TypeConstants.Any))
    scope.lookupVariable(NameConstants.This).variableNode.foreach { thisParam =>
      diffGraph.addEdge(thisNode, thisParam, EdgeTypes.REF)
    }
    val thisAst = Ast(thisNode)

    val initAst = Ast(callRoot)

    // callAst(callRoot, args, Some(thisAst))
    scope.enclosingTypeDecl.foreach(
      _.registerInitToComplete(
        PartialInit(typeFullName.getOrElse(TypeConstants.Any), initAst, thisAst, args.toList, None)
      )
    )
    initAst
  }

  private[statements] def astForAssertStatement(stmt: AssertStmt): Ast = {
    val callNode = NewCall()
      .name("assert")
      .methodFullName("assert")
      .dispatchType(DispatchTypes.STATIC_DISPATCH)
      .code(code(stmt))
      .lineNumber(line(stmt))
      .columnNumber(column(stmt))

    val args = astsForExpression(stmt.getCheck, ExpectedType.Boolean)
    callAst(callNode, args)
  }

  private[statements] def astForBreakStatement(stmt: BreakStmt): Ast = {
    val node = NewControlStructure()
      .controlStructureType(ControlStructureTypes.BREAK)
      .lineNumber(line(stmt))
      .columnNumber(column(stmt))
      .code(code(stmt))
    Ast(node)
  }

  private[statements] def astForContinueStatement(stmt: ContinueStmt): Ast = {
    val node = NewControlStructure()
      .controlStructureType(ControlStructureTypes.CONTINUE)
      .lineNumber(line(stmt))
      .columnNumber(column(stmt))
      .code(code(stmt))
    Ast(node)
  }

  private[statements] def astsForDo(stmt: DoStmt): List[Ast] = {
    val conditionAst = astsForExpression(stmt.getCondition, ExpectedType.Boolean).headOption

    val doContext = new DoStatementContext(stmt, new CombinedTypeSolver())

    val patternPartition = partitionPatternAstsByScope(doContext)

    scope.pushBlockScope()
    scope.addLocalsForPatternsToEnclosingBlock(patternPartition.patternsIntroducedToBody)
    val bodyAst = wrapInBlockWithPrefix(stmt.getBody, patternPartition.astsAddedToBody)
    scope.popBlockScope()

    scope.addLocalsForPatternsToEnclosingBlock(patternPartition.patternsIntroducedByStatement)

    val code         = s"do {...} while (${stmt.getCondition.toString})"
    val lineNumber   = line(stmt)
    val columnNumber = column(stmt)

    val ast = doWhileAst(conditionAst, List(bodyAst), Some(code), lineNumber, columnNumber)
    patternPartition.astsAddedBeforeStatement ++ (ast :: patternPartition.astsAddedAfterStatement)
  }

  private[statements] def astsForWhile(stmt: WhileStmt): List[Ast] = {
    val conditionAst = astsForExpression(stmt.getCondition, ExpectedType.Boolean).headOption

    val whileContext = new WhileStatementContext(stmt, new CombinedTypeSolver())

    val patternPartition = partitionPatternAstsByScope(whileContext)

    scope.pushBlockScope()
    scope.addLocalsForPatternsToEnclosingBlock(patternPartition.patternsIntroducedToBody)
    val bodyAst = wrapInBlockWithPrefix(stmt.getBody, patternPartition.astsAddedToBody)
    scope.popBlockScope()

    scope.addLocalsForPatternsToEnclosingBlock(patternPartition.patternsIntroducedByStatement)

    val code         = s"while (${stmt.getCondition.toString})"
    val lineNumber   = line(stmt)
    val columnNumber = column(stmt)

    val ast = whileAst(conditionAst, List(bodyAst), Some(code), lineNumber, columnNumber)
    patternPartition.astsAddedBeforeStatement ++ (ast :: patternPartition.astsAddedAfterStatement)
  }

  private[statements] def astsForIf(stmt: IfStmt): Seq[Ast] = {
    val ifNode =
      NewControlStructure()
        .controlStructureType(ControlStructureTypes.IF)
        .lineNumber(line(stmt))
        .columnNumber(column(stmt))
        .code(s"if (${stmt.getCondition.toString})")

    val conditionAst =
      astsForExpression(stmt.getCondition, ExpectedType.Boolean).headOption.toList

    val ifContext = new IfStatementContext(stmt, new CombinedTypeSolver())

    val patternPartition = partitionPatternAstsByScope(ifContext)

    scope.pushBlockScope()
    scope.addLocalsForPatternsToEnclosingBlock(patternPartition.patternsIntroducedToBody)
    val thenAst = stmt.getThenStmt match {
      case blockStmt: BlockStmt => astForBlockStatement(blockStmt, prefixAsts = patternPartition.astsAddedToBody)

      case stmt: Statement =>
        val elseStmts = astsForStatement(stmt)
        blockAst(blockNode(stmt), patternPartition.astsAddedToBody ++ elseStmts)
    }
    scope.popBlockScope()

    scope.pushBlockScope()
    scope.addLocalsForPatternsToEnclosingBlock(patternPartition.patternsIntroducedToElse)
    val elseAst = stmt.getElseStmt.toScala.map {
      case blockStmt: BlockStmt => astForBlockStatement(blockStmt, prefixAsts = patternPartition.astsAddedToElse)

      case stmt: Statement =>
        val elseStmts = astsForStatement(stmt)
        blockAst(blockNode(stmt), patternPartition.astsAddedToElse ++ elseStmts)
    }
    scope.popBlockScope()

    scope.addLocalsForPatternsToEnclosingBlock(patternPartition.patternsIntroducedByStatement)
    val ast = Ast(ifNode)
      .withChildren(conditionAst)
      .withChild(thenAst)
      .withChildren(elseAst.toList)

    val astWithConditionEdge = conditionAst.flatMap(_.root.toList) match {
      case r :: Nil =>
        ast.withConditionEdge(ifNode, r)
      case _ =>
        ast
    }

    patternPartition.astsAddedBeforeStatement ++ (astWithConditionEdge :: patternPartition.astsAddedAfterStatement)
  }

  private[statements] def astForElse(maybeStmt: Option[Statement]): Option[Ast] = {
    maybeStmt.map { stmt =>
      val elseAsts = astsForStatement(stmt)

      val elseNode =
        NewControlStructure()
          .controlStructureType(ControlStructureTypes.ELSE)
          .lineNumber(line(stmt))
          .columnNumber(column(stmt))
          .code("else")

      Ast(elseNode).withChildren(elseAsts)
    }
  }

  private[statements] def astForSwitchStatement(stmt: SwitchStmt): Ast = {
    val switchNode =
      NewControlStructure()
        .controlStructureType(ControlStructureTypes.SWITCH)
        .code(s"switch(${stmt.getSelector.toString})")

    val selectorAsts = astsForExpression(stmt.getSelector, ExpectedType.empty)
    val selectorNode = selectorAsts.head.root.get

    val entryAsts = stmt.getEntries.asScala.flatMap(astForSwitchEntry)

    val switchBodyAst = Ast(NewBlock()).withChildren(entryAsts)

    Ast(switchNode)
      .withChildren(selectorAsts)
      .withChild(switchBodyAst)
      .withConditionEdge(switchNode, selectorNode)
  }

  private[statements] def astForSynchronizedStatement(stmt: SynchronizedStmt): Ast = {
    val parentNode =
      NewBlock()
        .lineNumber(line(stmt))
        .columnNumber(column(stmt))

    val modifier = Ast(newModifierNode("SYNCHRONIZED"))

    val exprAsts = astsForExpression(stmt.getExpression, ExpectedType.empty)
    val bodyAst  = astForBlockStatement(stmt.getBody)

    Ast(parentNode)
      .withChild(modifier)
      .withChildren(exprAsts)
      .withChild(bodyAst)
  }

  private[statements] def astsForSwitchCases(entry: SwitchEntry): Seq[Ast] = {
    entry.getLabels.asScala.toList match {
      case Nil =>
        val target = NewJumpTarget()
          .name("default")
          .code("default")
        Seq(Ast(target))

      case labels =>
        labels.flatMap { label =>
          val jumpTarget = NewJumpTarget()
            .name("case")
            .code(label.toString)
          val labelAsts = astsForExpression(label, ExpectedType.empty).toList

          Ast(jumpTarget) :: labelAsts
        }
    }
  }

  private[statements] def astForSwitchEntry(entry: SwitchEntry): Seq[Ast] = {
    val labelAsts = astsForSwitchCases(entry)

    val statementAsts = entry.getStatements.asScala.flatMap(astsForStatement)

    labelAsts ++ statementAsts
  }

  private[statements] def astForReturnNode(ret: ReturnStmt): Ast = {
    val returnNode = NewReturn()
      .lineNumber(line(ret))
      .columnNumber(column(ret))
      .code(code(ret))
    if (ret.getExpression.isPresent) {
      val expectedType = scope.enclosingMethodReturnType.getOrElse(ExpectedType.empty)
      val exprAsts     = astsForExpression(ret.getExpression.get(), expectedType)
      returnAst(returnNode, exprAsts)
    } else {
      Ast(returnNode)
    }
  }

  private[statements] def astsForLabeledStatement(stmt: LabeledStmt): Seq[Ast] = {
    val jumpTargetAst = Ast(NewJumpTarget().name(stmt.getLabel.toString))
    val stmtAst       = astsForStatement(stmt.getStatement).toList

    jumpTargetAst :: stmtAst
  }

  private[statements] def astForThrow(stmt: ThrowStmt): Ast = {
    val throwNode = NewCall()
      .name("<operator>.throw")
      .methodFullName("<operator>.throw")
      .lineNumber(line(stmt))
      .columnNumber(column(stmt))
      .code(code(stmt))
      .dispatchType(DispatchTypes.STATIC_DISPATCH)

    val args = astsForExpression(stmt.getExpression, ExpectedType.empty)

    callAst(throwNode, args)
  }

  private[statements] def astForCatchClause(catchClause: CatchClause): Ast = {
    astForBlockStatement(catchClause.getBody)
  }

  private[statements] def astsForTry(stmt: TryStmt): Seq[Ast] = {
    val tryNode   = controlStructureNode(stmt, ControlStructureTypes.TRY, "try")
    val resources = stmt.getResources.asScala.flatMap(astsForExpression(_, expectedType = ExpectedType.empty)).toList

    val tryAst = astForBlockStatement(stmt.getTryBlock, codeStr = "try")
    val catchAsts = stmt.getCatchClauses.asScala.toList.map { catchClause =>
      val catchNode = controlStructureNode(catchClause, ControlStructureTypes.CATCH, "catch")
      Ast(catchNode).withChild(astForCatchClause(catchClause))
    }
    val finallyAst = stmt.getFinallyBlock.toScala.map { finallyBlock =>
      val finallyNode = controlStructureNode(finallyBlock, ControlStructureTypes.FINALLY, "finally")
      Ast(finallyNode).withChild(astForBlockStatement(finallyBlock, "finally"))
    }
    val controlStructureAst = tryCatchAst(tryNode, tryAst, catchAsts, finallyAst)
    resources.appended(controlStructureAst)
  }
}
