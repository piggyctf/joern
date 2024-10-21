package io.joern.javasrc2cpg.astcreation.expressions

import com.github.javaparser.ast.expr.{InstanceOfExpr, NameExpr, PatternExpr}
import io.joern.javasrc2cpg.astcreation.{AstCreator, ExpectedType}
import io.joern.javasrc2cpg.jartypereader.model.Model.TypeConstants
import io.joern.x2cpg.Ast
import io.joern.x2cpg.utils.AstPropertiesUtil.*
import io.shiftleft.codepropertygraph.generated.nodes.NewIdentifier
import io.joern.x2cpg.utils.NodeBuilders.*
import io.shiftleft.codepropertygraph.generated.Operators

trait AstForPatternExpressionsCreator { this: AstCreator =>

  private[astcreation] def astForInstanceOfWithPattern(instanceOfExpr: InstanceOfExpr, pattern: PatternExpr): Ast = {
    // If the LHS is not an identifier, create a temp variable and assignment for it

    // TODO: handle multiple ASTs
    val exprAst = astsForExpression(instanceOfExpr.getExpression, ExpectedType.empty).head

    val lhsAst = exprAst.nodes.toList match {
      case (_: NewIdentifier) :: Nil => exprAst

      case _ =>
        val tmpName       = tempNameProvider.next
        val tmpType       = exprAst.rootType.getOrElse(TypeConstants.Object)
        val tmpLocal      = localNode(instanceOfExpr.getExpression, tmpName, tmpName, tmpType)
        val tmpIdentifier = identifierNode(instanceOfExpr.getExpression, tmpName, tmpName, tmpType)

        val tmpAssignmentNode =
          newOperatorCallNode(Operators.assignment, s"$tmpName = ${exprAst.rootCodeOrEmpty}", Option(tmpType))

        // TODO Handle patterns in field initializers
        // Don't need to add the local to the block scope since the only identifiers referencing it are created here
        // (so a lookup for the local will never be done)
        scope.enclosingMethod.foreach(_.addTemporaryLocal(tmpLocal))

        callAst(tmpAssignmentNode, Ast(tmpIdentifier) :: exprAst :: Nil).withRefEdge(tmpIdentifier, tmpLocal)
    }

    val patternTypeFullName =
      tryWithSafeStackOverflow(typeInfoCalc.fullName(pattern.getType)).toOption.flatten.getOrElse(TypeConstants.Any)

    val patternTypeRef = typeRefNode(pattern.getType, patternTypeFullName, patternTypeFullName)

    // TODO Create pattern variable local + initializer and add to scope

    val instanceOfCall = newOperatorCallNode(
      Operators.instanceOf,
      s"${code(instanceOfExpr.getExpression)} instanceof $patternTypeFullName",
      Option(TypeConstants.Boolean)
    )

    callAst(instanceOfCall, lhsAst :: Ast(patternTypeRef) :: Nil)
  }
}
