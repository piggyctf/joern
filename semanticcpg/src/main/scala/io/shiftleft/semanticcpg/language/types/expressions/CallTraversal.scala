package io.shiftleft.semanticcpg.language.types.expressions

import io.shiftleft.codepropertygraph.generated.v2.nodes.*
import io.shiftleft.semanticcpg.language.*

/** A call site */
class CallTraversal(val traversal: Iterator[Call]) extends AnyVal {

  /** Only statically dispatched calls */
  def isStatic: Iterator[Call] =
    traversal.filter(_.isStatic)

  /** Only dynamically dispatched calls */
  def isDynamic: Iterator[Call] =
    traversal.filter(_.isDynamic)

  /** The receiver of a call if the call has a receiver associated. */
//  def receiver: Iterator[Expression] =
//    traversal.flatMap(_.receiver)

//  /** Arguments of the call
//    */
//  def argument: Iterator[Expression] =
//    traversal.flatMap(_.argument)
//
//  /** `i'th` arguments of the call
//    */
//  def argument(i: Integer): Iterator[Expression] =
//    traversal.flatMap(_.arguments(i))
//
//  /** To formal method return parameter
//    */
//  def toMethodReturn(implicit callResolver: ICallResolver): Iterator[MethodReturn] =
//    traversal
//      .flatMap(callResolver.getCalledMethodsAsTraversal)
//      .flatMap(_.methodReturn)
//
}
