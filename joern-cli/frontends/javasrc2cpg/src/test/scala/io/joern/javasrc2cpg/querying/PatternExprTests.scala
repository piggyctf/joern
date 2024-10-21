package io.joern.javasrc2cpg.querying

import io.joern.javasrc2cpg.testfixtures.JavaSrcCode2CpgFixture
import io.shiftleft.codepropertygraph.generated.Operators
import io.shiftleft.codepropertygraph.generated.nodes.{Call, Identifier, Local}
import io.shiftleft.semanticcpg.language.*

class PatternExprTests extends JavaSrcCode2CpgFixture {

  "a pattern matching instanceof with a call lhs" should {
    val cpg = code("""
        |class Test {
        |  static String foo() {
        |    return "Hello, world!";
        |  }
        |
        |  static void sink(String s) { /* Do nothing */ }
        |
        |  void test(Object o) {
        |    if (foo() instanceof String s) {
        |      sink(s);
        |    }
        |  }
        |}
        |""".stripMargin)

    "parse" in {
      cpg.call.name("sink").size shouldBe 1
    }

    "add a tmp local for the foo call to the start of the method" in {
      inside(cpg.method.name("test").body.astChildren.l) { case (tmpLocal: Local) :: _ =>
        tmpLocal.name shouldBe "$obj0"
        tmpLocal.code shouldBe "$obj0"
        tmpLocal.typeFullName shouldBe "java.lang.String"
      }
    }

    "create an assignment for the temporary local as the first instanceof argument" in {
      inside(cpg.call.nameExact(Operators.instanceOf).argument.head) { case assignment: Call =>
        assignment.name shouldBe Operators.assignment
        assignment.typeFullName shouldBe "java.lang.String"
        assignment.code shouldBe "$obj0 = foo()"

        inside(assignment.argument.l) { case List(tmpIdentifier: Identifier, fooCall: Call) =>
          tmpIdentifier.name shouldBe "$obj0"
          tmpIdentifier.code shouldBe "$obj0"
          tmpIdentifier.typeFullName shouldBe "java.lang.String"
          tmpIdentifier.refsTo.l shouldBe cpg.local.nameExact("$obj0").l

          fooCall.name shouldBe "foo"
          fooCall.methodFullName shouldBe "Test.foo:java.lang.String()"
          fooCall.typeFullName shouldBe "java.lang.String"
          fooCall.code shouldBe "foo()"
        }
      }
    }
  }
}
