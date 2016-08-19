
package firrtlTests

import org.scalatest.FlatSpec

import firrtl.{Parser, Compiler, VerilogCompiler, HighFirrtlCompiler}
import firrtl.Annotations.AnnotationMap

class InlineVerilogSpec extends FlatSpec {
  private def runCompiler(input: String, compiler: Compiler): String = {
    val writer = new java.io.StringWriter
    val parsedInput = firrtl.Parser.parse(input split ("\n"))
    compiler.compile(parsedInput, AnnotationMap(Seq.empty), writer)
    writer.toString
  }
  private def toVerilog(input: String): String =
    runCompiler(input, new VerilogCompiler)
  private def toFirrtl(input: String): String =
    runCompiler(input, new HighFirrtlCompiler)
  // Compare firrtl code ignoring surrounding whitespace and empty lines
  private def compareFirrtl(a: String, b: String): Boolean = {
    (a split ("\n") map (_.trim)).toSet === (b split ("\n") map (_.trim)).toSet
  }

  behavior of "Inline Verilog"

  it should "pass Verilog through the compiler" in {
    val inline = "wire [3:0] foo;"
    val input =
     s"""circuit Unit :
        |  module Unit :
        |    vinline("$inline")
      """.stripMargin

    val output = toVerilog(input)
    assert(output.contains(inline))
  }

  it should "insert dereferenced identifiers correctly" in {
    val inline = "cover property (@(posedge %I) %I == 1'd0);"
    val input =
     s"""circuit Unit :
        |  module Unit :
        |    input clk : Clock
        |    input start : { end : UInt<1>, collide : UInt<1> }
        |    input start_collide : UInt<1> ; Force start to be renamed
        |    vinline("$inline", clk, start.end)
      """.stripMargin
    val output = toVerilog(input)

    // get renamed start.end
    val searchRegex = """.*input\s+(start_+end).*""".r // group(1) is identifier
    val startEndName = searchRegex findFirstMatchIn output getOrElse
      fail("Name regex is incorrect, this is a bug in the test itself")

    val expect = inline.replaceFirst("%I", "clk")
                       .replaceFirst("%I", startEndName.group(1))
    assert(output.contains(expect))
  }

  it should "remove one layer of escaping when emitting Verilog (but not Firrtl)" in {
    val input =
     """circuit Unit :
       |  module Unit :
       |    input clk : Clock
       |    vinline("always @(posedge %I)", clk)
       |    vinline("  $display(\"A very \\\"special\\\" message!\\n\");")
     """.stripMargin
    val firrtlOutput = toFirrtl(input) // parse and back out
    assert(compareFirrtl(input, firrtlOutput))

    val verilogOutput = toVerilog(input)
    val expected = """$display("A very \"special\" message!\n");"""
    assert(verilogOutput split ("\n") map (_.trim) contains expected)
  }

  // This is for a hack to get inline verilog to be able to assign to Firrtl values
  it should "not connect to invalid wires or output ports" in {
    val expectedRhs = "32'hdeadbeef"
    val input =
     s"""circuit Unit :
        |  module Unit :
        |    output out : UInt<32>
        |    output foo : UInt<32>
        |    foo is invalid
        |    wire bar : UInt<32>
        |    bar is invalid
        |    out <= bar
        |    vinline("assign %I = $expectedRhs;", foo)
        |    vinline("assign %I = $expectedRhs;", bar)
      """.stripMargin
    val verilogOutput = toVerilog(input)

    // Check that we have the exact 3 assignments we expect (2 come from vinline)
    val AssignRegex = """assign (\w+) = (.+);""".r
    val fooAssigns = verilogOutput split "\n" map (_.trim) flatMap {
      case AssignRegex(lhs, rhs) => Some(lhs -> rhs)
      case _ => None
    }
    assert(fooAssigns.toMap ===
      Map("foo" -> expectedRhs, "bar" -> expectedRhs, "out" -> "bar"))
  }
}
