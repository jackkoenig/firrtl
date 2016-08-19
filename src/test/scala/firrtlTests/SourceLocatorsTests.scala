
package firrtlTests

import org.scalatest.FlatSpec
import collection.mutable

import firrtl.{Parser, Compiler, VerilogCompiler, HighFirrtlCompiler}
import firrtl.Parser.GenInfo
import firrtl.ir._
import firrtl.Mappers._
import firrtl.Annotations.AnnotationMap

class SourceLocatorsSpec extends FlatSpec {

  behavior of "Source Locators"

  it should "be propagated to Verilog" in {
    val input =
      """
      |circuit SourceLocators :
      |  module SourceLocators :
      |    input in : UInt<4>
      |    output out : UInt<4>
      |
      |    out <= in
      |    when eq(in, UInt<4>(7)) :
      |      out <= tail(add(in, UInt<4>(1)), 1)
      |    when lt(in, UInt<4>(5)) :
      |    else :
      |      out <= UInt<4>(3)
      """.stripMargin
    // Get all source locators from parsed code
    def gatherInfo(module: Module): Set[String] = {
      val allInfo: mutable.Set[Info] = mutable.Set.empty
      def onStmt(stmt: Statement): Statement =
        (stmt map onStmt) match {
          case has: HasInfo =>
            allInfo += has.info
            has
          case s => s
        }
      allInfo += module.info
      allInfo ++= (module.ports map (_.info)).toSet
      onStmt(module.body)
      // Extract strings from the info
      (allInfo map { case FileInfo(lit) => lit.serialize }).toSet
    }
    // Extracts info from @[...] string
    val InfoRegex = """.*@\[(.*)\].*""".r
    def extractInfo(str: String): Set[String] = str match {
      case InfoRegex(infos) => (infos split (",") map (_.trim)).toSet
      case _ => Set.empty
    }

    val circuit = Parser.parse((input split ("\n")).toIterator,
                               GenInfo("SourceLocators.fir"))
    val initInfo = gatherInfo(circuit.modules.head.asInstanceOf[Module])

    val writer = new java.io.StringWriter
    val compiler = new VerilogCompiler
    compiler.compile(circuit, AnnotationMap(Seq.empty), writer)

    val finalInfo = (writer.toString split ("\n")).toSet flatMap extractInfo
    for (info <- initInfo) {
      assert(finalInfo contains info)
    }
  }
}
