package benchmark

import kotlinx.benchmark.BenchmarkTimeUnit
import kotlinx.benchmark.Mode
import kotlinx.benchmark.Scope
import org.openjdk.jmh.annotations.Benchmark
import org.openjdk.jmh.annotations.BenchmarkMode
import org.openjdk.jmh.annotations.Measurement
import org.openjdk.jmh.annotations.OutputTimeUnit
import org.openjdk.jmh.annotations.Setup
import org.openjdk.jmh.annotations.State
import org.openjdk.jmh.annotations.Warmup
import tools.aqua.konstraints.parser.Parser
import java.io.BufferedReader
import java.io.File
import java.util.concurrent.TimeUnit

@State(Scope.Benchmark)
@BenchmarkMode(Mode.All)
@OutputTimeUnit(BenchmarkTimeUnit.MILLISECONDS)
@Warmup(iterations = 0, time = 500, timeUnit = BenchmarkTimeUnit.MILLISECONDS)
@Measurement(iterations = 1575, time = 1, timeUnit = TimeUnit.MILLISECONDS)
class ParseIndividual {
  val programs =
      File(javaClass.getResource("/smt-benchmark/QF_BV/20190311-bv-term-small-rw-Noetzli/")!!.file)
          .walk()
          .filter { file: File -> file.isFile }
          .map { file: File ->
            file.bufferedReader().use(BufferedReader::readLines).joinToString("\n")
          }
          .asSequence()

  var counter = 0
  var program = ""

  @Setup
  fun setProgram() {
    program = programs.elementAtOrElse(counter) { "" }
    counter++
  }

  @Benchmark
  fun QF_BV() {
    Parser().parse(program)
  }
}