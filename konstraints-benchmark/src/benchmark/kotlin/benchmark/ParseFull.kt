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
@BenchmarkMode(Mode.AverageTime)
@OutputTimeUnit(BenchmarkTimeUnit.MILLISECONDS)
@Warmup(iterations = 0, time = 500, timeUnit = BenchmarkTimeUnit.MILLISECONDS)
@Measurement(iterations = 1, time = -1, timeUnit = TimeUnit.MINUTES)
class ParseFull {
    val programs =
        File(javaClass.getResource("/smt-benchmark/QF_BV/20190311-bv-term-small-rw-Noetzli/")!!.file)
            .walk()
            .filter { file: File -> file.isFile }
            .mapIndexed { i, file: File ->
                "(set-info :bench |$i|)" +
                file.bufferedReader().use(BufferedReader::readLines).joinToString("\n")
            }

    @Benchmark
    fun QF_BV() {
        programs.forEach { program ->
            val prog = Parser().parse(program)
            println(prog.info.find { attribute -> attribute.keyword.contains("bench") }?.value)
        }
    }
}