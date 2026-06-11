package tools.aqua.konstraints.util

import tools.aqua.konstraints.parser.SMTScriptParser
import tools.aqua.konstraints.smt.SatStatus
import tools.aqua.konstraints.solvers.InteractiveZ3Solver
import tools.aqua.konstraints.solvers.Solver
import java.io.File
import kotlin.time.Duration
import kotlin.time.measureTime

enum class Format {
    JSON, CSV
}

data class BenchmarkResult(val data: List<BenchmarkEntry>) {
    fun write(path: String, format: Format, prefix: String = "", suffix: String = "") =
        write(File(path), format, prefix, suffix)

    fun write(file: File, format: Format, prefix: String = "", suffix: String = "") = when(format) {
        Format.JSON -> write(file, ::formatJSON, "{", "}")
        Format.CSV -> write(file, ::formatCSV, "File, Result, Duration, Message\n", "")
    }

    fun write(file: File, format: (BenchmarkEntry) -> String, prefix: String = "", suffix: String = "") {
        val writer = file.bufferedWriter()

        writer.write(prefix)
        data.forEach { entry -> writer.write(format(entry)) }
        writer.write(suffix)
        writer.flush()
    }

    private fun formatJSON(entry: BenchmarkEntry) = "\"${entry.path}\": { \"status\": \"${entry.result}\", \"duration\": ${entry.duration.inWholeNanoseconds}, \"msg\": ${entry.msg} },"

    private fun formatCSV(entry: BenchmarkEntry) = "\"${entry.path}\", \"${entry.result}\", ${entry.duration.inWholeNanoseconds}, ${entry.msg}\n"
}

data class BenchmarkEntry(val path: String, val result: SatStatus, val duration: Duration, val msg: String)

class BenchmarkRunner(val verbose: Boolean = false) {
    private val results = mutableListOf<BenchmarkEntry>()

    fun start(baseDirectory: String, solver: () -> Solver, timeout: Long) =
        start(File(baseDirectory), solver, timeout)

    fun start(baseDirectory: File, solver: () -> Solver, timeout: Long) =
        baseDirectory.
        walk().
        filter { it.isFile }.
        forEach { file ->
            try {
                results.add(benchmark(file, solver, timeout))
            } catch (e: Exception) {
                results.add(BenchmarkEntry(file.path, SatStatus.ERROR, Duration.ZERO, e.message ?: ""))
            }
        }.let { BenchmarkResult(results) }

    private fun benchmark(file: File, solver: () -> Solver, timeout: Long): BenchmarkEntry {
        if(verbose) {
            println("Benchmarking ${file.path}")
        }

        val program = SMTScriptParser(file.reader())
        var result = SatStatus.PENDING
        val duration = measureTime {
            result = solver().use { solver -> solver.solve(program, false, timeout) }.first
        }

        if(verbose) {
            println("Got $result after $duration")
        }

        return BenchmarkEntry(file.path, result, duration, "")
    }
}

fun main(args: Array<String>) {
    val runner = BenchmarkRunner(true)
    val results = runner.start("E:\\Projects\\aqua\\smt-benchmark\\QF_BV\\20190311-bv-term-small-rw-Noetzli", {InteractiveZ3Solver()}, 1000)

    results.write("test.csv", Format.CSV)
}