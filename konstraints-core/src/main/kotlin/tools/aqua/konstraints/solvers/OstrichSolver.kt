package tools.aqua.konstraints.solvers

import tools.aqua.konstraints.parser.ResponseParser
import tools.aqua.konstraints.smt.Model
import tools.aqua.konstraints.smt.SMTProgram
import tools.aqua.konstraints.smt.SatStatus
import java.io.BufferedReader
import java.io.InputStreamReader

class OstrichSolver(location : String, file : String): Solver {
    val processBuilder = ProcessBuilder("java", "-jar", location, file, "+quiet")
        .redirectErrorStream(true)

    override fun solve(program: SMTProgram): SatStatus {
        val process = processBuilder.start()
        val reader = BufferedReader(InputStreamReader(process.inputStream, Charsets.UTF_8))
        process.waitFor()
        ResponseParser.parse(reader, program)
        process.destroy()

        return program.status
    }

    override fun getModel(): Model {
        TODO("Not yet implemented")
    }

    override fun close() {

    }
}