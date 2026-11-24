package tools.aqua.konstraints.solvers

import tools.aqua.konstraints.smt.Model
import tools.aqua.konstraints.smt.SatStatus

data class SolverResult(val status: SatStatus, val model: Model?)