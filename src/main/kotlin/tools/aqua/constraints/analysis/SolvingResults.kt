package tools.aqua.constraints.analysis

import tools.aqua.constraints.expressions.BoolSort
import tools.aqua.constraints.expressions.Expression
import tools.aqua.constraints.expressions.Valuation


interface SolverResult
interface ModelGeneratorResult
interface UnsatCoreProviderResult
interface WitnessProviderResult

object Sat : SolverResult

object Unsat : ModelGeneratorResult

data class DontKnow(val notes:String = "") :
        SolverResult, ModelGeneratorResult, UnsatCoreProviderResult, WitnessProviderResult

data class ModelResult(val model:Valuation) :
        ModelGeneratorResult, WitnessProviderResult

data class UnsatCoreResult(val unsatCore:Array<Expression<BoolSort>>) :
        UnsatCoreProviderResult, WitnessProviderResult

data class Interpolant(val interploant:Expression<BoolSort>)
