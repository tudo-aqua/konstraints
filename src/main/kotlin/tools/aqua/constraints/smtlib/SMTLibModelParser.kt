package tools.aqua.constraints.smtlib

import com.github.h0tk3y.betterParse.combinators.*
import com.github.h0tk3y.betterParse.parser.Parser
import tools.aqua.constraints.expressions.*
import tools.aqua.constraints.solver.FunctionDefinition
import tools.aqua.constraints.solver.Model

/**
 * Parser for SMTLib models
 */
// casts that fail during parsing are due to actual type mis-matches in the parsed SMTLib code
@Suppress("UNCHECKED_CAST")
class SMTLibModelParser : SMTLibGrammar<Model>() {

    /**
     * Parameter: name + type
     */
    private val paramDefinition : Parser<Variable<Sort>> by
        (-lparLit * symbol * ruleSort * -rparLit map { (a, b) ->
            declareFun(a.text, emptyList(), b)
            typedVariable(a.text)
        })

    /**
     * rule for definitions
     */
    private val functionDefinition : Parser<FunctionDefinition> by
        (-decfineFunLit  * symbol * -lparLit * zeroOrMore(paramDefinition) * -rparLit * ruleSort * term map { (a, b, c, d) ->
            // TODO: need proper scoping?
            // remove local variables
            b.forEach { vars.remove(it.symbol) }
            FunctionDefinition(a.text, b, c, d) })

    /**
     * rule for SMTLib models
     */
    private val model : Parser<Model> by
        (zeroOrMore(-lparLit * functionDefinition * -rparLit) map {
            val elements = HashMap<String,FunctionDefinition>()
            it.forEach { elements[it.name] = it }
            Model( elements )
        })
        // TODO: add missing cases (recursive functions)

    override val rootParser by model
}