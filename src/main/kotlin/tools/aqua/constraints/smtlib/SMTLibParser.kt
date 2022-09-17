package tools.aqua.constraints.smtlib

import com.github.h0tk3y.betterParse.combinators.*
import com.github.h0tk3y.betterParse.parser.Parser
import tools.aqua.constraints.expressions.BooleanExpression
import tools.aqua.constraints.expressions.Variable

/**
 * Parser for SMTLib scripts
 */
// casts that fail during parsing are due to actual type mis-matches in the parsed SMTLib code
@Suppress("UNCHECKED_CAST")
class SMTLibParser : SMTLibGrammar<SMTLibScript>() {

    private val symbolOrDomainValue : Parser<Variable<*>> by
        (-lparLit * symbol * oneOrMore(term) * -rparLit map { (a,b) -> domainValue(a.text, b)}) or
        (symbol map { typedVariable(it.text) })

    /**
     * rule for SMTLib statements
     */
    private val command : Parser<SMTLibStatement> by
        (ruleFunDeclaration map { it }) or
        (-assertLit * term map { Assert(it as BooleanExpression) }) or
        (checkSatLit asJust CheckSat) or
        (exitLit asJust Exit) or
        (-setLogicLit * symbol map { SetLogic(Logic.valueOf(it.text))}) or
        (-setOptionLit * option * (symbol or trueLit or falseLit map { it }) map { (a,b) -> SetOption(a.text, b.text)}) or
        (getModelLit asJust GetModel) or
        (-getValueLit * -lparLit * oneOrMore(symbolOrDomainValue) * -rparLit map {
            GetValue( it ) }) or
        (-pushLit * ruleNumeral map { Push(it) }) or
        (-popLit * ruleNumeral map { Pop(it) })
        // TODO: add remaining commands


    /**
     * rule for SMTLib scripts
     */
    private val script : Parser<SMTLibScript> by
        zeroOrMore(-lparLit * command * -rparLit) map { SMTLibScript(it) }

    override val rootParser by script
}
