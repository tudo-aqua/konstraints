package tools.aqua.constraints.smtlib.parser

import com.github.h0tk3y.betterParse.combinators.*
import com.github.h0tk3y.betterParse.grammar.Grammar
import com.github.h0tk3y.betterParse.grammar.parser
import com.github.h0tk3y.betterParse.lexer.literalToken
import com.github.h0tk3y.betterParse.lexer.regexToken
import com.github.h0tk3y.betterParse.parser.Parser
import tools.aqua.constraints.expressions.*

object SMTLibParser : Grammar<Expression<*>>() {

    private val and by literalToken("and")
    private val assert by literalToken("assert")
    private val declare_const by literalToken("declare-const")
    private val or by literalToken("or")
    private val xor by literalToken("xor")
    private val implies by literalToken("=>")
    private val not by literalToken("not")
    private val _true by literalToken("true")
    private val _false by literalToken("false")

    private val fpeq by literalToken("fp.eq")
    private val fplit by literalToken("fp")

    private val _bit by literalToken("#b")
    private val _hex by literalToken("#x")

    private val bits by regexToken("[01]+")
    private val id by regexToken("\\w+")
    private val lpar by literalToken("(")
    private val rpar by literalToken(")")
    private val ws by regexToken("\\s+", ignore = true)

    private val bitstring : Parser<String> by
        (-_bit * bits map { it.text })

    private val fpExpr : Parser<FPExpression<FPSort>> by
        (-fplit * (3 times bitstring) map { (s,e,m) -> FPLiteral( FPSort(e.length, s.length + m.length), s, e, m)})

    private val fpExprInParen : Parser<FPExpression<FPSort>> by
        (-lpar * fpExpr * -rpar) map { it }

    private val boolExpr : Parser<BooleanExpression> by
        (_true  asJust True) or
        (_false asJust False) or
        (id map { BooleanVariable(it.text) }) or
        (-lpar * parser(this::complexBoolExpr) * -rpar)

    private val complexBoolExpr : Parser<BooleanExpression> by
        (-and * oneOrMore(boolExpr) map { And(it.toTypedArray()) }) or
        (-or * oneOrMore(boolExpr) map { Or(it.toTypedArray()) }) or
        (-xor * (2 times boolExpr) map { (a, b) -> Xor(a, b) }) or
        (-not * boolExpr map { Not(it) }) or
        (-fpeq * (2 times fpExprInParen) map { (a, b) -> FPEq(a, b) })

    override val rootParser by boolExpr
}
