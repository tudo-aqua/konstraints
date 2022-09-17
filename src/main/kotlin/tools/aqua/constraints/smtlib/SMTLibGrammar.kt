package tools.aqua.constraints.smtlib

import com.github.h0tk3y.betterParse.combinators.*
import com.github.h0tk3y.betterParse.grammar.Grammar
import com.github.h0tk3y.betterParse.grammar.parser
import com.github.h0tk3y.betterParse.lexer.literalToken
import com.github.h0tk3y.betterParse.lexer.regexToken
import com.github.h0tk3y.betterParse.parser.Parser
import tools.aqua.constraints.expressions.*
import tools.aqua.constraints.expressions.Function

/**
 * Portions of grammar shared by all parsers
 */
// casts that fail during parsing are due to actual type mis-matches in the parsed SMTLib code
@Suppress("UNCHECKED_CAST")
abstract class SMTLibGrammar<T> : Grammar<T>() {

    /*
     * Symbol tables
     */

    internal var vars : HashMap<String, Variable<*>> = HashMap()

    fun <T:Variable<*>> typedVariable(name:String) : T =
        vars[name] as T

    fun domainValue(name:String, domain:List<Expression<*>>) : Variable<*> =
        Application<Sort>(vars[name]!! as Function<*>, domain)

    fun declareFun(name:String, argTypes:List<Sort>, type:Sort) : FunctionDeclaration {
        vars[name]?.let {
            error("$name is already declared.")
        }
        // constants
        if (argTypes.isEmpty()) {
            vars[name] = when (type) {
                is BoolSort -> BooleanVariable(name)
                is IntSort -> NumericVariable(name, type)
                is RealSort -> NumericVariable(name, type)
                is BVSort -> BVVariable(name, type)
                is FPSort -> FPVariable(name, type)
                is NamedSort -> TypedVariable(name, type)
                else -> error("Unsupported sort: $type")
            }
        }
        else {
            vars[name] = Function(name, FunctionSort(argTypes, type))
        }
        return FunctionDeclaration(name, argTypes, type)
    }

    fun getNamedSort(name:String) : Sort = NamedSort(name)

    /*
     * Literals
     */

    // only used in theory declarations

    internal val parLit by literalToken("par")
    internal val decimalLit by literalToken("DECIMAL")
    internal val numeralLit by literalToken("NUMERAL")
    internal val stringLit by literalToken("STRING")

    // Models
    
    internal val decfineFunLit by literalToken("define-fun")

    // Commands

    internal val declareConstLit by literalToken("declare-const")
    internal val declareFunLit by literalToken("declare-fun")
    internal val assertLit by literalToken("assert")
    internal val checkSatLit by literalToken("check-sat")
    internal val setLogicLit by literalToken("set-logic")
    internal val setOptionLit by literalToken("set-option")
    internal val getModelLit by literalToken("get-model")
    internal val getValueLit by literalToken("get-value")
    internal val exitLit by literalToken("exit")
    internal val pushLit by literalToken("push")
    internal val popLit by literalToken("pop")

    // Basic syntactic constructs

    internal val lparLit by literalToken("(")
    internal val rparLit by literalToken(")")

    // Sort names

    internal val sortBoolLit by literalToken("Bool")
    internal val sortIntLit by literalToken("Int")
    internal val sortRealLit by literalToken("Real")
    internal val sortBitVecLit by literalToken("BitVec")
    internal val sortFloatingPointLit by literalToken("FloatingPoint")

    internal val sortFloat16Lit by literalToken("Float16")
    internal val sortFloat32Lit by literalToken("Float32")
    internal val sortFloat64Lit by literalToken("Float64")
    internal val sortFloat128Lit by literalToken("Float128")

    // named values and literals

    internal val trueLit by literalToken("true")
    internal val falseLit by literalToken("false")

    internal val bitLit by literalToken("#b")
    internal val hexLit by literalToken("#x")

    // operators etc.
    internal val iteLit by literalToken("ite")

    // boolean
    internal val and by literalToken("and")
    internal val or by literalToken("or")
    internal val xor by literalToken("xor")
    internal val implies by literalToken("=>")
    internal val not by literalToken("not")

    // equality
    internal val eqLit by literalToken("=")
    internal val distinctLit by literalToken("distinct")

    // numeric
    internal val addLit by literalToken("+")
    internal val subLit by literalToken("-")
    internal val mulLit by literalToken("*")
    internal val divLit by literalToken("div")

    internal val gtLit by literalToken(">")
    internal val geLit by literalToken(">=")
    internal val ltLit by literalToken("<")
    internal val leLit by literalToken("<=")

    // bv
    internal val bvAddLit by literalToken("bvadd")
    internal val bvSubLit by literalToken("bvsub")
    internal val bvMulLit by literalToken("bvmul")
    internal val bvDivLit by literalToken("bvdiv")

    // fp
    internal val fpeq by literalToken("fp.eq")
    internal val fplit by literalToken("fp")

    // Reserved words

    internal val exclLit by literalToken("!")
    internal val underscoreLit by regexToken("_\\b")
    internal val asLit by literalToken("as")
    internal val existsLit by literalToken("exists")
    internal val forallLit by literalToken("forall")
    internal val letLit by literalToken("let")

    // others tokens

    internal val numeral by regexToken("0|[1-9]\\d*")

    //internal val decimal by regexToken("(0|([1-9]\\d*))\\.0*(0|([1-9]\\d*))")

    internal val hexadecimal by regexToken("#x[0-9a-fA-F]+")

    internal val binary by regexToken("#b[01]+")

    internal val option by regexToken(":[a-zA-Z\\-]+")

    internal val symbol by regexToken("[a-zA-Z\\-_0-9!]+")
    
    // ignore white space and comments
    internal val ws by regexToken("\\s+", ignore = true)
    internal val commentLit by regexToken(";[^\\n]*", ignore = true)
    
    /*
     * Parsers
     */

    /**
     * sequence of digits as int
     */
    internal val ruleNumeral : Parser<Int> by
        (numeral map { it.text.toInt() })

    /**
     * sequence of bits
     */
    internal val ruleBitstring : Parser<String> by
        (-bitLit * binary map { it.text })

    /**
     * floating point literal
     */
    internal val fpLiteral : Parser<FPExpression<FPSort>> by
        (-fplit * (3 times ruleBitstring) map { (s,e,m) -> FPLiteral( s, e, m)})
    
    /**
     * sorts with parameters
     */
    internal val ruleSortWithParams : Parser<Sort> by
        (-sortBitVecLit * numeral map { BVSort(it.text.toInt()) }) or
        (-sortFloatingPointLit * (2 times ruleNumeral) map { (e, m) -> FPSort(e, m) })

    /**
     * sorts
     */
    internal val ruleSort : Parser<Sort> by
        (sortBoolLit asJust BoolSort) or
        (sortIntLit  asJust IntSort) or
        (sortRealLit asJust RealSort) or
        (-lparLit * -underscoreLit * ruleSortWithParams * -rparLit map { it }) or
        (symbol map { getNamedSort(it.text) }) or
        (sortFloat16Lit  asJust FPSort(5, 11)) or
        (sortFloat32Lit  asJust FPSort(8, 24)) or
        (sortFloat64Lit  asJust FPSort(11, 53)) or
        (sortFloat128Lit asJust FPSort(15, 113))

    /**
     * list of sorts (arguments of functions)
     */
    internal val ruleSortList : Parser<List<Sort>> by
        zeroOrMore(ruleSort) map { it }

    /**
     * rule for declarations
     */
    internal val ruleFunDeclaration : Parser<FunctionDeclaration> by
        (-declareConstLit * symbol * ruleSort map { (a,b) -> declareFun(a.text, emptyList(), b) }) or
        (-declareFunLit   * symbol * -lparLit * ruleSortList * -rparLit * ruleSort map { (a, b, c) -> declareFun(a.text, b, c) })


    /**
     * Boolean terms
     */
    internal val booleanTerm : Parser<BooleanExpression> by
        (-and * oneOrMore(parser(this::term)) map {
            And(it as List<BooleanExpression>) }) or
        (-or * oneOrMore(parser(this::term)) map {
            Or(it as List<BooleanExpression>) }) or
        (-xor * (2 times parser(this::term)) map {
            (a, b) -> Xor(a as BooleanExpression, b as BooleanExpression) }) or
        (-not * parser(this::term) map {
            Not(it as BooleanExpression) })

    /**
     * Equality and distinct
     */
    internal val equalityTerm : Parser<BooleanExpression> by
        (-eqLit * (2 times parser(this::term)) map {
            (a, b) -> Eq(a as Expression<Sort>, b as Expression<Sort>) }) or
        (-distinctLit * oneOrMore(parser(this::term)) map {
            Distinct(it as List<Expression<Sort>>) })

    /**
     * Minus or unary minus
     */
    internal val ruleSubOrNeg : Parser<NumericExpression<NumericSort>> by
        ((2 times parser(this::term)) map {
            Sub(it[0] as NumericExpression<NumericSort>, it[1] as NumericExpression<NumericSort>)}) or
        (parser(this::term) map {
            Neg(it as NumericExpression<NumericSort>) })

    /**
     * Numeric terms
     */
    internal val numericTerm : Parser<NumericExpression<NumericSort>> by
        (-addLit * oneOrMore(parser(this::term)) map {
            Add( it as List<NumericExpression<NumericSort>>) }) or
        (-subLit * ruleSubOrNeg map { it }) or
        (-mulLit * oneOrMore(parser(this::term)) map {
            Mul( it as List<NumericExpression<NumericSort>>) })

    /**
     * Boolean numeric terms
     */
    internal val numericBooleanTerm : Parser<NumericBooleanExpression<NumericSort>> by
        (-geLit * (2 times parser(this::term)) map {
            (a, b) -> GEq<NumericSort>(a as NumericExpression<NumericSort>, b as NumericExpression<NumericSort>) })

    /**
     * Bit vector terms
     */
    internal val bitVectorTerm : Parser<BVExpression<BVSort>> by
        (-bvAddLit * (2 times parser(this::term)) map {
                (a,b) -> BVAdd( a as BVExpression<BVSort>, b as BVExpression<BVSort>) })  or
        (-bvSubLit * (2 times parser(this::term)) map {
                (a,b) -> BVSub( a as BVExpression<BVSort>, b as BVExpression<BVSort>) })

    /**
     * Terms
     */
    internal val term : Parser<Expression<*>> by
        (-lparLit * (
            (booleanTerm map { it }) or
            (equalityTerm map { it }) or
            (numericTerm map { it }) or
            (bitVectorTerm map { it }) or
            (numericBooleanTerm map { it }) or
            (-iteLit * (3 times parser(this::term)) map {
                    (a,b,c) -> Ite(a as BooleanExpression, b as Expression<Sort>, c as Expression<Sort>)} ) or
            (symbol * oneOrMore(parser(this::term)) map {
                    (a,b) ->  domainValue(a.text, b) })
        ) * -rparLit map { it }) or
        (ruleNumeral map { IntLiteral(it) }) or
        (trueLit  asJust True) or
        (falseLit asJust False) or
        (symbol map { typedVariable(it.text) })


}
