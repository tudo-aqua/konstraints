package tools.aqua.konstraints.smt

import org.petitparser.context.Token

// S-Expression

sealed interface SExpression

data class SubSExpression(val subExpressions: List<SExpression>) : SExpression

data class SExpressionConstant(val constant: SpecConstant) : SExpression

data class SExpressionSymbol(val symbol: Symbol) : SExpression

data class SExpressionReserved(val reserved: Token) : SExpression

data class SExpressionKeyword(val keyword: Token) : SExpression