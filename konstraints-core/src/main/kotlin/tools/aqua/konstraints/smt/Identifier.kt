package tools.aqua.konstraints.smt

import tools.aqua.konstraints.parser.ParseSymbol

sealed interface Identifier {
  val symbol: Symbol
}

data class SymbolIdentifier(override val symbol: ParseSymbol) : Identifier
data class IndexedIdentifier(override val symbol: ParseSymbol, val indices: List<Index>) :
    Identifier