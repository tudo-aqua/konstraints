/*
 * SPDX-License-Identifier: Apache-2.0
 *
 * Copyright 2023-2025 The Konstraints Authors
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package tools.aqua.konstraints.parser

import java.math.BigDecimal
import kotlin.contracts.ExperimentalContracts
import kotlin.contracts.contract
import tools.aqua.konstraints.lexer.AsWord
import tools.aqua.konstraints.lexer.AssertWord
import tools.aqua.konstraints.lexer.Binary
import tools.aqua.konstraints.lexer.CheckSatAssumingWord
import tools.aqua.konstraints.lexer.CheckSatWord
import tools.aqua.konstraints.lexer.ClosingBracket
import tools.aqua.konstraints.lexer.CommandName
import tools.aqua.konstraints.lexer.Decimal
import tools.aqua.konstraints.lexer.DeclareConstWord
import tools.aqua.konstraints.lexer.DeclareDatatypeWord
import tools.aqua.konstraints.lexer.DeclareDatatypesWord
import tools.aqua.konstraints.lexer.DeclareFunWord
import tools.aqua.konstraints.lexer.DeclareSortParameterWord
import tools.aqua.konstraints.lexer.DeclareSortWord
import tools.aqua.konstraints.lexer.DefineConstWord
import tools.aqua.konstraints.lexer.DefineFunRecWord
import tools.aqua.konstraints.lexer.DefineFunWord
import tools.aqua.konstraints.lexer.DefineSortWord
import tools.aqua.konstraints.lexer.EchoWord
import tools.aqua.konstraints.lexer.ExclamationWord
import tools.aqua.konstraints.lexer.ExistsWord
import tools.aqua.konstraints.lexer.ExitWord
import tools.aqua.konstraints.lexer.ForallWord
import tools.aqua.konstraints.lexer.GetAssertionsWord
import tools.aqua.konstraints.lexer.GetAssignmentWord
import tools.aqua.konstraints.lexer.GetInfoWord
import tools.aqua.konstraints.lexer.GetModelWord
import tools.aqua.konstraints.lexer.GetOptionWord
import tools.aqua.konstraints.lexer.GetProofWord
import tools.aqua.konstraints.lexer.GetUnsatAssumptionsWord
import tools.aqua.konstraints.lexer.GetUnsatCoreWord
import tools.aqua.konstraints.lexer.GetValueWord
import tools.aqua.konstraints.lexer.Hexadecimal
import tools.aqua.konstraints.lexer.KeywordToken
import tools.aqua.konstraints.lexer.LambdaWord
import tools.aqua.konstraints.lexer.LetWord
import tools.aqua.konstraints.lexer.MatchWord
import tools.aqua.konstraints.lexer.Numeral
import tools.aqua.konstraints.lexer.OpeningBracket
import tools.aqua.konstraints.lexer.PopWord
import tools.aqua.konstraints.lexer.PushWord
import tools.aqua.konstraints.lexer.QuotedSymbolToken
import tools.aqua.konstraints.lexer.ResetAssertionsWord
import tools.aqua.konstraints.lexer.ResetWord
import tools.aqua.konstraints.lexer.SMTString
import tools.aqua.konstraints.lexer.SetInfoWord
import tools.aqua.konstraints.lexer.SetLogicWord
import tools.aqua.konstraints.lexer.SetOptionWord
import tools.aqua.konstraints.lexer.SimpleSymbolToken
import tools.aqua.konstraints.lexer.SpecConstantToken
import tools.aqua.konstraints.lexer.SymbolToken
import tools.aqua.konstraints.lexer.Token
import tools.aqua.konstraints.lexer.UnderscoreWord
import tools.aqua.konstraints.parser.lexer.SMTTokenizer
import tools.aqua.konstraints.smt.AnnotatedExpression
import tools.aqua.konstraints.smt.Attribute
import tools.aqua.konstraints.smt.AttributeValue
import tools.aqua.konstraints.smt.BVLiteral
import tools.aqua.konstraints.smt.BinaryConstant
import tools.aqua.konstraints.smt.CheckSat
import tools.aqua.konstraints.smt.ConstantAttributeValue
import tools.aqua.konstraints.smt.DecimalConstant
import tools.aqua.konstraints.smt.ExistsExpression
import tools.aqua.konstraints.smt.Exit
import tools.aqua.konstraints.smt.Expression
import tools.aqua.konstraints.smt.ForallExpression
import tools.aqua.konstraints.smt.FunctionDef
import tools.aqua.konstraints.smt.HexConstant
import tools.aqua.konstraints.smt.Identifier
import tools.aqua.konstraints.smt.Index
import tools.aqua.konstraints.smt.IndexedIdentifier
import tools.aqua.konstraints.smt.IntLiteral
import tools.aqua.konstraints.smt.LetExpression
import tools.aqua.konstraints.smt.Logic
import tools.aqua.konstraints.smt.MutableSMTProgram
import tools.aqua.konstraints.smt.NumeralConstant
import tools.aqua.konstraints.smt.NumeralIndex
import tools.aqua.konstraints.smt.RealLiteral
import tools.aqua.konstraints.smt.Sort
import tools.aqua.konstraints.smt.SortedVar
import tools.aqua.konstraints.smt.StringConstant
import tools.aqua.konstraints.smt.StringLiteral
import tools.aqua.konstraints.smt.Symbol
import tools.aqua.konstraints.smt.SymbolAttributeValue
import tools.aqua.konstraints.smt.SymbolIdentifier
import tools.aqua.konstraints.smt.SymbolIndex
import tools.aqua.konstraints.smt.Theories
import tools.aqua.konstraints.smt.VarBinding
import tools.aqua.konstraints.smt.assert
import tools.aqua.konstraints.smt.cast
import tools.aqua.konstraints.smt.declareFun
import tools.aqua.konstraints.smt.defineFun
import tools.aqua.konstraints.smt.setInfo
import tools.aqua.konstraints.smt.toSymbolWithQuotes
import tools.aqua.konstraints.util.PeekableIterator
import tools.aqua.konstraints.util.peekIs
import tools.aqua.konstraints.util.peekIsNot
import tools.aqua.konstraints.util.peekable

class Parser private constructor(val lexer: PeekableIterator<Token>) {
  companion object {
    operator fun invoke(input: String) =
        Parser(SMTTokenizer(input.reader()).peekable()).parseScript()
  }

  private fun parseScript(): MutableSMTProgram {
    val program = MutableSMTProgram()

    while (lexer.hasNext()) {
      parseCommand(program)
    }

    return program
  }

  @OptIn(ExperimentalContracts::class)
  private fun parseCommand(program: MutableSMTProgram) {
    requireIsInstance<OpeningBracket>(lexer.next())

    val commandName = lexer.next()
    requireIsInstance<CommandName>(commandName)

    when (commandName) {
      is AssertWord -> parseAssert(program)
      is CheckSatAssumingWord -> TODO()
      is CheckSatWord -> program.add(CheckSat)
      is DeclareConstWord -> parseDeclareConst(program)
      is DeclareDatatypeWord -> TODO()
      is DeclareDatatypesWord -> TODO()
      is DeclareFunWord -> parseDeclareFun(program)
      is DeclareSortParameterWord -> TODO()
      is DeclareSortWord -> TODO()
      is DefineConstWord -> parseDefineConst(program)
      is DefineFunRecWord -> TODO()
      is DefineFunWord -> parseDefineFun(program)
      is DefineSortWord -> TODO()
      is EchoWord -> TODO()
      is ExitWord -> program.add(Exit)
      is GetAssertionsWord -> TODO()
      is GetAssignmentWord -> TODO()
      is GetInfoWord -> TODO()
      is GetModelWord -> TODO()
      is GetOptionWord -> TODO()
      is GetProofWord -> TODO()
      is GetUnsatAssumptionsWord -> TODO()
      is GetUnsatCoreWord -> TODO()
      is GetValueWord -> TODO()
      is PopWord -> parsePop(program)
      is PushWord -> parsePush(program)
      is ResetAssertionsWord -> TODO()
      is ResetWord -> TODO()
      is SetInfoWord -> parseSetInfo(program)
      is SetLogicWord -> parseSetLogic(program)
      is SetOptionWord -> TODO()
    }

    requireIsInstance<ClosingBracket>(lexer.next())
  }

  private fun parseAssert(program: MutableSMTProgram) {
    program.assert(parseTerm(program).cast())
  }

  private fun parseDeclareConst(program: MutableSMTProgram) {
    val symbol = parseSymbol()
    val sort = parseSort(program)

    program.declareConst(symbol, sort)
  }

  @OptIn(ExperimentalContracts::class)
  private fun parseDeclareFun(program: MutableSMTProgram) {
    val symbol = parseSymbol()

    requireIsInstance<OpeningBracket>(lexer.next())
    val sorts = star<ClosingBracket, Sort>(program, ::parseSort)
    requireIsInstance<ClosingBracket>(lexer.next())

    val sort = parseSort(program)

    program.declareFun(symbol, sorts, sort)
  }

  private fun parseDefineConst(program: MutableSMTProgram) {
    val symbol = parseSymbol()
    val sort = parseSort(program)
    val term = parseTerm(program)

    program.defineConst(symbol, sort, term)
  }

  @OptIn(ExperimentalContracts::class)
  private fun parseDefineFun(program: MutableSMTProgram) {
    val symbol = parseSymbol()

    requireIsInstance<OpeningBracket>(lexer.next())
    val sortedVars = star<ClosingBracket, SortedVar<*>>(program, ::parseSortedVar)
    requireIsInstance<ClosingBracket>(lexer.next())

    val sort = parseSort(program)

    // bind the local variables for this function that can be used locally
    // TODO implement a more let like syntax bind/unbind do not need to be split anymore
    program.context.bindVariables(sortedVars)
    val term = parseTerm(program)
    program.context.unbindVariables()

    program.defineFun(FunctionDef(symbol, sortedVars, sort, term))
  }

  private fun parseSetLogic(program: MutableSMTProgram) {
    val symbol = parseSymbol()
    program.setLogic(
        Logic.logics[symbol.toString()] ?: throw IllegalArgumentException("Unknown logic $symbol!")
    )
  }

  private fun parseSetInfo(program: MutableSMTProgram) {
    val attribute = parseAttribute()

    program.setInfo(attribute)
  }

  @OptIn(ExperimentalContracts::class)
  private fun parsePush(program: MutableSMTProgram) {
    val numeral = lexer.next()
    requireIsInstance<Numeral>(numeral)

    program.push(numeral.number.toInt())
  }

  @OptIn(ExperimentalContracts::class)
  private fun parsePop(program: MutableSMTProgram) {
    val numeral = lexer.next()
    requireIsInstance<Numeral>(numeral)

    program.pop(numeral.number.toInt())
  }

  @OptIn(ExperimentalContracts::class)
  private fun parseAttribute(): Attribute {
    val keyword = lexer.next()
    requireIsInstance<KeywordToken>(keyword)

    val value =
        if (lexer.peekIsNot { token -> token is ClosingBracket }) {
          // attribute has an attached value
          parseAttributeValue()
        } else null

    return Attribute(keyword.toString(), value)
  }

  private fun parseAttributeValue(): AttributeValue =
      when (val token = lexer.next()) {
        is SpecConstantToken -> ConstantAttributeValue(parseSpecConstant(token))
        is SymbolToken -> SymbolAttributeValue(parseSymbol(token))
        is OpeningBracket -> TODO("SExpr attribute value not implemented yet")
        else ->
            throw UnexpectedTokenException(
                token,
                "any of SpecConstantToken, SymbolToken or OpeningBracket",
            )
      }

  // all these function will not discard the stop token so the user does not unexpectedly lose a
  // token
  /**
   * Implements star operator, parsing objects using [parser] until a token of type [T] is reach,
   * the final token will NOT be discarded.
   */
  @OptIn(ExperimentalContracts::class)
  private inline fun <reified T : Token, S> star(
      program: MutableSMTProgram,
      parser: (MutableSMTProgram) -> S,
  ): List<S> {
    val results = mutableListOf<S>()
    while (lexer.peekIsNot { token -> token is T }) {
      results.add(parser(program))
    }

    return results
  }

  /**
   * Implements star operator, parsing objects using [parser] until a token of type [T] is reach,
   * the final token will NOT be discarded.
   */
  @OptIn(ExperimentalContracts::class)
  private inline fun <reified T : Token, S> star(parser: () -> S): List<S> {
    val results = mutableListOf<S>()
    while (lexer.peekIsNot { token -> token is T }) {
      results.add(parser())
    }

    return results
  }

  /**
   * Implements plus (this is match at least once) operator, parsing objects using [parser] until a
   * token of type [T] is reach, the final token will NOT be discarded.
   */
  @OptIn(ExperimentalContracts::class)
  private inline fun <reified T : Token, S> plus(
      program: MutableSMTProgram,
      parser: (MutableSMTProgram) -> S,
  ): List<S> {
    val results = mutableListOf<S>()
    do {
      results.add(parser(program))
    } while (lexer.peekIsNot { token -> token is T })

    return results
  }

  /**
   * Implements plus (this is match at least once) operator, parsing objects using [parser] until a
   * token of type [T] is reach, the final token will NOT be discarded.
   */
  @OptIn(ExperimentalContracts::class)
  private inline fun <reified T : Token, S> plus(parser: () -> S): List<S> {
    val results = mutableListOf<S>()
    do {
      results.add(parser())
    } while (lexer.peekIsNot { token -> token is T })

    return results
  }

  @OptIn(ExperimentalContracts::class)
  private fun parseSymbol(): Symbol {
    val symbol = lexer.next()
    requireIsInstance<SymbolToken>(symbol)

    return parseSymbol(symbol)
  }

  private fun parseSymbol(token: SymbolToken) =
      when (token) {
        // for quoted symbol we can not immediately know if they are simple or not (that is valid
        // without quotes)
        // so the Symbol constructor has to check again to set the isSimple flag correct
        is QuotedSymbolToken -> Symbol(token.toString(), true)
        is SimpleSymbolToken -> Symbol(token.toString(), false, true)
      }

  @OptIn(ExperimentalContracts::class)
  private fun parseSort(program: MutableSMTProgram): Sort =
      if (lexer.peekIs { token -> token is OpeningBracket }) {
        // parse a sort with arity > 0
        // discard opening bracket
        requireIsInstance<OpeningBracket>(lexer.next())

        val identifier = parseIdentifier()

        // this is parsed as ( <Identifier> <Sort>+ )
        val sorts = plus<ClosingBracket, Sort>(program, ::parseSort)
        requireIsInstance<ClosingBracket>(lexer.next())

        when (identifier) {
          is IndexedIdentifier -> {
            program.context
                .getSort(identifier.symbol)
                .build(sorts, identifier.indices as List<NumeralIndex>)
          }

          is SymbolIdentifier -> {
            program.context.getSort(identifier.symbol).build(sorts, emptyList())
          }
        }
      } else {
        // parse a sort with arity 0
        when (val identifier = parseIdentifier()) {
          is IndexedIdentifier -> {
            program.context
                .getSort(identifier.symbol)
                .build(emptyList(), identifier.indices as List<NumeralIndex>)
          }

          is SymbolIdentifier -> {
            program.context.getSort(identifier.symbol).build(emptyList(), emptyList())
          }
        }
      }

  @OptIn(ExperimentalContracts::class)
  private fun parseIdentifier(): Identifier {
    if (lexer.peekIs { token -> token is OpeningBracket }) {
      // parse indexed identifier

      // check indexed identifiers start with an underscore and discard
      requireIsInstance<UnderscoreWord>(lexer.next())

      val symbol = parseSymbol()
      val indices = plus<ClosingBracket, Index>(::parseIndex)

      requireIsInstance<ClosingBracket>(lexer.next())

      return IndexedIdentifier(symbol, indices)
    } else {
      // parse simple identifier

      return SymbolIdentifier(parseSymbol())
    }
  }

  @OptIn(ExperimentalContracts::class)
  private fun parseIndex(): Index {
    if (lexer.peekIs { token -> token is SymbolToken }) {
      return SymbolIndex(parseSymbol())
    } else {
      // parse numeral index
      val numeral = lexer.next()
      requireIsInstance<Numeral>(numeral)

      return NumeralIndex(numeral.number.toInt())
    }
  }

  /*
  * term in smt is defined as follows
  * term ::= <spec_constant>
     | <qual_identifier>
     | ( <qual_identifier> <term>+ )
     | ( let ( <var_binding>+ ) <term> )
     | ( lambda ( <sorted_var>+ ) <term> )
     | ( forall ( <sorted_var>+ ) <term> )
     | ( exists ( <sorted_var>+ ) <term> )
     | ( match <term> ( <match_case>+ ) )
     | ( ! <term> <attribute>+ )
  * to parse without back tracking we 'unroll' some of the definitions which leads to
  * term ::= <spec_constant>
     | <symbol>
     | ( _ <symbol> <index>+ )
     | ( as <identifier> <sort> )
     | ( let ( <var_binding>+ ) <term> )
     | ( lambda ( <sorted_var>+ ) <term> )
     | ( forall ( <sorted_var>+ ) <term> )
     | ( exists ( <sorted_var>+ ) <term> )
     | ( match <term> ( <match_case>+ ) )
     | ( ! <term> <attribute>+ )
     | ( <symbol> <term>+ )
     | ( ( _ <symbol> <index>+ ) <term>+ )
     | ( ( as <identifier> <sort> ) <term>+ )
  * by peeking at the next two tokens max we can guarantee a correct parse given a correct smt program
  */
  @OptIn(ExperimentalContracts::class)
  private fun parseTerm(program: MutableSMTProgram): Expression<*> {
    when (val token = lexer.next()) {
      is SpecConstantToken -> {
        // here we get a literal
        return parseSpecConstantTerm(program, token)
      }
      is SymbolToken -> {
        // smt function invocation with arity 0
        return when (token) {
          is QuotedSymbolToken ->
              program.context
                  .getFunc(token.toString().toSymbolWithQuotes())
                  .constructDynamic(emptyList(), emptyList())
          is SimpleSymbolToken ->
              program.context
                  .getFunc(token.toString().toSymbolWithQuotes())
                  .constructDynamic(emptyList(), emptyList())
        }
      }
      is OpeningBracket -> {
        val expr =
            when (lexer.peek()) {
              is AsWord -> TODO("As not implemented in konstraints yet")
              is LetWord -> parseLet(program)
              is LambdaWord -> TODO("Lambda not implemented in konstraints yet")
              is ForallWord -> parseForall(program)
              is ExistsWord -> parseExists(program)
              is MatchWord -> TODO("Match not implemented in konstraints yet")
              is ExclamationWord -> parseAnnotatedTerm(program)
              is SymbolToken -> {
                // smt function with arity > 0 but not indexed (so e.g. not ((_ extract i j)
                // bv_term))
                val func = program.context.getFunc(parseSymbol())
                val terms = plus<ClosingBracket, Expression<*>>(program, ::parseTerm)

                func.constructDynamic(terms, emptyList())
              }
              is OpeningBracket -> {
                // discard opening bracket
                lexer.next()
                when (lexer.peek()) {
                  is AsWord -> TODO("As not implemented in konstraints yet")
                  is UnderscoreWord -> {
                    val identifier = parseIdentifier()

                    // sanity check identifier may be removed later
                    require(identifier is IndexedIdentifier) {
                      "Expected IndexedIdentifier but found ${identifier.javaClass}"
                    }

                    val indices = identifier.indices
                    require(indices.all { index -> index is NumeralIndex }) {
                      "Expected all indices to be numeral but found at least one symbolic"
                    }

                    val terms = plus<ClosingBracket, Expression<*>>(program, ::parseTerm)

                    // consume closing bracket
                    requireIsInstance<ClosingBracket>(lexer.next())

                    program.context.getFunc(identifier.symbol).constructDynamic(terms, indices)
                  }
                  else -> throw UnexpectedTokenException(token, "any of AsWord or UnderscoreWord")
                }
              }
              else ->
                  throw UnexpectedTokenException(
                      token,
                      "any of AsWord, LetWord, LambdaWord, ForallWord, ExistsWord, MatchWord, ExclamationWord, SymbolToken or OpeningBracket",
                  )
            }

        // read and discard the closing bracket
        requireIsInstance<ClosingBracket>(lexer.next())

        return expr
      }
      else ->
          throw UnexpectedTokenException(
              token,
              "any of SpecConstantToken, SymbolToken or OpeningBracket",
          )
    }
  }

  @OptIn(ExperimentalContracts::class)
  private fun parseLet(program: MutableSMTProgram): LetExpression<Sort> {
    // consume let token
    lexer.next()

    // check and consume opening bracket
    requireIsInstance<OpeningBracket>(lexer.next())

    val bindings = plus<ClosingBracket, VarBinding<*>>(program, ::parseVarBinding)

    requireIsInstance<ClosingBracket>(lexer.next())

    // bind the bindings locally note that the context automatically discards the bindings once the
    // lambda exits
    val term = program.context.let(bindings) { parseTerm(program) }

    return LetExpression(bindings, term)
  }

  @OptIn(ExperimentalContracts::class)
  private fun parseForall(program: MutableSMTProgram): ForallExpression {
    // consume forall token
    lexer.next()

    // check and consume opening bracket
    requireIsInstance<OpeningBracket>(lexer.next())

    val sortedVars = plus<ClosingBracket, SortedVar<*>>(program, ::parseSortedVar)

    requireIsInstance<ClosingBracket>(lexer.next())

    val term = program.context.forall(sortedVars) { parseTerm(program) }

    // TODO might want to add a try-catch around so if the cast fails we can have a more meaningful
    // error message
    return ForallExpression(sortedVars, term.cast())
  }

  @OptIn(ExperimentalContracts::class)
  private fun parseExists(program: MutableSMTProgram): ExistsExpression {
    // consume exists token
    lexer.next()

    // check and consume opening bracket
    requireIsInstance<OpeningBracket>(lexer.next())

    val sortedVars = plus<ClosingBracket, SortedVar<*>>(program, ::parseSortedVar)

    requireIsInstance<ClosingBracket>(lexer.next())

    val term = program.context.exists(sortedVars) { parseTerm(program) }

    // TODO might want to add a try-catch around so if the cast fails we can have a more meaningful
    // error message
    return ExistsExpression(sortedVars, term.cast())
  }

  private fun parseAnnotatedTerm(program: MutableSMTProgram): AnnotatedExpression<*> {
    // consume exclamation token
    lexer.next()

    val term = parseTerm(program)
    val attribute = TODO()

    return AnnotatedExpression(term, attribute)
  }

  @OptIn(ExperimentalContracts::class)
  private fun parseSortedVar(program: MutableSMTProgram): SortedVar<*> {
    requireIsInstance<OpeningBracket>(lexer.next())

    val symbol = parseSymbol()
    val sort = parseSort(program)

    requireIsInstance<ClosingBracket>(lexer.next())

    return SortedVar(symbol, sort)
  }

  @OptIn(ExperimentalContracts::class)
  private fun parseVarBinding(program: MutableSMTProgram): VarBinding<*> {
    requireIsInstance<OpeningBracket>(lexer.next())
    val symbol = parseSymbol()
    val term = parseTerm(program)
    requireIsInstance<ClosingBracket>(lexer.next())

    return VarBinding(symbol, term)
  }

  private fun parseSpecConstantTerm(
      program: MutableSMTProgram,
      token: SpecConstantToken,
  ): Expression<*> =
      when (val constant = parseSpecConstant(token)) {
        is BinaryConstant -> BVLiteral(constant.binary)
        is DecimalConstant -> RealLiteral(constant.decimal)
        is HexConstant -> BVLiteral(constant.hexadecimal)
        is NumeralConstant ->
            if (
                Theories.INTS in program.logic!!.theories ||
                    Theories.REALS_INTS in program.logic!!.theories
            )
                IntLiteral(constant.numeral)
            else if (Theories.REALS in program.logic!!.theories)
                RealLiteral(BigDecimal(constant.numeral))
            else if (Theories.STRINGS in program.logic!!.theories) IntLiteral(constant.numeral)
            else throw RuntimeException("Unsupported numeral literal!")

        is StringConstant -> StringLiteral(constant.string)
      }

  private fun parseSpecConstant(token: SpecConstantToken) =
      when (token) {
        is Decimal -> DecimalConstant(token.number)
        is Binary -> BinaryConstant(token.number.toString())
        is Hexadecimal -> HexConstant(token.number.toString())
        is Numeral -> NumeralConstant(token.number)
        is SMTString -> StringConstant(token.toString())
      }
}

/**
 * Checks if [actual] is instance of [T]. Uses [ExperimentalContracts] to tell the compiler that
 * [actual] can be smart cast to [T]
 *
 * @throws [UnexpectedTokenException] if [actual] is not instance of [T]
 */
@ExperimentalContracts
inline fun <reified T : Token> requireIsInstance(actual: Token): Boolean {
  contract { returns() implies (actual is T) }
  if (actual !is T) {
    throw UnexpectedTokenException(actual, T::class.toString())
  }

  return true
}

class UnexpectedTokenException(actual: Token, expected: String) :
    IllegalArgumentException("Expected token $expected but found $actual at ${actual.source}!")
