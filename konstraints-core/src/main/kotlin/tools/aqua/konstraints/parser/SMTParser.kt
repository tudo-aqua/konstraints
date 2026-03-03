/*
 * SPDX-License-Identifier: Apache-2.0
 *
 * Copyright 2023-2026 The Konstraints Authors
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
import tools.aqua.konstraints.parser.lexer.AsWord
import tools.aqua.konstraints.parser.lexer.Binary
import tools.aqua.konstraints.parser.lexer.ClosingBracket
import tools.aqua.konstraints.parser.lexer.Decimal
import tools.aqua.konstraints.parser.lexer.ExclamationWord
import tools.aqua.konstraints.parser.lexer.ExistsWord
import tools.aqua.konstraints.parser.lexer.ForallWord
import tools.aqua.konstraints.parser.lexer.Hexadecimal
import tools.aqua.konstraints.parser.lexer.KeywordToken
import tools.aqua.konstraints.parser.lexer.LambdaWord
import tools.aqua.konstraints.parser.lexer.LetWord
import tools.aqua.konstraints.parser.lexer.MatchWord
import tools.aqua.konstraints.parser.lexer.Numeral
import tools.aqua.konstraints.parser.lexer.OpeningBracket
import tools.aqua.konstraints.parser.lexer.ParWord
import tools.aqua.konstraints.parser.lexer.QuotedSymbolToken
import tools.aqua.konstraints.parser.lexer.ReservedWord
import tools.aqua.konstraints.parser.lexer.SMTStringToken
import tools.aqua.konstraints.parser.lexer.SimpleSymbolToken
import tools.aqua.konstraints.parser.lexer.SpecConstantToken
import tools.aqua.konstraints.parser.lexer.SymbolToken
import tools.aqua.konstraints.parser.lexer.Token
import tools.aqua.konstraints.parser.lexer.UnderscoreWord
import tools.aqua.konstraints.parser.util.PeekableIterator
import tools.aqua.konstraints.parser.util.peekIs
import tools.aqua.konstraints.parser.util.peekIsNot
import tools.aqua.konstraints.smt.AnnotatedExpression
import tools.aqua.konstraints.smt.Attribute
import tools.aqua.konstraints.smt.AttributeValue
import tools.aqua.konstraints.smt.BinaryConstant
import tools.aqua.konstraints.smt.BitVecLiteral
import tools.aqua.konstraints.smt.ConstantAttributeValue
import tools.aqua.konstraints.smt.ConstructorDecl
import tools.aqua.konstraints.smt.DecimalConstant
import tools.aqua.konstraints.smt.ExistsExpression
import tools.aqua.konstraints.smt.Expression
import tools.aqua.konstraints.smt.ForallExpression
import tools.aqua.konstraints.smt.HexConstant
import tools.aqua.konstraints.smt.Identifier
import tools.aqua.konstraints.smt.Index
import tools.aqua.konstraints.smt.IndexedIdentifier
import tools.aqua.konstraints.smt.IntLiteral
import tools.aqua.konstraints.smt.LetExpression
import tools.aqua.konstraints.smt.NumeralConstant
import tools.aqua.konstraints.smt.NumeralIndex
import tools.aqua.konstraints.smt.RealLiteral
import tools.aqua.konstraints.smt.SExpression
import tools.aqua.konstraints.smt.SExpressionAttributeValue
import tools.aqua.konstraints.smt.SExpressionConstant
import tools.aqua.konstraints.smt.SExpressionKeyword
import tools.aqua.konstraints.smt.SExpressionReserved
import tools.aqua.konstraints.smt.SExpressionSymbol
import tools.aqua.konstraints.smt.SMTProgram
import tools.aqua.konstraints.smt.SelectorDecl
import tools.aqua.konstraints.smt.Sort
import tools.aqua.konstraints.smt.SortedVar
import tools.aqua.konstraints.smt.SpecConstant
import tools.aqua.konstraints.smt.StringConstant
import tools.aqua.konstraints.smt.StringLiteral
import tools.aqua.konstraints.smt.SubSExpression
import tools.aqua.konstraints.smt.Symbol
import tools.aqua.konstraints.smt.SymbolAttributeValue
import tools.aqua.konstraints.smt.SymbolIdentifier
import tools.aqua.konstraints.smt.SymbolIndex
import tools.aqua.konstraints.smt.Theories
import tools.aqua.konstraints.smt.VarBinding
import tools.aqua.konstraints.smt.cast
import tools.aqua.konstraints.smt.toSymbol

internal object SMTParser {
  @OptIn(ExperimentalContracts::class)
  internal fun parseDatatypeDecl(
      lexer: PeekableIterator<Token>,
      program: SMTProgram,
  ): List<ConstructorDecl> {
    requireIsInstance<OpeningBracket>(lexer.next())

    // parametric datatypes
    if (lexer.peek() is ParWord) {
      TODO("Parametric datatypes are not supported yet!")
    }

    val constructorDecls =
        plus<ClosingBracket, SMTProgram, ConstructorDecl>(lexer, program, ::parseConstructorDecl)
    requireIsInstance<ClosingBracket>(lexer.next())

    return constructorDecls
  }

  @OptIn(ExperimentalContracts::class)
  internal fun parseConstructorDecl(
      lexer: PeekableIterator<Token>,
      program: SMTProgram,
  ): ConstructorDecl {
    requireIsInstance<OpeningBracket>(lexer.next())
    val symbol = parseSymbol(lexer)
    val selectorDecls =
        star<ClosingBracket, SMTProgram, SelectorDecl<*>>(lexer, program, ::parseSelectorDecl)
    requireIsInstance<ClosingBracket>(lexer.next())

    return ConstructorDecl(symbol, selectorDecls)
  }

  @OptIn(ExperimentalContracts::class)
  internal fun parseSelectorDecl(
      lexer: PeekableIterator<Token>,
      program: SMTProgram,
  ): SelectorDecl<*> {
    requireIsInstance<OpeningBracket>(lexer.next())
    val symbol = parseSymbol(lexer)
    val sort = parseSort(lexer, program)
    requireIsInstance<ClosingBracket>(lexer.next())

    return SelectorDecl(symbol, sort)
  }

  @OptIn(ExperimentalContracts::class)
  internal fun parseAttribute(lexer: PeekableIterator<Token>): Attribute {
    val keyword = lexer.next()
    requireIsInstance<KeywordToken>(keyword)

    val value =
        if (lexer.peekIsNot { token -> token is ClosingBracket }) {
          // attribute has an attached value
          parseAttributeValue(lexer)
        } else null

    return Attribute(keyword.toString(), value)
  }

  internal fun parseAttributeValue(lexer: PeekableIterator<Token>): AttributeValue =
      when (lexer.peek()) {
        is SpecConstantToken -> ConstantAttributeValue(parseSpecConstant(lexer))
        is SymbolToken -> SymbolAttributeValue(parseSymbol(lexer))
        is OpeningBracket -> {
          val sExpression = mutableListOf<SExpression>()
          lexer.next()
          while (lexer.peekIsNot { token -> token is ClosingBracket }) {
            sExpression.add(parseSExpr(lexer))
          }
          lexer.next()
          SExpressionAttributeValue(sExpression)
        }
        else ->
            throw UnexpectedTokenException(
                lexer.peek(),
                "any of SpecConstantToken, SymbolToken or OpeningBracket",
            )
      }

  internal val parseSExpr =
      DeepRecursiveFunction<PeekableIterator<Token>, SExpression> { lexer ->
        when (lexer.peek()) {
          is SpecConstantToken -> SExpressionConstant(parseSpecConstant(lexer))
          is SymbolToken -> SExpressionSymbol(parseSymbol(lexer))
          is ReservedWord -> SExpressionReserved((lexer.next() as ReservedWord).word)
          is KeywordToken -> SExpressionKeyword((lexer.next() as KeywordToken).contents)
          is OpeningBracket -> {
            val sExpression = mutableListOf<SExpression>()
            lexer.next()
            while (lexer.peekIsNot { token -> token is ClosingBracket }) {
              sExpression.add(callRecursive(lexer))
            }
            lexer.next()
            SubSExpression(sExpression)
          }
          else ->
              throw UnexpectedTokenException(
                  lexer.peek(),
                  "any of SpecConstantToken, SymbolToken, ReservedWord, KeywordToken or OpeningBracket",
              )
        }
      }

  @OptIn(ExperimentalContracts::class)
  internal fun parseSymbol(
      lexer: PeekableIterator<Token>,
  ): Symbol {
    val symbol = lexer.next()
    requireIsInstance<SymbolToken>(symbol)

    return when (symbol) {
      // for quoted symbol we can not immediately know if they are simple or not (that is valid
      // without quotes)
      // so the Symbol constructor has to check again to set the isSimple flag correct
      is QuotedSymbolToken -> Symbol(symbol.toString(), true)
      is SimpleSymbolToken -> Symbol(symbol.toString(), false, true)
    }
  }

  /*
   * Sort is defined as
   * sort ::= <identifier> | ( <identifier> <sort>+ )
   * We substitute <identifier> so we get
   * sort ::= <symbol> | ( _ <symbol> <index>+ ) | ( <identifier> <sort>+ )
   */
  @OptIn(ExperimentalContracts::class)
  internal fun parseSort(lexer: PeekableIterator<Token>, program: SMTProgram): Sort =
      if (lexer.peekIs { token -> token is OpeningBracket }) {
        if (lexer.peekIs(depth = 1) { token -> token is UnderscoreWord }) {
          // indexed sort
          val identifier = parseIdentifier(lexer)

          require(identifier is IndexedIdentifier)
          program.context
              .getSort(identifier.symbol)
              .build(emptyList(), identifier.indices as List<NumeralIndex>)
        } else {
          // sort with arity > 0
          // parse a sort with arity > 0 or indexed sort
          // discard opening bracket
          lexer.next()

          val identifier = parseIdentifier(lexer)

          // this is parsed as ( <Identifier> <Sort>+ )
          val sorts = plus<ClosingBracket, SMTProgram, Sort>(lexer, program, ::parseSort)
          requireIsInstance<ClosingBracket>(lexer.next())

          program.context.getSort(identifier.symbol).build(sorts, emptyList())
        }
      } else {
        // parse a simple sort with arity 0
        when (val identifier = parseIdentifier(lexer)) {
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
  internal fun parseIdentifier(
      lexer: PeekableIterator<Token>,
  ): Identifier {
    if (lexer.peekIs { token -> token is OpeningBracket }) {
      // parse indexed identifier

      // discard opening bracket
      lexer.next()

      // check for underscore and discard
      requireIsInstance<UnderscoreWord>(lexer.next())

      val symbol = parseSymbol(lexer)
      val indices = plus<ClosingBracket, Index>(lexer, ::parseIndex)

      requireIsInstance<ClosingBracket>(lexer.next())

      return IndexedIdentifier(symbol, indices)
    } else {
      // parse simple identifier

      return SymbolIdentifier(parseSymbol(lexer))
    }
  }

  @OptIn(ExperimentalContracts::class)
  internal fun parseIndex(
      lexer: PeekableIterator<Token>,
  ): Index {
    if (lexer.peekIs { token -> token is SymbolToken }) {
      return SymbolIndex(parseSymbol(lexer))
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
  val parseTerm =
      DeepRecursiveFunction<Pair<PeekableIterator<Token>, SMTProgram>, Expression<*>> {
          (lexer, program) ->
        when (lexer.peek()) {
          is SpecConstantToken -> {
            // here we get a literal
            parseSpecConstantTerm(lexer, program)
          }
          is SymbolToken -> {
            // smt function invocation with arity 0
            val symbolToken = lexer.next() as SymbolToken
            when (symbolToken) {
              is QuotedSymbolToken ->
                  program.context
                      .getFunc(symbolToken.toString().toSymbol())
                      .constructDynamic(emptyList(), emptyList())
              is SimpleSymbolToken ->
                  program.context
                      .getFunc(symbolToken.toString().toSymbol())
                      .constructDynamic(emptyList(), emptyList())
            }
          }
          is OpeningBracket -> {
            val expr =
                when (lexer.peek(depth = 1)) {
                  is UnderscoreWord -> {
                    // indexed identifier

                    val identifier = parseIdentifier(lexer)

                    require(identifier is IndexedIdentifier) {
                      "Expected indexed identifier but found ${identifier.javaClass}!"
                    }

                    // there is a special pseudo function (_ bv<Numeral> <Index>) that needs to be
                    // handled here
                    if (
                        identifier.symbol.value.startsWith("bv") &&
                            !identifier.symbol.isQuoted &&
                            program.context.containsSort("BitVec".toSymbol()) &&
                            identifier.symbol.value.substring(2).all { ch -> ch.isDigit() }
                    ) {
                      BitVecLiteral(
                          identifier.symbol.value,
                          (identifier.indices.single() as NumeralIndex).numeral,
                      )
                    } else {
                      program.context
                          .getFunc(identifier.symbol)
                          .constructDynamic(emptyList(), identifier.indices)
                    }
                  }
                  is AsWord -> TODO("As not implemented in konstraints yet")
                  is LetWord -> parseLet.callRecursive(lexer to program)
                  is LambdaWord -> TODO("Lambda not implemented in konstraints yet")
                  is ForallWord -> parseForall(lexer, program)
                  is ExistsWord -> parseExists(lexer, program)
                  is MatchWord -> TODO("Match not implemented in konstraints yet")
                  is ExclamationWord -> parseAnnotatedTerm(lexer, program)
                  is SymbolToken -> {
                    // consume opening bracket
                    lexer.next()

                    // smt function with arity > 0 but not indexed (so e.g. not ((_ extract i j)
                    // bv_term))
                    val func = program.context.getFunc(parseSymbol(lexer))
                    val terms = mutableListOf<Expression<*>>()
                    do {
                      terms.add(callRecursive(lexer to program))
                    } while (lexer.peekIsNot { token -> token is ClosingBracket })

                    // discard let closing bracket
                    requireIsInstance<ClosingBracket>(lexer.next())

                    func.constructDynamic(terms, emptyList())
                  }
                  is OpeningBracket -> {
                    // discard opening bracket
                    lexer.next()

                    when (lexer.peek(depth = 1)) {
                      is AsWord -> TODO("As not implemented in konstraints yet")
                      is UnderscoreWord -> {
                        // indexed function with arity > 0
                        val identifier = parseIdentifier(lexer)

                        // check and smart cast identifier
                        require(identifier is IndexedIdentifier) {
                          "Expected IndexedIdentifier but found ${identifier.javaClass}"
                        }

                        val indices = identifier.indices
                        require(indices.all { index -> index is NumeralIndex }) {
                          "Expected all indices to be numeral but found at least one symbolic"
                        }

                        // plus need to be implemented by hand here since we are in a deep recursive
                        // function
                        // that needs to be called inside the plus lambda
                        val terms = mutableListOf<Expression<*>>()
                        do {
                          terms.add(callRecursive(lexer to program))
                        } while (lexer.peekIsNot { token -> token is ClosingBracket })

                        // consume closing bracket of the whole term not the identifier
                        requireIsInstance<ClosingBracket>(lexer.next())

                        program.context.getFunc(identifier.symbol).constructDynamic(terms, indices)
                      }
                      else ->
                          throw UnexpectedTokenException(
                              lexer.peek(depth = 1),
                              "any of AsWord or UnderscoreWord",
                          )
                    }
                  }
                  else ->
                      throw UnexpectedTokenException(
                          lexer.peek(depth = 1),
                          "any of AsWord, LetWord, LambdaWord, ForallWord, ExistsWord, MatchWord, ExclamationWord, SymbolToken or OpeningBracket",
                      )
                }

            expr
          }
          else ->
              throw UnexpectedTokenException(
                  lexer.peek(),
                  "any of SpecConstantToken, SymbolToken or OpeningBracket",
              )
        }
      }

  /**
   * Parse a let including the opening and closing bracket (importantly the opening bracket must not
   * be consumed before calling this function)
   */
  @OptIn(ExperimentalContracts::class)
  val parseLet: DeepRecursiveFunction<Pair<PeekableIterator<Token>, SMTProgram>, LetExpression<*>> =
      DeepRecursiveFunction<Pair<PeekableIterator<Token>, SMTProgram>, LetExpression<*>> {
          (lexer, program) ->
        // TODO implement discard function with depth on iterator for cleaner code
        // consume opening bracket
        lexer.next()

        // consume let token
        lexer.next()

        // check and consume opening bracket for bindings
        requireIsInstance<OpeningBracket>(lexer.next())

        val bindings =
            plus<ClosingBracket, SMTProgram, VarBinding<*>>(lexer, program, ::parseVarBinding)

        requireIsInstance<ClosingBracket>(lexer.next())

        // bind the bindings locally note that we can not use program.let since this is a deep
        // recursive scope
        program.context.bindVariables(bindings)
        val term = parseTerm.callRecursive(lexer to program)
        program.context.unbindVariables()

        // discard let closing bracket
        requireIsInstance<ClosingBracket>(lexer.next())

        LetExpression(bindings, term)
      }

  @OptIn(ExperimentalContracts::class)
  internal fun parseForall(
      lexer: PeekableIterator<Token>,
      program: SMTProgram,
  ): ForallExpression {
    // consume opening bracket
    lexer.next()

    // consume forall token
    lexer.next()

    // check and consume opening bracket
    requireIsInstance<OpeningBracket>(lexer.next())

    val sortedVars =
        plus<ClosingBracket, SMTProgram, SortedVar<*>>(lexer, program, ::parseSortedVar)

    requireIsInstance<ClosingBracket>(lexer.next())

    val term = program.context.forall(sortedVars) { parseTerm(lexer to program) }

    // discard let closing bracket
    requireIsInstance<ClosingBracket>(lexer.next())

    // TODO might want to add a try-catch around so if the cast fails we can have a more meaningful
    // error message
    return ForallExpression(sortedVars, term.cast())
  }

  @OptIn(ExperimentalContracts::class)
  internal fun parseExists(
      lexer: PeekableIterator<Token>,
      program: SMTProgram,
  ): ExistsExpression {
    // consume opening bracket
    lexer.next()

    // consume exists token
    lexer.next()

    // check and consume opening bracket
    requireIsInstance<OpeningBracket>(lexer.next())

    val sortedVars =
        plus<ClosingBracket, SMTProgram, SortedVar<*>>(lexer, program, ::parseSortedVar)

    requireIsInstance<ClosingBracket>(lexer.next())

    val term = program.context.exists(sortedVars) { parseTerm(lexer to program) }

    // discard let closing bracket
    requireIsInstance<ClosingBracket>(lexer.next())

    // TODO might want to add a try-catch around so if the cast fails we can have a more meaningful
    // error message
    return ExistsExpression(sortedVars, term.cast())
  }

  @OptIn(ExperimentalContracts::class)
  internal fun parseAnnotatedTerm(
      lexer: PeekableIterator<Token>,
      program: SMTProgram,
  ): AnnotatedExpression<*> {
    // consume opening bracket
    lexer.next()

    // consume exclamation token
    lexer.next()

    val term = parseTerm(lexer to program)
    val attributes = plus<ClosingBracket, Attribute>(lexer, ::parseAttribute)

    // discard let closing bracket
    requireIsInstance<ClosingBracket>(lexer.next())

    return AnnotatedExpression(term, attributes)
  }

  @OptIn(ExperimentalContracts::class)
  internal fun parseSortedVar(
      lexer: PeekableIterator<Token>,
      program: SMTProgram,
  ): SortedVar<*> {
    requireIsInstance<OpeningBracket>(lexer.next())

    val symbol = parseSymbol(lexer)
    val sort = parseSort(lexer, program)

    requireIsInstance<ClosingBracket>(lexer.next())

    return SortedVar(symbol, sort)
  }

  @OptIn(ExperimentalContracts::class)
  internal fun parseVarBinding(
      lexer: PeekableIterator<Token>,
      program: SMTProgram,
  ): VarBinding<*> {
    requireIsInstance<OpeningBracket>(lexer.next())
    val symbol = parseSymbol(lexer)
    val term = parseTerm(lexer to program)
    requireIsInstance<ClosingBracket>(lexer.next())

    return VarBinding(symbol, term)
  }

  internal fun parseSpecConstantTerm(
      lexer: PeekableIterator<Token>,
      program: SMTProgram,
  ): Expression<*> =
      when (val constant = parseSpecConstant(lexer)) {
        is BinaryConstant -> BitVecLiteral(constant.binary)
        is DecimalConstant -> RealLiteral(constant.decimal)
        is HexConstant -> BitVecLiteral(constant.hexadecimal)
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

  @OptIn(ExperimentalContracts::class)
  internal fun parseSpecConstant(
      lexer: PeekableIterator<Token>,
  ): SpecConstant {
    val token = lexer.next()
    requireIsInstance<SpecConstantToken>(token)
    return when (token) {
      is Decimal -> DecimalConstant(token.number)
      is Binary -> BinaryConstant(token.toString())
      is Hexadecimal -> HexConstant(token.toString())
      is Numeral -> NumeralConstant(token.number)
      is SMTStringToken -> StringConstant(token.contents)
    }
  }
}

// all these function will not discard the stop token so the user does not unexpectedly lose a
// token
/**
 * Implements star operator, parsing objects using [parser] until a token of type [T] is reach, the
 * final token will NOT be discarded.
 */
@OptIn(ExperimentalContracts::class)
internal inline fun <reified T : Token, P : SMTProgram, S> star(
    lexer: PeekableIterator<Token>,
    program: P,
    parser: (PeekableIterator<Token>, P) -> S,
): List<S> {
  val results = mutableListOf<S>()
  while (lexer.peekIsNot { token -> token is T }) {
    results.add(parser(lexer, program))
  }

  return results
}

/**
 * Implements star operator, parsing objects using [parser] until a token of type [T] is reach, the
 * final token will NOT be discarded.
 */
@OptIn(ExperimentalContracts::class)
internal inline fun <reified T : Token, S> star(
    lexer: PeekableIterator<Token>,
    parser: (PeekableIterator<Token>) -> S,
): List<S> {
  val results = mutableListOf<S>()
  while (lexer.peekIsNot { token -> token is T }) {
    results.add(parser(lexer))
  }

  return results
}

/**
 * Implements plus (this is match at least once) operator, parsing objects using [parser] until a
 * token of type [T] is reach, the final token will NOT be discarded.
 */
@OptIn(ExperimentalContracts::class)
internal inline fun <reified T : Token, P : SMTProgram, S> plus(
    lexer: PeekableIterator<Token>,
    program: P,
    parser: (PeekableIterator<Token>, P) -> S,
): List<S> {
  val results = mutableListOf<S>()
  do {
    results.add(parser(lexer, program))
  } while (lexer.peekIsNot { token -> token is T })

  return results
}

/**
 * Implements plus (this is match at least once) operator, parsing objects using [parser] until a
 * token of type [T] is reach, the final token will NOT be discarded.
 */
@OptIn(ExperimentalContracts::class)
internal inline fun <reified T : Token, S> plus(
    lexer: PeekableIterator<Token>,
    parser: (PeekableIterator<Token>) -> S,
): List<S> {
  val results = mutableListOf<S>()
  do {
    results.add(parser(lexer))
  } while (lexer.peekIsNot { token -> token is T })

  return results
}

/**
 * Checks if [actual] is instance of [T]. Uses [kotlin.contracts.ExperimentalContracts] to tell the
 * compiler that [actual] can be smart cast to [T]
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
