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

import java.io.Reader
import java.math.BigDecimal
import kotlin.contracts.ExperimentalContracts
import kotlin.contracts.contract
import kotlin.invoke
import tools.aqua.konstraints.parser.lexer.AsWord
import tools.aqua.konstraints.parser.lexer.AssertWord
import tools.aqua.konstraints.parser.lexer.Binary
import tools.aqua.konstraints.parser.lexer.CheckSatAssumingWord
import tools.aqua.konstraints.parser.lexer.CheckSatWord
import tools.aqua.konstraints.parser.lexer.ClosingBracket
import tools.aqua.konstraints.parser.lexer.CommandName
import tools.aqua.konstraints.parser.lexer.Decimal
import tools.aqua.konstraints.parser.lexer.DeclareConstWord
import tools.aqua.konstraints.parser.lexer.DeclareDatatypeWord
import tools.aqua.konstraints.parser.lexer.DeclareDatatypesWord
import tools.aqua.konstraints.parser.lexer.DeclareFunWord
import tools.aqua.konstraints.parser.lexer.DeclareSortParameterWord
import tools.aqua.konstraints.parser.lexer.DeclareSortWord
import tools.aqua.konstraints.parser.lexer.DefineConstWord
import tools.aqua.konstraints.parser.lexer.DefineFunRecWord
import tools.aqua.konstraints.parser.lexer.DefineFunWord
import tools.aqua.konstraints.parser.lexer.DefineSortWord
import tools.aqua.konstraints.parser.lexer.EOFToken
import tools.aqua.konstraints.parser.lexer.EchoWord
import tools.aqua.konstraints.parser.lexer.ExclamationWord
import tools.aqua.konstraints.parser.lexer.ExistsWord
import tools.aqua.konstraints.parser.lexer.ExitWord
import tools.aqua.konstraints.parser.lexer.ForallWord
import tools.aqua.konstraints.parser.lexer.GetAssertionsWord
import tools.aqua.konstraints.parser.lexer.GetAssignmentWord
import tools.aqua.konstraints.parser.lexer.GetInfoWord
import tools.aqua.konstraints.parser.lexer.GetModelWord
import tools.aqua.konstraints.parser.lexer.GetOptionWord
import tools.aqua.konstraints.parser.lexer.GetProofWord
import tools.aqua.konstraints.parser.lexer.GetUnsatAssumptionsWord
import tools.aqua.konstraints.parser.lexer.GetUnsatCoreWord
import tools.aqua.konstraints.parser.lexer.GetValueWord
import tools.aqua.konstraints.parser.lexer.Hexadecimal
import tools.aqua.konstraints.parser.lexer.KeywordToken
import tools.aqua.konstraints.parser.lexer.LambdaWord
import tools.aqua.konstraints.parser.lexer.LetWord
import tools.aqua.konstraints.parser.lexer.MatchWord
import tools.aqua.konstraints.parser.lexer.Numeral
import tools.aqua.konstraints.parser.lexer.OpeningBracket
import tools.aqua.konstraints.parser.lexer.ParWord
import tools.aqua.konstraints.parser.lexer.PopWord
import tools.aqua.konstraints.parser.lexer.PushWord
import tools.aqua.konstraints.parser.lexer.QuotedSymbolToken
import tools.aqua.konstraints.parser.lexer.ReservedWord
import tools.aqua.konstraints.parser.lexer.ResetAssertionsWord
import tools.aqua.konstraints.parser.lexer.ResetWord
import tools.aqua.konstraints.parser.lexer.SMTString
import tools.aqua.konstraints.parser.lexer.SMTTokenizer
import tools.aqua.konstraints.parser.lexer.SetInfoWord
import tools.aqua.konstraints.parser.lexer.SetLogicWord
import tools.aqua.konstraints.parser.lexer.SetOptionWord
import tools.aqua.konstraints.parser.lexer.SimpleSymbolToken
import tools.aqua.konstraints.parser.lexer.SpecConstantToken
import tools.aqua.konstraints.parser.lexer.SymbolToken
import tools.aqua.konstraints.parser.lexer.Token
import tools.aqua.konstraints.parser.lexer.UnderscoreWord
import tools.aqua.konstraints.parser.util.PeekableIterator
import tools.aqua.konstraints.parser.util.peekIs
import tools.aqua.konstraints.parser.util.peekIsNot
import tools.aqua.konstraints.parser.util.peekable
import tools.aqua.konstraints.smt.AnnotatedExpression
import tools.aqua.konstraints.smt.Attribute
import tools.aqua.konstraints.smt.AttributeValue
import tools.aqua.konstraints.smt.BVLiteral
import tools.aqua.konstraints.smt.BinaryConstant
import tools.aqua.konstraints.smt.CheckSat
import tools.aqua.konstraints.smt.ConstantAttributeValue
import tools.aqua.konstraints.smt.ConstructorDecl
import tools.aqua.konstraints.smt.Datatype
import tools.aqua.konstraints.smt.DecimalConstant
import tools.aqua.konstraints.smt.ExistsExpression
import tools.aqua.konstraints.smt.Exit
import tools.aqua.konstraints.smt.Expression
import tools.aqua.konstraints.smt.ForallExpression
import tools.aqua.konstraints.smt.FunctionDef
import tools.aqua.konstraints.smt.GetModel
import tools.aqua.konstraints.smt.GetValue
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
import tools.aqua.konstraints.smt.SExpression
import tools.aqua.konstraints.smt.SExpressionAttributeValue
import tools.aqua.konstraints.smt.SExpressionConstant
import tools.aqua.konstraints.smt.SExpressionKeyword
import tools.aqua.konstraints.smt.SExpressionReserved
import tools.aqua.konstraints.smt.SExpressionSymbol
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
import tools.aqua.konstraints.smt.assert
import tools.aqua.konstraints.smt.cast
import tools.aqua.konstraints.smt.declareFun
import tools.aqua.konstraints.smt.defineFun
import tools.aqua.konstraints.smt.setInfo
import tools.aqua.konstraints.smt.toSymbolAsIs
import tools.aqua.konstraints.smt.toSymbolWithQuotes

class Parser private constructor(val lexer: PeekableIterator<Token>) {
  companion object {
    operator fun invoke(input: String) =
        Parser(SMTTokenizer(input.reader()).peekable()).parseScript()

    operator fun invoke(input: Reader) = Parser(SMTTokenizer(input).peekable()).parseScript()
  }

  private fun parseScript(): MutableSMTProgram {
    val program = MutableSMTProgram()

    while (lexer.peek() !is EOFToken) {
      parseCommand(program)
    }

    return program
  }

  @OptIn(ExperimentalContracts::class)
  private fun parseCommand(program: MutableSMTProgram) {
    // TODO EOF token would help here as EOF is valid at this point
    // when the input ends on a whitespace or comment we skip that token and get EOF here
    // we are finished parsing so this state is valid
    requireIsInstance<OpeningBracket>(lexer.next())

    val commandName = lexer.next()
    requireIsInstance<CommandName>(commandName)

    when (commandName) {
      is AssertWord -> parseAssert(program)
      is CheckSatAssumingWord -> TODO("CheckSatAssumingWord")
      is CheckSatWord -> program.add(CheckSat)
      is DeclareConstWord -> parseDeclareConst(program)
      is DeclareDatatypeWord -> parseDatatype(program)
      is DeclareDatatypesWord -> TODO("DeclareDatatypesWord")
      is DeclareFunWord -> parseDeclareFun(program)
      is DeclareSortParameterWord -> TODO("DeclareSortParameterWord")
      is DeclareSortWord -> parseDeclareSort(program)
      is DefineConstWord -> parseDefineConst(program)
      is DefineFunRecWord -> TODO("DefineFunRecWord")
      is DefineFunWord -> parseDefineFun(program)
      is DefineSortWord -> parseDefineSort(program)
      is EchoWord -> TODO("EchoWord")
      is ExitWord -> program.add(Exit)
      is GetAssertionsWord -> TODO("GetAssertionsWord")
      is GetAssignmentWord -> TODO("GetAssignmentWord")
      is GetInfoWord -> TODO("GetInfoWord")
      is GetModelWord -> program.add(GetModel)
      is GetOptionWord -> TODO("GetOptionWord")
      is GetProofWord -> TODO("GetProofWord")
      is GetUnsatAssumptionsWord -> TODO("GetUnsatAssumptionsWord")
      is GetUnsatCoreWord -> TODO("GetUnsatCoreWord")
      is GetValueWord -> parseGetValue(program)
      is PopWord -> parsePop(program)
      is PushWord -> parsePush(program)
      is ResetAssertionsWord -> TODO("ResetAssertionsWord")
      is ResetWord -> TODO("ResetWord")
      is SetInfoWord -> parseSetInfo(program)
      is SetLogicWord -> parseSetLogic(program)
      is SetOptionWord -> TODO("SetOptionWord")
    }

    requireIsInstance<ClosingBracket>(lexer.next())
  }

  private fun parseDatatype(program: MutableSMTProgram) {
    val symbol = parseSymbol()
    val decl = parseDatatypeDecl(program)

    program.declareDatatype(Datatype(0, symbol, decl))
  }

  @OptIn(ExperimentalContracts::class)
  private fun parseDatatypeDecl(program: MutableSMTProgram): List<ConstructorDecl> {
    requireIsInstance<OpeningBracket>(lexer.next())

    // parametric datatypes
    if(lexer.peek() is ParWord) {
      TODO("Parametric datatypes are not supported yet!")
    }

    val constructorDecls = plus<ClosingBracket, ConstructorDecl> { parseConstructorDecl(program) }
    requireIsInstance<ClosingBracket>(lexer.next())

    return constructorDecls
  }

  @OptIn(ExperimentalContracts::class)
  private fun parseConstructorDecl(program: MutableSMTProgram): ConstructorDecl {
    requireIsInstance<OpeningBracket>(lexer.next())
    val symbol = parseSymbol()
    val selectorDecls = star<ClosingBracket, SelectorDecl<*>> { parseSelectorDecl(program) }
    requireIsInstance<ClosingBracket>(lexer.next())

    return ConstructorDecl(symbol, selectorDecls)
  }

  @OptIn(ExperimentalContracts::class)
  private fun parseSelectorDecl(program: MutableSMTProgram): SelectorDecl<*> {
    requireIsInstance<OpeningBracket>(lexer.next())
    val symbol = parseSymbol()
    val sort = parseSort(program)
    requireIsInstance<ClosingBracket>(lexer.next())

    return SelectorDecl(symbol, sort)
  }

  @OptIn(ExperimentalContracts::class)
  private fun parseGetValue(program: MutableSMTProgram) {
    requireIsInstance<OpeningBracket>(lexer.next())

    val terms = plus<ClosingBracket, Expression<*>> { parseTerm(program) }

    requireIsInstance<ClosingBracket>(lexer.next())

    // TODO implement get value in program
    program.add(GetValue(terms))
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
  private fun parseDeclareSort(program: MutableSMTProgram) {
    val symbol = parseSymbol()

    val numeralToken = lexer.next()
    requireIsInstance<Numeral>(numeralToken)

    program.declareSort(symbol, numeralToken.number.toInt())
  }

  @OptIn(ExperimentalContracts::class)
  private fun parseDefineSort(program: MutableSMTProgram) {
    val symbol = parseSymbol()

    // consume opening bracket
    requireIsInstance<OpeningBracket>(lexer.next())

    val typeParameter = star<ClosingBracket, Symbol>(::parseSymbol)

    // consume closing bracket
    requireIsInstance<ClosingBracket>(lexer.next())

    val sort = parseSort(program)

    program.defineSort(symbol, typeParameter, sort)
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
      when (lexer.peek()) {
        is SpecConstantToken -> ConstantAttributeValue(parseSpecConstant())
        is SymbolToken -> SymbolAttributeValue(parseSymbol())
        is OpeningBracket -> {
          val sExpression = mutableListOf<SExpression>()
          lexer.next()
          while (lexer.peekIsNot { token -> token is ClosingBracket }) {
            sExpression.add(parseSExpr(Unit))
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

  private val parseSExpr =
      DeepRecursiveFunction<Unit, SExpression> {
        when (lexer.peek()) {
          is SpecConstantToken -> SExpressionConstant(parseSpecConstant())
          is SymbolToken -> SExpressionSymbol(parseSymbol())
          is ReservedWord -> SExpressionReserved((lexer.next() as ReservedWord).word)
          is KeywordToken -> SExpressionKeyword((lexer.next() as KeywordToken).contents)
          is OpeningBracket -> {
            val sExpression = mutableListOf<SExpression>()
            lexer.next()
            while (lexer.peekIsNot { token -> token is ClosingBracket }) {
              sExpression.add(callRecursive(Unit))
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
  private fun parseSort(program: MutableSMTProgram): Sort =
      if (lexer.peekIs { token -> token is OpeningBracket }) {
        if (lexer.peekIs(depth = 1) { token -> token is UnderscoreWord }) {
          // indexed sort
          val identifier = parseIdentifier()

          require(identifier is IndexedIdentifier)
          program.context
              .getSort(identifier.symbol)
              .build(emptyList(), identifier.indices as List<NumeralIndex>)
        } else {
          // sort with arity > 0
          // parse a sort with arity > 0 or indexed sort
          // discard opening bracket
          lexer.next()

          val identifier = parseIdentifier()

          // this is parsed as ( <Identifier> <Sort>+ )
          val sorts = plus<ClosingBracket, Sort>(program, ::parseSort)
          requireIsInstance<ClosingBracket>(lexer.next())

          program.context.getSort(identifier.symbol).build(sorts, emptyList())
        }
      } else {
        // parse a simple sort with arity 0
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

      // discard opening bracket
      lexer.next()

      // check for underscore and discard
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
  val parseTerm =
      DeepRecursiveFunction<MutableSMTProgram, Expression<*>> { program ->
        when (lexer.peek()) {
          is SpecConstantToken -> {
            // here we get a literal
            parseSpecConstantTerm(program)
          }
          is SymbolToken -> {
            // smt function invocation with arity 0
            val symbolToken = lexer.next() as SymbolToken
            when (symbolToken) {
              is QuotedSymbolToken ->
                  program.context
                      .getFunc(symbolToken.toString().toSymbolWithQuotes())
                      .constructDynamic(emptyList(), emptyList())
              is SimpleSymbolToken ->
                  program.context
                      .getFunc(symbolToken.toString().toSymbolWithQuotes())
                      .constructDynamic(emptyList(), emptyList())
            }
          }
          is OpeningBracket -> {
            val expr =
                when (lexer.peek(depth = 1)) {
                  is UnderscoreWord -> {
                    // indexed identifier

                    val identifier = parseIdentifier()

                    require(identifier is IndexedIdentifier) {
                      "Expected indexed identifier but found ${identifier.javaClass}!"
                    }

                    // there is a special pseudo function (_ bv<Numeral> <Index>) that needs to be
                    // handled here
                    if (
                        identifier.symbol.value.startsWith("bv") &&
                            !identifier.symbol.isQuoted &&
                            program.context.containsSort("BitVec".toSymbolAsIs()) &&
                            identifier.symbol.value.substring(2).all { ch -> ch.isDigit() }
                    ) {
                      BVLiteral(
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
                  is LetWord -> parseLet.callRecursive(program)
                  is LambdaWord -> TODO("Lambda not implemented in konstraints yet")
                  is ForallWord -> parseForall(program)
                  is ExistsWord -> parseExists(program)
                  is MatchWord -> TODO("Match not implemented in konstraints yet")
                  is ExclamationWord -> parseAnnotatedTerm(program)
                  is SymbolToken -> {
                    // consume opening bracket
                    lexer.next()

                    // smt function with arity > 0 but not indexed (so e.g. not ((_ extract i j)
                    // bv_term))
                    val func = program.context.getFunc(parseSymbol())
                    val terms = mutableListOf<Expression<*>>()
                    do {
                      terms.add(callRecursive(program))
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
                        val identifier = parseIdentifier()

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
                          terms.add(callRecursive(program))
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
  val parseLet: DeepRecursiveFunction<MutableSMTProgram, LetExpression<*>> =
      DeepRecursiveFunction<MutableSMTProgram, LetExpression<*>> { program ->
        // TODO implement discard function with depth on iterator for cleaner code
        // consume opening bracket
        lexer.next()

        // consume let token
        lexer.next()

        // check and consume opening bracket for bindings
        requireIsInstance<OpeningBracket>(lexer.next())

        val bindings = plus<ClosingBracket, VarBinding<*>>(program, ::parseVarBinding)

        requireIsInstance<ClosingBracket>(lexer.next())

        // bind the bindings locally note that we can not use program.let since this is a deep
        // recursive scope
        program.context.bindVariables(bindings)
        val term = parseTerm.callRecursive<MutableSMTProgram, Expression<*>>(program)
        program.context.unbindVariables()

        // discard let closing bracket
        requireIsInstance<ClosingBracket>(lexer.next())

        LetExpression(bindings, term)
      }

  @OptIn(ExperimentalContracts::class)
  private fun parseForall(program: MutableSMTProgram): ForallExpression {
    // consume opening bracket
    lexer.next()

    // consume forall token
    lexer.next()

    // check and consume opening bracket
    requireIsInstance<OpeningBracket>(lexer.next())

    val sortedVars = plus<ClosingBracket, SortedVar<*>>(program, ::parseSortedVar)

    requireIsInstance<ClosingBracket>(lexer.next())

    val term = program.context.forall(sortedVars) { parseTerm(program) }

    // discard let closing bracket
    requireIsInstance<ClosingBracket>(lexer.next())

    // TODO might want to add a try-catch around so if the cast fails we can have a more meaningful
    // error message
    return ForallExpression(sortedVars, term.cast())
  }

  @OptIn(ExperimentalContracts::class)
  private fun parseExists(program: MutableSMTProgram): ExistsExpression {
    // consume opening bracket
    lexer.next()

    // consume exists token
    lexer.next()

    // check and consume opening bracket
    requireIsInstance<OpeningBracket>(lexer.next())

    val sortedVars = plus<ClosingBracket, SortedVar<*>>(program, ::parseSortedVar)

    requireIsInstance<ClosingBracket>(lexer.next())

    val term = program.context.exists(sortedVars) { parseTerm(program) }

    // discard let closing bracket
    requireIsInstance<ClosingBracket>(lexer.next())

    // TODO might want to add a try-catch around so if the cast fails we can have a more meaningful
    // error message
    return ExistsExpression(sortedVars, term.cast())
  }

  @OptIn(ExperimentalContracts::class)
  private fun parseAnnotatedTerm(program: MutableSMTProgram): AnnotatedExpression<*> {
    // consume opening bracket
    lexer.next()

    // consume exclamation token
    lexer.next()

    val term = parseTerm(program)
    val attributes = plus<ClosingBracket, Attribute>(::parseAttribute)

    // discard let closing bracket
    requireIsInstance<ClosingBracket>(lexer.next())

    return AnnotatedExpression(term, attributes)
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

  private fun parseSpecConstantTerm(program: MutableSMTProgram): Expression<*> =
      when (val constant = parseSpecConstant()) {
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

  @OptIn(ExperimentalContracts::class)
  private fun parseSpecConstant(): SpecConstant {
    val token = lexer.next()
    requireIsInstance<SpecConstantToken>(token)
    return when (token) {
      is Decimal -> DecimalConstant(token.number)
      is Binary -> BinaryConstant(token.toString())
      is Hexadecimal -> HexConstant(token.toString())
      is Numeral -> NumeralConstant(token.number)
      is SMTString -> StringConstant(token.contents)
    }
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
