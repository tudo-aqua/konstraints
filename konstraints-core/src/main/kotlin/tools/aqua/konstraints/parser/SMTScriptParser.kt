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
import kotlin.contracts.ExperimentalContracts
import kotlin.invoke
import tools.aqua.konstraints.parser.lexer.AssertWord
import tools.aqua.konstraints.parser.lexer.CheckSatAssumingWord
import tools.aqua.konstraints.parser.lexer.CheckSatWord
import tools.aqua.konstraints.parser.lexer.ClosingBracket
import tools.aqua.konstraints.parser.lexer.CommandName
import tools.aqua.konstraints.parser.lexer.DeclareConstWord
import tools.aqua.konstraints.parser.lexer.DeclareDatatypeWord
import tools.aqua.konstraints.parser.lexer.DeclareDatatypesWord
import tools.aqua.konstraints.parser.lexer.DeclareFunWord
import tools.aqua.konstraints.parser.lexer.DeclareSortParameterWord
import tools.aqua.konstraints.parser.lexer.DeclareSortWord
import tools.aqua.konstraints.parser.lexer.DefineConstWord
import tools.aqua.konstraints.parser.lexer.DefineFunRecWord
import tools.aqua.konstraints.parser.lexer.DefineFunWord
import tools.aqua.konstraints.parser.lexer.DefineFunsRecWord
import tools.aqua.konstraints.parser.lexer.DefineSortWord
import tools.aqua.konstraints.parser.lexer.EOFToken
import tools.aqua.konstraints.parser.lexer.EchoWord
import tools.aqua.konstraints.parser.lexer.ExitWord
import tools.aqua.konstraints.parser.lexer.GetAssertionsWord
import tools.aqua.konstraints.parser.lexer.GetAssignmentWord
import tools.aqua.konstraints.parser.lexer.GetInfoWord
import tools.aqua.konstraints.parser.lexer.GetModelWord
import tools.aqua.konstraints.parser.lexer.GetOptionWord
import tools.aqua.konstraints.parser.lexer.GetProofWord
import tools.aqua.konstraints.parser.lexer.GetUnsatAssumptionsWord
import tools.aqua.konstraints.parser.lexer.GetUnsatCoreWord
import tools.aqua.konstraints.parser.lexer.GetValueWord
import tools.aqua.konstraints.parser.lexer.Numeral
import tools.aqua.konstraints.parser.lexer.OpeningBracket
import tools.aqua.konstraints.parser.lexer.PopWord
import tools.aqua.konstraints.parser.lexer.PushWord
import tools.aqua.konstraints.parser.lexer.ResetAssertionsWord
import tools.aqua.konstraints.parser.lexer.ResetWord
import tools.aqua.konstraints.parser.lexer.SMTTokenizer
import tools.aqua.konstraints.parser.lexer.SetInfoWord
import tools.aqua.konstraints.parser.lexer.SetLogicWord
import tools.aqua.konstraints.parser.lexer.SetOptionWord
import tools.aqua.konstraints.parser.lexer.Token
import tools.aqua.konstraints.parser.util.PeekableIterator
import tools.aqua.konstraints.parser.util.peekable
import tools.aqua.konstraints.smt.CheckSat
import tools.aqua.konstraints.smt.Exit
import tools.aqua.konstraints.smt.Expression
import tools.aqua.konstraints.smt.FunctionDef
import tools.aqua.konstraints.smt.GetModel
import tools.aqua.konstraints.smt.GetValue
import tools.aqua.konstraints.smt.Logic
import tools.aqua.konstraints.smt.MutableSMTProgram
import tools.aqua.konstraints.smt.SMTProgram
import tools.aqua.konstraints.smt.Sort
import tools.aqua.konstraints.smt.SortedVar
import tools.aqua.konstraints.smt.Symbol
import tools.aqua.konstraints.smt.assert
import tools.aqua.konstraints.smt.cast
import tools.aqua.konstraints.smt.declareFun
import tools.aqua.konstraints.smt.defineFun
import tools.aqua.konstraints.smt.setInfo

object SMTScriptParser {
  operator fun invoke(input: String) =
      SMTScriptParser.parseScript(SMTTokenizer(input.reader()).peekable())

  operator fun invoke(input: Reader) = SMTScriptParser.parseScript(SMTTokenizer(input).peekable())

  internal fun parseScript(lexer: PeekableIterator<Token>): MutableSMTProgram {
    val program = MutableSMTProgram()

    while (lexer.peek() !is EOFToken) {
      parseCommand(lexer, program)
    }

    return program
  }

  @OptIn(ExperimentalContracts::class)
  internal fun parseCommand(lexer: PeekableIterator<Token>, program: MutableSMTProgram) {
    // TODO EOF token would help here as EOF is valid at this point
    // when the input ends on a whitespace or comment we skip that token and get EOF here
    // we are finished parsing so this state is valid
    requireIsInstance<OpeningBracket>(lexer.next())

    val commandName = lexer.next()
    requireIsInstance<CommandName>(commandName)

    when (commandName) {
      is AssertWord -> parseAssert(lexer, program)
      is CheckSatAssumingWord -> TODO("CheckSatAssumingWord")
      is CheckSatWord -> program.add(CheckSat)
      is DeclareConstWord -> parseDeclareConst(lexer, program)
      is DeclareDatatypeWord -> parseDatatype(lexer, program)
      is DeclareDatatypesWord -> TODO("DeclareDatatypesWord")
      is DeclareFunWord -> parseDeclareFun(lexer, program)
      is DeclareSortParameterWord -> TODO("DeclareSortParameterWord")
      is DeclareSortWord -> parseDeclareSort(lexer, program)
      is DefineConstWord -> parseDefineConst(lexer, program)
      is DefineFunRecWord -> TODO("DefineFunRecWord")
      is DefineFunsRecWord -> TODO("DefineFunsRecWord")
      is DefineFunWord -> parseDefineFun(lexer, program)
      is DefineSortWord -> parseDefineSort(lexer, program)
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
      is GetValueWord -> parseGetValue(lexer, program)
      is PopWord -> parsePop(lexer, program)
      is PushWord -> parsePush(lexer, program)
      is ResetAssertionsWord -> TODO("ResetAssertionsWord")
      is ResetWord -> TODO("ResetWord")
      is SetInfoWord -> parseSetInfo(lexer, program)
      is SetLogicWord -> parseSetLogic(lexer, program)
      is SetOptionWord -> TODO("SetOptionWord")
    }

    requireIsInstance<ClosingBracket>(lexer.next())
  }

  private fun parseDatatype(lexer: PeekableIterator<Token>, program: MutableSMTProgram) {
    val symbol = SMTParser.parseSymbol(lexer)

    val datatype = program.declareEmptyDatatype(0, symbol)

    val decl = SMTParser.parseDatatypeDecl(lexer, program)
    decl.forEach { t -> datatype.add(t) }

    program.finishDatatype(datatype)
  }

  @OptIn(ExperimentalContracts::class)
  internal fun parseGetValue(lexer: PeekableIterator<Token>, program: MutableSMTProgram) {
    requireIsInstance<OpeningBracket>(lexer.next())

    val terms = plus<ClosingBracket, Expression<*>>(lexer) { SMTParser.parseTerm(lexer to program) }

    requireIsInstance<ClosingBracket>(lexer.next())

    // TODO implement get value in program
    program.add(GetValue(terms))
  }

  internal fun parseAssert(lexer: PeekableIterator<Token>, program: MutableSMTProgram) {
    program.assert(SMTParser.parseTerm(lexer to program).cast())
  }

  internal fun parseDeclareConst(lexer: PeekableIterator<Token>, program: MutableSMTProgram) {
    val symbol = SMTParser.parseSymbol(lexer)
    val sort = SMTParser.parseSort(lexer, program)

    program.declareConst(symbol, sort)
  }

  @OptIn(ExperimentalContracts::class)
  internal fun parseDeclareFun(lexer: PeekableIterator<Token>, program: MutableSMTProgram) {
    val symbol = SMTParser.parseSymbol(lexer)

    requireIsInstance<OpeningBracket>(lexer.next())
    val sorts = star<ClosingBracket, SMTProgram, Sort>(lexer, program, SMTParser::parseSort)
    requireIsInstance<ClosingBracket>(lexer.next())

    val sort = SMTParser.parseSort(lexer, program)

    program.declareFun(symbol, sorts, sort)
  }

  internal fun parseDefineConst(lexer: PeekableIterator<Token>, program: MutableSMTProgram) {
    val symbol = SMTParser.parseSymbol(lexer)
    val sort = SMTParser.parseSort(lexer, program)
    val term = SMTParser.parseTerm(lexer to program)

    program.defineConst(symbol, sort, term)
  }

  @OptIn(ExperimentalContracts::class)
  internal fun parseDefineFun(lexer: PeekableIterator<Token>, program: MutableSMTProgram) {
    program.defineFun(parseFuncDef(lexer, program))
  }

  @OptIn(ExperimentalContracts::class)
  internal fun parseFuncDef(
      lexer: PeekableIterator<Token>,
      program: SMTProgram,
  ): FunctionDef<*> {
    val symbol = SMTParser.parseSymbol(lexer)

    requireIsInstance<OpeningBracket>(lexer.next())
    val sortedVars =
        star<ClosingBracket, SMTProgram, SortedVar<*>>(lexer, program, SMTParser::parseSortedVar)
    requireIsInstance<ClosingBracket>(lexer.next())

    val sort = SMTParser.parseSort(lexer, program)

    // bind the local variables for this function that can be used locally
    // TODO implement a more let like syntax bind/unbind do not need to be split anymore
    program.context.bindVariables(sortedVars)
    val term = SMTParser.parseTerm(lexer to program)
    program.context.unbindVariables()

    return FunctionDef(symbol, sortedVars, sort, term)
  }

  internal fun parseSetLogic(lexer: PeekableIterator<Token>, program: MutableSMTProgram) {
    val symbol = SMTParser.parseSymbol(lexer)
    program.setLogic(
        Logic.logics[symbol.toString()] ?: throw IllegalArgumentException("Unknown logic $symbol!")
    )
  }

  internal fun parseSetInfo(lexer: PeekableIterator<Token>, program: MutableSMTProgram) {
    val attribute = SMTParser.parseAttribute(lexer)

    program.setInfo(attribute)
  }

  @OptIn(ExperimentalContracts::class)
  internal fun parseDeclareSort(lexer: PeekableIterator<Token>, program: MutableSMTProgram) {
    val symbol = SMTParser.parseSymbol(lexer)

    val numeralToken = lexer.next()
    requireIsInstance<Numeral>(numeralToken)

    program.declareSort(symbol, numeralToken.number.toInt())
  }

  @OptIn(ExperimentalContracts::class)
  internal fun parseDefineSort(lexer: PeekableIterator<Token>, program: MutableSMTProgram) {
    val symbol = SMTParser.parseSymbol(lexer)

    // consume opening bracket
    requireIsInstance<OpeningBracket>(lexer.next())

    val typeParameter = star<ClosingBracket, Symbol>(lexer, SMTParser::parseSymbol)

    // consume closing bracket
    requireIsInstance<ClosingBracket>(lexer.next())

    val sort = SMTParser.parseSort(lexer, program)

    program.defineSort(symbol, typeParameter, sort)
  }

  @OptIn(ExperimentalContracts::class)
  internal fun parsePush(lexer: PeekableIterator<Token>, program: MutableSMTProgram) {
    val numeral = lexer.next()
    requireIsInstance<Numeral>(numeral)

    program.push(numeral.number.toInt())
  }

  @OptIn(ExperimentalContracts::class)
  internal fun parsePop(lexer: PeekableIterator<Token>, program: MutableSMTProgram) {
    val numeral = lexer.next()
    requireIsInstance<Numeral>(numeral)

    program.pop(numeral.number.toInt())
  }
}
