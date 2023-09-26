/*
 * SPDX-License-Identifier: Apache-2.0
 *
 * Copyright 2023-2023 The Konstraints Authors
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
import org.petitparser.context.Token
import org.petitparser.parser.Parser
import org.petitparser.parser.combinators.ChoiceParser
import org.petitparser.parser.combinators.SequenceParser
import org.petitparser.parser.combinators.SettableParser.undefined
import org.petitparser.parser.primitive.CharacterParser.anyOf
import org.petitparser.parser.primitive.CharacterParser.of
import org.petitparser.parser.primitive.CharacterParser.range
import org.petitparser.parser.primitive.StringParser.of
import tools.aqua.konstraints.CheckSat

operator fun Parser.plus(other: Parser): ChoiceParser = or(other)

operator fun Parser.times(other: Parser): SequenceParser = seq(other)

infix fun Parser.trim(both: Parser): Parser = trim(both)

object Parser {
  // Auxiliary Lexical Categories

  val whitespaceCat = anyOf(" \t\r\n", "space, tab, or newline expected")
  val printableCat = range('\u0020', '\u007E') + range('\u0080', '\u00FF')
  val digitCat = range('0', '9')
  val letterCat = range('A', 'Z') + range('a', 'z')

  // Tokens: Reserved Words: General

  val exclamationKW = of('!') trim whitespaceCat
  val underscoreKW = of('_') trim whitespaceCat
  val asKW = of("as") trim whitespaceCat
  val binaryKW = of("BINARY") trim whitespaceCat
  val decimalKW = of("DECIMAL") trim whitespaceCat
  val existsKW = of("exists") trim whitespaceCat
  val hexadecimalKW = of("HEXADECIMAL") trim whitespaceCat
  val forallKW = of("forall") trim whitespaceCat
  val letKW = of("let") trim whitespaceCat
  val matchKW = of("match") trim whitespaceCat
  val numeralKW = of("NUMERAL") trim whitespaceCat
  val parKW = of("par") trim whitespaceCat
  val stringKW = of("STRING") trim whitespaceCat

  val reservedGeneral =
      (exclamationKW +
              underscoreKW +
              asKW +
              binaryKW +
              decimalKW +
              existsKW +
              hexadecimalKW +
              forallKW +
              letKW +
              matchKW +
              numeralKW +
              parKW +
              stringKW)
          .token()

  // Tokens: Reserved Words: Command names

  val assertKW = of("assert") trim whitespaceCat
  val checkSatKW = of("check-sat") trim whitespaceCat
  val checkSatAssumingKW = of("check-sat-assuming") trim whitespaceCat
  val declareConstKW = of("declare-const") trim whitespaceCat
  val declareDatatypeKW = of("declare-datatype") trim whitespaceCat
  val declareDatatypesKW = of("declare-datatypes") trim whitespaceCat
  val declareFunKW = of("declare-fun") trim whitespaceCat
  val declareSortKW = of("declare-sort") trim whitespaceCat
  val defineFunKW = of("define-fun") trim whitespaceCat
  val defineFunRecKW = of("define-fun-rec") trim whitespaceCat
  val defineSortKW = of("define-sort") trim whitespaceCat
  val echoKW = of("echo") trim whitespaceCat
  val exitKW = of("exit") trim whitespaceCat
  val getAssertionsKW = of("get-assertions") trim whitespaceCat
  val getAssignmentKW = of("get-assignment") trim whitespaceCat
  val getInfoKW = of("get-info") trim whitespaceCat
  val getModelKW = of("get-model") trim whitespaceCat
  val getOptionKW = of("get-option") trim whitespaceCat
  val getProofKW = of("get-proof") trim whitespaceCat
  val getUnsatAssumptionsKW = of("get-unsat-assumptions") trim whitespaceCat
  val getUnsatCoreKW = of("get-unsat-core") trim whitespaceCat
  val getValueKW = of("get-value") trim whitespaceCat
  val popKW = of("pop") trim whitespaceCat
  val pushKW = of("push") trim whitespaceCat
  val resetKW = of("reset") trim whitespaceCat
  val resetAssertionsKW = of("reset-assertions") trim whitespaceCat
  val setInfoKW = of("set-info") trim whitespaceCat
  val setLogicKW = of("set-logic") trim whitespaceCat
  val setOptionKW = of("set-option") trim whitespaceCat

  val reservedCommands =
      (assertKW +
              checkSatKW +
              checkSatAssumingKW +
              declareConstKW +
              declareDatatypeKW +
              declareDatatypesKW +
              declareFunKW +
              declareSortKW +
              defineFunKW +
              defineFunRecKW +
              defineSortKW +
              echoKW +
              exitKW +
              getAssertionsKW +
              getAssignmentKW +
              getInfoKW +
              getModelKW +
              getOptionKW +
              getProofKW +
              getUnsatAssumptionsKW +
              getUnsatCoreKW +
              getValueKW +
              popKW +
              pushKW +
              resetKW +
              resetAssertionsKW +
              setInfoKW +
              setLogicKW +
              setOptionKW)
          .token()

  // Tokens: Other tokens

  val lparen = of('(') trim whitespaceCat
  val rparen = of(')') trim whitespaceCat

  val numeralBase = (of('0') + (range('1', '9') * digitCat.plus())).flatten()
  val numeral = numeralBase.map(String::toInt)
  val decimal =
      (numeralBase * of('.') * of('0').star() * numeralBase)
          .flatten()
          .map<String, BigDecimal>(::BigDecimal)
  val hexadecimal = of("#x") * (digitCat + range('A', 'F') + range('a', 'f')).plus()
  val binary = (of("#b") * range('0', '1').plus()).flatten()
  val anythingButQuotes =
      whitespaceCat +
          range('\u0020', '"' - 1) +
          range('"' + 1, '\u007E') +
          range('\u0080', '\u00FF')
  val string =
      of("\"") *
          (anythingButQuotes.star() +
              ((anythingButQuotes.star() * of("\"\"") * anythingButQuotes.star()).star())) *
          of("\"")

  val symbolSymbols = anyOf("+-/*=%?!.\$_~&^<>@")
  val simpleSymbol =
      (letterCat + symbolSymbols) * (letterCat + digitCat + anyOf("+-/*=%?!.\$_~&^<>@")).star()

  val anythingButPipeOrBackslash =
      whitespaceCat +
          range('\u0020', '\\' - 1) +
          range('\\' + 1, '|' - 1) +
          range('|' + 1, '\u007E') +
          range('\u0080', '\u00FF')
  val quotedSymbol = of('|') * anythingButPipeOrBackslash.star() * of('|')

  val symbol =
      (simpleSymbol + quotedSymbol).trim(whitespaceCat).flatten().token().map { token: Token ->
        Symbol(token)
      }
  val keyword = (of(':') * simpleSymbol).flatten().token()

  // S-Expressions

  val specConstant = (numeralBase + decimal + hexadecimal + binary + string).token()
  val sExpression = undefined()
  val reserved = reservedCommands + reservedGeneral

  init {
    sExpression.set(
        ((specConstant + reserved + symbol + keyword) trim whitespaceCat) +
            ((lparen * sExpression.star() * rparen).pick(1) trim whitespaceCat))
    /*
      pick(1) only returns the second result (here the result of sExpression.star()) to filter out
      the lparen/rparen matches that are no longer needed for further parsing
    */
  }

  // Identifiers

  val index = numeralBase + symbol
  val identifier =
      symbol +
          (lparen * symbol * index.plus() * rparen).map { results: List<Any> ->
            val temp = mutableListOf<Any>()
            temp.add(results[1])
            temp.addAll(results[2] as List<Any>)
            temp.toList()
          }

  // Sorts

  val sort = undefined()

  init {
    sort.set(
        identifier.token().map { token: Token -> ProtoSort(token, listOf()) } +
            (lparen * identifier.token() * sort.plus() * rparen).map { results: List<Any> ->
              ProtoSort(results[1] as Token, results[2] as List<Any>)
            })
  }

  // Attributes
  val attributeValue = specConstant + symbol + (lparen * sExpression.star() * rparen)
  val attribute = keyword + (keyword * attributeValue)

  // Terms

  val term = undefined()
  val qualIdentifier = identifier + (lparen * asKW * identifier * sort * rparen)
  val varBinding = lparen * symbol * term * rparen
  val sortedVar = lparen * symbol * sort * rparen
  val pattern = symbol + (lparen * symbol * symbol.plus() * rparen)
  val matchCase = lparen * pattern * term * rparen

  init {
    term.set(
        specConstant +
            qualIdentifier.trim(whitespaceCat) +
            (lparen *
                qualIdentifier.trim(whitespaceCat) *
                term.plus() *
                rparen) /*+
                        (lparen * letKW * lparen * varBinding.plus() * rparen * term * rparen) +
                        (lparen * forallKW * lparen * sortedVar.plus() * rparen * term * rparen) +
                        (lparen * existsKW * lparen * sortedVar.plus() * rparen * term * rparen) +
                        (lparen * matchKW * term * lparen * matchCase.plus() * rparen * rparen) +
                        (lparen * exclamationKW * term * attribute.plus() * rparen)*/) // map to prototerm (token?)
  }

  // Theories
  // TODO

  // Logics
  // TODO

  // Info flags
  // TODO

  // Command options
  // TODO

  // Commands
  val sortDec = lparen * symbol * numeralBase * rparen
  val selectorDec = lparen * symbol * sort * rparen
  val constructorDec = lparen * symbol * selectorDec.star() * rparen
  val datatypeDec =
      (lparen * constructorDec.plus() * rparen) +
          (lparen *
              parKW *
              lparen *
              symbol.plus() *
              rparen *
              lparen *
              constructorDec.plus() *
              rparen *
              rparen)
  val functionDec = lparen * symbol * lparen * sortedVar.star() * rparen * sort * rparen
  val functionDef = symbol * lparen * sortedVar.star() * rparen * sort * term
  val propLiteral = undefined() /*symbol + (lparen * notKW * symbol * rparen)*/

  val assertCMD = lparen * assertKW * term * rparen

  val checkSatCMD = (lparen * checkSatKW * rparen).map { _: Any -> CheckSat }

  val declareConstCMD =
      (lparen * declareConstKW * symbol * sort * rparen).map { results: ArrayList<Any> ->
        ProtoDeclareConst(results[2] as Symbol, results[3] as ProtoSort)
      }

  val declareFunCMD =
      (lparen * declareFunKW * symbol * lparen * sort.star() * rparen * sort * rparen).map {
          results: ArrayList<Any> ->
        ProtoDeclareFun(
            results[2] as Symbol, results[4] as List<ProtoSort>, results[6] as ProtoSort)
      }

  val command = assertCMD + checkSatCMD + declareConstCMD + declareFunCMD
  val script = command.star()

  // TODO missing commands

  // Command responses
  // TODO
}
