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

  private val whitespaceCat = anyOf(" \t\r\n", "space, tab, or newline expected")
  private val printableCat = range('\u0020', '\u007E') + range('\u0080', '\u00FF')
  private val digitCat = range('0', '9')
  private val letterCat = range('A', 'Z') + range('a', 'z')

  // Tokens: Reserved Words: General

  private val exclamationKW = of('!') trim whitespaceCat
  private val underscoreKW = of('_') trim whitespaceCat
  private val asKW = of("as") trim whitespaceCat
  private val binaryKW = of("BINARY") trim whitespaceCat
  private val decimalKW = of("DECIMAL") trim whitespaceCat
  private val existsKW = of("exists") trim whitespaceCat
  private val hexadecimalKW = of("HEXADECIMAL") trim whitespaceCat
  private val forallKW = of("forall") trim whitespaceCat
  private val letKW = of("let") trim whitespaceCat
  private val matchKW = of("match") trim whitespaceCat
  private val numeralKW = of("NUMERAL") trim whitespaceCat
  private val parKW = of("par") trim whitespaceCat
  private val stringKW = of("STRING") trim whitespaceCat

  internal val reservedGeneral =
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

  private val assertKW = of("assert") trim whitespaceCat
  private val checkSatKW = of("check-sat") trim whitespaceCat
  private val checkSatAssumingKW = of("check-sat-assuming") trim whitespaceCat
  private val declareConstKW = of("declare-const") trim whitespaceCat
  private val declareDatatypeKW = of("declare-datatype") trim whitespaceCat
  private val declareDatatypesKW = of("declare-datatypes") trim whitespaceCat
  private val declareFunKW = of("declare-fun") trim whitespaceCat
  private val declareSortKW = of("declare-sort") trim whitespaceCat
  private val defineFunKW = of("define-fun") trim whitespaceCat
  private val defineFunRecKW = of("define-fun-rec") trim whitespaceCat
  private val defineSortKW = of("define-sort") trim whitespaceCat
  private val echoKW = of("echo") trim whitespaceCat
  private val exitKW = of("exit") trim whitespaceCat
  private val getAssertionsKW = of("get-assertions") trim whitespaceCat
  private val getAssignmentKW = of("get-assignment") trim whitespaceCat
  private val getInfoKW = of("get-info") trim whitespaceCat
  private val getModelKW = of("get-model") trim whitespaceCat
  private val getOptionKW = of("get-option") trim whitespaceCat
  private val getProofKW = of("get-proof") trim whitespaceCat
  private val getUnsatAssumptionsKW = of("get-unsat-assumptions") trim whitespaceCat
  private val getUnsatCoreKW = of("get-unsat-core") trim whitespaceCat
  private val getValueKW = of("get-value") trim whitespaceCat
  private val popKW = of("pop") trim whitespaceCat
  private val pushKW = of("push") trim whitespaceCat
  private val resetKW = of("reset") trim whitespaceCat
  private val resetAssertionsKW = of("reset-assertions") trim whitespaceCat
  private val setInfoKW = of("set-info") trim whitespaceCat
  private val setLogicKW = of("set-logic") trim whitespaceCat
  private val setOptionKW = of("set-option") trim whitespaceCat

  internal val reservedCommands =
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

  private val lparen = of('(') trim whitespaceCat
  private val rparen = of(')') trim whitespaceCat

  private val numeralBase = (of('0') + (range('1', '9') * digitCat.star())).flatten()
  private val numeral = numeralBase.map(String::toInt)
  private val decimal =
      (numeralBase * of('.') * of('0').star() * numeralBase)
          .flatten()
          .map<String, BigDecimal>(::BigDecimal)
  private val hexadecimal = of("#x") * (digitCat + range('A', 'F') + range('a', 'f')).plus()
  private val binary = (of("#b") * range('0', '1').plus()).flatten()
  private val anythingButQuotes =
      whitespaceCat +
          range('\u0020', '"' - 1) +
          range('"' + 1, '\u007E') +
          range('\u0080', '\u00FF')
  private val string =
      of("\"") *
          (anythingButQuotes.star() +
              ((anythingButQuotes.star() * of("\"\"") * anythingButQuotes.star()).star())) *
          of("\"")

  private val symbolSymbols = anyOf("+-/*=%?!.\$_~&^<>@")
  internal val simpleSymbol =
      (letterCat + symbolSymbols) * (letterCat + digitCat + anyOf("+-/*=%?!.\$_~&^<>@")).star()

  private val anythingButPipeOrBackslash =
      whitespaceCat +
          range('\u0020', '\\' - 1) +
          range('\\' + 1, '|' - 1) +
          range('|' + 1, '\u007E') +
          range('\u0080', '\u00FF')
  internal val quotedSymbol = of('|') * anythingButPipeOrBackslash.star() * of('|')

  private val symbol =
      (simpleSymbol + quotedSymbol).flatten().trim(whitespaceCat).token().map { token: Token ->
        ParseSymbol(token)
      }
  private val keyword = (of(':') * simpleSymbol).trim(whitespaceCat).flatten().token()

  // S-Expressions

  /* maps to an implementation of SpecConstant */
  private val specConstant =
      decimal.map { decimal: BigDecimal -> DecimalConstant(decimal) } +
          numeral.map { numeral: Int -> NumeralConstant(numeral) } +
          hexadecimal.map { hexadecimal: String -> HexConstant(hexadecimal) } +
          binary.map { binary: String -> BinaryConstant(binary) } +
          string.map { string: String -> StringConstant(string) }
  private val sExpression = undefined()
  internal val reserved = reservedCommands + reservedGeneral

  init {
    /* maps to an implementation of SExpression */
    sExpression.set(
        ((specConstant.map { constant: SpecConstant -> SExpressionConstant(constant) } +
            reserved.map { reserved: Token -> SExpressionReserved(reserved) } +
            symbol.map { symbol: ParseSymbol -> SExpressionSymbol(symbol) } +
            keyword.map { keyword: Token -> SExpressionKeyword(keyword) }) trim whitespaceCat) +
            ((lparen * sExpression.star() * rparen).map { results: List<Any> ->
              SubSExpression(results.slice(1..results.size - 2) as List<SExpression>)
              // results is guaranteed to be a list of SExpression except the first and last entry
            } trim whitespaceCat))
  }

  // Identifiers

  /* maps to an implementation of Index */
  private val index =
      numeral.map { numeral: Int -> NumeralParseIndex(numeral) } +
          symbol.map { symbol: ParseSymbol -> SymbolParseIndex(symbol) }

  /* maps to an implementation of Identifier */
  private val identifier =
      symbol.map { symbol: ParseSymbol -> SymbolIdentifier(symbol) } +
          (lparen * of("_") * symbol * index.plus() * rparen).map { results: List<Any> ->
            IndexedIdentifier(results[2] as ParseSymbol, results[3] as List<ParseIndex>)
            // results[3] is guaranteed to be a list of Index
          }

  // Sorts

  internal val sort = undefined()

  init {
    /* maps to ProtoSort */
    sort.set(
        identifier.map { identifier: Identifier -> ProtoSort(identifier, listOf()) } +
            (lparen * identifier * sort.plus() * rparen).map { results: List<Any> ->
              ProtoSort(results[1] as Identifier, results[2] as List<ProtoSort>)
              // results[2] is guaranteed to be a none empty List of ProtoSort
            })
  }

  // Attributes

  /* maps to an implementation of AttributeValue */
  private val attributeValue =
      specConstant.map { constant: SpecConstant -> ConstantAttributeValue(constant) } +
          symbol.map { symbol: ParseSymbol -> SymbolAttributeValue(symbol) } +
          (lparen * sExpression.star() * rparen).map { results: List<Any> ->
            SExpressionAttributeValue(results.slice(1..results.size - 2) as List<SExpression>)
          }

  /*
   * maps to Attribute
   * ChoiceParser matches greedy, so it's important to first match (keyword * attributeValue)
   * Maybe replace with (keyword * attributeValue.optional())
   */
  internal val attribute =
      (keyword * attributeValue).map { results: List<Any> ->
        Attribute(results[0] as Token, results[1] as AttributeValue)
      } + keyword.map { keyword: Token -> Attribute(keyword, null) }

  // Terms

  private val term = undefined()

  /* maps to an implementation of QualIdentifier */
  private val qualIdentifier =
      identifier.map { identifier: Identifier -> SimpleQualIdentifier(identifier) } +
          (lparen * asKW * identifier * sort * rparen).map { results: List<Any> ->
            AsQualIdentifier(results[2] as Identifier, results[3] as ProtoSort)
          }

  /* maps to VarBinding */
  private val varBinding =
      (lparen * symbol * term * rparen).map { results: List<Any> ->
        VarBinding(results[1] as ParseSymbol, results[2] as ProtoTerm)
      }

  /* maps to SortedVar */
  private val sortedVar =
      (lparen * symbol * sort * rparen).map { results: List<Any> ->
        SortedVar(results[1] as ParseSymbol, results[2] as ProtoSort)
      }

  /* maps to pattern */
  private val pattern =
      symbol.map { symbol: ParseSymbol -> Pattern(listOf(symbol)) } +
          (lparen * symbol * symbol.plus() * rparen).map { results: List<Any> ->
            Pattern(listOf(listOf(results[1] as ParseSymbol), results[2] as List<ParseSymbol>).flatten())
            // results[2] is guaranteed to be a list of Symbol
          }

  /* maps to match case */
  private val matchCase =
      (lparen * pattern * term * rparen).map { results: List<Any> ->
        MatchCase(results[1] as Pattern, results[2] as ProtoTerm)
      }

  init {
    term.set(
        specConstant.map { constant: SpecConstant ->
          SpecConstantTerm(constant)
        } + /* maps to SpecConstantTerm */
            qualIdentifier /* Results is either SymbolTree or ProtoAs */ +
            (lparen * qualIdentifier * term.plus() * rparen).map { results: List<Any> ->
              /* Results contains QualIdentifier follow by list of ProtoTerm */
              BracketedProtoTerm(results[1] as QualIdentifier, results[2] as List<ProtoTerm>)
            } + /* maps to GenericProtoTerm */
            (lparen * letKW * lparen * varBinding.plus() * rparen * term * rparen).map {
                results: List<Any> ->
              ProtoLet(results[3] as List<VarBinding>, results[5] as ProtoTerm)
              // results[3] is guaranteed to be a list of VarBinding
            } + /* maps to ProtoLet */
            (lparen * forallKW * lparen * sortedVar.plus() * rparen * term * rparen).map {
                results: List<Any> ->
              ProtoForAll(results[3] as List<SortedVar>, results[5] as ProtoTerm)
              // results[3] is guaranteed to be a list of SortedVar
            } + /* maps to ProtoForAll */
            (lparen * existsKW * lparen * sortedVar.plus() * rparen * term * rparen).map {
                results: List<Any> ->
              ProtoExists(results[3] as List<SortedVar>, results[5] as ProtoTerm)
              // results[3] is guaranteed to be a list of SortedVar
            } + /* maps to ProtoExists */
            (lparen * matchKW * term * lparen * matchCase.plus() * rparen * rparen).map {
                results: List<Any> ->
              ProtoMatch(results[2] as ProtoTerm, results[3] as List<MatchCase>)
              // results[3] is guaranteed to be a list of MatchCase
            } + /* maps to ProtoMatch */
            (lparen * exclamationKW * term * attribute.plus() * rparen).map { results: List<Any> ->
              ProtoAnnotation(results[2] as ProtoTerm, results[3] as List<Attribute>)
              // results[3] is guaranteed to be a list of Attributes
            } /* maps to ProtoExclamation */)
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
  private val sortDec = lparen * symbol * numeralBase * rparen
  private val selectorDec = lparen * symbol * sort * rparen
  private val constructorDec = lparen * symbol * selectorDec.star() * rparen
  private val datatypeDec =
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
  private val functionDec = lparen * symbol * lparen * sortedVar.star() * rparen * sort * rparen
  private val functionDef = symbol * lparen * sortedVar.star() * rparen * sort * term

  /*
   * The spec lists "not" as reserved here, but it is not reserved in any other context
   */
  private val propLiteral = symbol + (lparen * of("not") * symbol * rparen)

  private val assertCMD =
      (lparen * assertKW * term * rparen).map { results: List<Any> ->
        ProtoAssert(results[2] as ProtoTerm)
      }

  private val checkSatCMD = (lparen * checkSatKW * rparen).map { _: Any -> CheckSat }

  private val declareConstCMD =
      (lparen * declareConstKW * symbol * sort * rparen).map { results: ArrayList<Any> ->
        ProtoDeclareConst(results[2] as ParseSymbol, results[3] as ProtoSort)
      }

  private val declareFunCMD =
      (lparen * declareFunKW * symbol * lparen * sort.star() * rparen * sort * rparen).map {
          results: ArrayList<Any> ->
        ProtoDeclareFun(
            results[2] as ParseSymbol, results[4] as List<ProtoSort>, results[6] as ProtoSort)
        // results[4] is guaranteed to be a List of ProtoSort
      }

  val command = assertCMD + checkSatCMD + declareConstCMD + declareFunCMD
  val script = command.star()

  // TODO missing commands

  // Command responses
  // TODO
}
