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

@SuppressWarnings("UNCHECKED_CAST")
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

  val numeralBase = (of('0') + (range('1', '9') * digitCat.star())).flatten()
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
      (simpleSymbol + quotedSymbol).flatten().trim(whitespaceCat).token().map { token: Token ->
        Symbol(token)
      }
  val keyword = (of(':') * simpleSymbol).trim(whitespaceCat).flatten().token()

  // S-Expressions

  /* maps to an implementation of SpecConstant */
  val specConstant =
      decimal.map { decimal: BigDecimal -> DecimalConstant(decimal) } +
          numeral.map { numeral: Int -> NumeralConstant(numeral) } +
          hexadecimal.map { hexadecimal: String -> HexConstant(hexadecimal) } +
          binary.map { binary: String -> BinaryConstant(binary) } +
          string.map { string: String -> StringConstant(string) }
  val sExpression = undefined()
  val reserved = reservedCommands + reservedGeneral

  init {
    /* maps to an implementation of SExpression */
    sExpression.set(
        ((specConstant.map { constant: SpecConstant -> SExpressionConstant(constant) } +
            reserved.map { reserved: Token -> SExpressionReserved(reserved) } +
            symbol.map { symbol: Symbol -> SExpressionSymbol(symbol) } +
            keyword.map { keyword: Token -> SExpressionKeyword(keyword) }) trim whitespaceCat) +
            ((lparen * sExpression.star() * rparen).map { results: List<Any> ->
              SubSExpression(results.slice(1..results.size - 2) as List<SExpression>)
              // results is guaranteed to be a list of SExpression except the first and last entry
            } trim whitespaceCat))
  }

  // Identifiers

  /* maps to an implementation of Index */
  val index =
      numeral.map { numeral: Int -> NumeralIndex(numeral) } +
          symbol.map { symbol: Symbol -> SymbolIndex(symbol) }

  /* maps to an implementation of Identifier */
  val identifier =
      symbol.map { symbol: Symbol -> SymbolIdentifier(symbol) } +
          (lparen * of("_") * symbol * index.plus() * rparen).map { results: List<Any> ->
            IndexedIdentifier(results[2] as Symbol, results[3] as List<Index>)
            // results[3] is guaranteed to be a list of Index
          }

  // Sorts

  val sort = undefined()

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
  val attributeValue =
      specConstant.map { constant: SpecConstant -> ConstantAttributeValue(constant) } +
          symbol.map { symbol: Symbol -> SymbolAttributeValue(symbol) } +
          (lparen * sExpression.star() * rparen).map { results: List<Any> ->
            SExpressionAttributeValue(results.slice(1..results.size - 2) as List<SExpression>)
          }

  /*
   * maps to Attribute
   * ChoiceParser matches greedy, so it's important to first match (keyword * attributeValue)
   * Maybe replace with (keyword * attributeValue.optional())
   */
  val attribute =
      (keyword * attributeValue).map { results: List<Any> ->
        Attribute(results[0] as Token, results[1] as AttributeValue)
      } + keyword.map { keyword: Token -> Attribute(keyword, null) }

  // Terms

  val term = undefined()

  /* maps to an implementation of QualIdentifier */
  val qualIdentifier =
      identifier.map { identifier: Identifier -> SimpleQualIdentifier(identifier) } +
          (lparen * asKW * identifier * sort * rparen).map { results: List<Any> ->
            AsQualIdentifier(results[2] as Identifier, results[3] as ProtoSort)
          }

  /* maps to VarBinding */
  val varBinding =
      (lparen * symbol * term * rparen).map { results: List<Any> ->
        VarBinding(results[1] as Symbol, results[2] as ProtoTerm)
      }

  /* maps to SortedVar */
  val sortedVar =
      (lparen * symbol * sort * rparen).map { results: List<Any> ->
        SortedVar(results[1] as Symbol, results[2] as ProtoSort)
      }

  /* maps to pattern */
  val pattern =
      symbol.map { symbol: Symbol -> Pattern(listOf(symbol)) } +
          (lparen * symbol * symbol.plus() * rparen).map { results: List<Any> ->
            Pattern(listOf(listOf(results[1] as Symbol), results[2] as List<Symbol>).flatten())
            // results[2] is guaranteed to be a list of Symbol
          }

  /* maps to match case */
  val matchCase =
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
  val propLiteral = symbol /*+ (lparen * notKW * symbol * rparen)*/

  val assertCMD =
      (lparen * assertKW * term * rparen).map { results: List<Any> ->
        ProtoAssert(results[2] as ProtoTerm)
      }

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
        // results[4] is guaranteed to be a List of ProtoSort
      }

  val command = assertCMD + checkSatCMD + declareConstCMD + declareFunCMD
  val script = command.star()

  // TODO missing commands

  // Command responses
  // TODO
}
