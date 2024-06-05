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
import org.petitparser.parser.primitive.CharacterParser.*
import org.petitparser.parser.primitive.StringParser.of
import org.petitparser.utils.FailureJoiner
import tools.aqua.konstraints.smt.*

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

  private val numeral = (of('0') + (range('1', '9') * digitCat.star())).flatten()
  private val decimal =
      (numeral * of('.') * of('0').star() * numeral).flatten().map<String, BigDecimal>(::BigDecimal)
  private val hexadecimal = of("#x") * (digitCat + range('A', 'F') + range('a', 'f')).plus()
  private val binary = (of("#b") * range('0', '1').plus()).flatten()
  // all printable characters that are not double quotes
  private val anythingButQuotes =
      whitespaceCat +
          range('\u0020', '"' - 1) +
          range('"' + 1, '\u007E') +
          range('\u0080', '\u00FF')
  internal val string =
      (of("\"") *
              (anythingButQuotes.star() +
                  ((anythingButQuotes.star() * of("\"\"") * anythingButQuotes.star()).star())) *
              of("\""))
          .flatten()

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
  private val keyword = (of(':') * simpleSymbol).flatten().trim(whitespaceCat).token()

  // Logics

  private val abv = of("ABV").map { _: Any -> ABV }
  private val abvfp = of("ABVFP").map { _: Any -> ABVFP }
  private val abvfplra = of("ABVFPLRA").map { _: Any -> ABVFPLRA }
  private val alia = of("ALIA").map { _: Any -> ALIA }
  private val ania = of("ANIA").map { _: Any -> ANIA }
  private val aufbv = of("AUFBV").map { _: Any -> AUFBV }
  private val aufbvdtlia = of("AUFBVDTLIA").map { _: Any -> AUFBVDTLIA }
  private val aufbvdtnia = of("AUFBVDTNIA").map { _: Any -> AUFBVDTNIA }
  private val aufbvdtnira = of("AUFBVDTNIRA").map { _: Any -> AUFBVDTNIRA }
  private val aufbvfp = of("AUFBVFP").map { _: Any -> AUFBVFP }
  private val aufdtlia = of("AUFDTLIA").map { _: Any -> AUFDTLIA }
  private val aufdtlira = of("AUFDTLIRA").map { _: Any -> AUFDTLIRA }
  private val aufdtnira = of("AUFDTNIRA").map { _: Any -> AUFDTNIRA }
  private val auffpdtnira = of("AUFFPDTNIRA").map { _: Any -> AUFFPDTNIRA }
  private val auflia = of("AUFLIA").map { _: Any -> AUFLIA }
  private val auflira = of("AUFLIRA").map { _: Any -> AUFLIRA }
  private val aufnia = of("AUFNIA").map { _: Any -> AUFNIA }
  private val aufnira = of("AUFNIRA").map { _: Any -> AUFNIRA }
  private val bv = of("BV").map { _: Any -> BV }
  private val bvfp = of("BVFP").map { _: Any -> BVFP }
  private val bvfplra = of("BVFPLRA").map { _: Any -> BVFPLRA }
  private val fp = of("FP").map { _: Any -> FP }
  private val fplra = of("FPLRA").map { _: Any -> FPLRA }
  private val lia = of("LIA").map { _: Any -> LIA }
  private val lra = of("LRA").map { _: Any -> LRA }
  private val nia = of("NIA").map { _: Any -> NIA }
  private val nra = of("NRA").map { _: Any -> NRA }
  private val qf_abv = of("QF_ABV").map { _: Any -> QF_ABV }
  private val qf_abvfp = of("QF_ABVFP").map { _: Any -> QF_ABVFP }
  private val qf_abvfplra = of("QF_ABVFPLRA").map { _: Any -> QF_ABVFPLRA }
  private val qf_alia = of("QF_ALIA").map { _: Any -> QF_ALIA }
  private val qf_ania = of("QF_ANIA").map { _: Any -> QF_ANIA }
  private val qf_aufbv = of("QF_AUFBV").map { _: Any -> QF_AUFBV }
  private val qf_aufbvfp = of("QF_AUFBVFP").map { _: Any -> QF_AUFBVFP }
  private val qf_auflia = of("QF_AUFLIA").map { _: Any -> QF_AUFLIA }
  private val qf_aufnia = of("QF_AUFNIA").map { _: Any -> QF_AUFNIA }
  private val qf_ax = of("QF_AX").map { _: Any -> QF_AX }
  private val qf_bv = of("QF_BV").map { _: Any -> QF_BV }
  private val qf_bvfp = of("QF_BVFP").map { _: Any -> QF_BVFP }
  private val qf_bvfplra = of("QF_BVFPLRA").map { _: Any -> QF_BVFPLRA }
  private val qf_dt = of("QF_DT").map { _: Any -> QF_DT }
  private val qf_fp = of("QF_FP").map { _: Any -> QF_FP }
  private val qf_fplra = of("QF_FPLRA").map { _: Any -> QF_FPLRA }
  private val qf_idl = of("QF_IDL").map { _: Any -> QF_IDL }
  private val qf_lia = of("QF_LIA").map { _: Any -> QF_LIA }
  private val qf_lira = of("QF_LIRA").map { _: Any -> QF_LIRA }
  private val qf_lra = of("QF_LRA").map { _: Any -> QF_LRA }
  private val qf_nia = of("QF_NIA").map { _: Any -> QF_NIA }
  private val qf_nira = of("QF_NIRA").map { _: Any -> QF_NIRA }
  private val qf_nra = of("QF_NRA").map { _: Any -> QF_NRA }
  private val qf_rdl = of("QF_RDL").map { _: Any -> QF_RDL }
  private val qf_s = of("QF_S").map { _: Any -> QF_S }
  private val qf_slia = of("QF_SLIA").map { _: Any -> QF_SLIA }
  private val qf_snia = of("QF_SNIA").map { _: Any -> QF_SNIA }
  private val qf_uf = of("QF_UF").map { _: Any -> QF_UF }
  private val qf_ufbv = of("QF_UFBV").map { _: Any -> QF_UFBV }
  private val qf_ufbvdt = of("QF_UFBVDT").map { _: Any -> QF_UFBVDT }
  private val qf_ufdt = of("QF_UFDT").map { _: Any -> QF_UFDT }
  private val qf_ufdtlia = of("QF_UFDTLIA").map { _: Any -> QF_UFDTLIA }
  private val qf_ufdtlira = of("QF_UFDTLIRA").map { _: Any -> QF_UFDTLIRA }
  private val qf_ufdtnia = of("QF_UFDTNIA").map { _: Any -> QF_UFDTNIA }
  private val qf_uffp = of("QF_UFFP").map { _: Any -> QF_UFFP }
  private val qf_uffpdtnira = of("QF_UFFPDTNIRA").map { _: Any -> QF_UFFPDTNIRA }
  private val qf_ufidl = of("QF_UFIDL").map { _: Any -> QF_UFIDL }
  private val qf_uflia = of("QF_UFLIA").map { _: Any -> QF_UFLIA }
  private val qf_uflra = of("QF_UFLRA").map { _: Any -> QF_UFLRA }
  private val qf_ufnia = of("QF_UFNIA").map { _: Any -> QF_UFNIA }
  private val qf_ufnra = of("QF_UFNRA").map { _: Any -> QF_UFNRA }
  private val uf = of("UF").map { _: Any -> UF }
  private val ufbv = of("UFBV").map { _: Any -> UFBV }
  private val ufbvdt = of("UFBVDT").map { _: Any -> UFBVDT }
  private val ufbvfp = of("UFBVFP").map { _: Any -> UFBVFP }
  private val ufbvlia = of("UFBVLIA").map { _: Any -> UFBVLIA }
  private val ufdt = of("UFDT").map { _: Any -> UFDT }
  private val ufdtlia = of("UFDTLIA").map { _: Any -> UFDTLIA }
  private val ufdtlira = of("UFDTLIRA").map { _: Any -> UFDTLIRA }
  private val ufdtnia = of("UFDTNIA").map { _: Any -> UFDTNIA }
  private val ufdtnira = of("UFDTNIRA").map { _: Any -> UFDTNIRA }
  private val uffpdtnira = of("UFFPDTNIRA").map { _: Any -> UFFPDTNIRA }
  private val ufidl = of("UFIDL").map { _: Any -> UFIDL }
  private val uflia = of("UFLIA").map { _: Any -> UFLIA }
  private val uflra = of("UFLRA").map { _: Any -> UFLRA }
  private val ufnia = of("UFNIA").map { _: Any -> UFNIA }
  private val ufnira = of("UFNIRA").map { _: Any -> UFNIRA }

  // logics must be in reverse alphabetical order so that e.g. QF_UFBV gets parsed before QF_UF
  // (plus works greedy)
  internal val logic =
      ufnira +
          ufnia +
          uflra +
          uflia +
          ufidl +
          uffpdtnira +
          ufdtnira +
          ufdtnia +
          ufdtlira +
          ufdtlia +
          ufdt +
          ufbvlia +
          ufbvfp +
          ufbvdt +
          ufbv +
          uf +
          qf_ufnra +
          qf_ufnia +
          qf_uflra +
          qf_uflia +
          qf_ufidl +
          qf_uffpdtnira +
          qf_uffp +
          qf_ufdtnia +
          qf_ufdtlira +
          qf_ufdtlia +
          qf_ufdt +
          qf_ufbvdt +
          qf_ufbv +
          qf_uf +
          qf_snia +
          qf_slia +
          qf_s +
          qf_rdl +
          qf_nra +
          qf_nira +
          qf_nia +
          qf_lra +
          qf_lira +
          qf_lia +
          qf_idl +
          qf_fplra +
          qf_fp +
          qf_dt +
          qf_bvfplra +
          qf_bvfp +
          qf_bv +
          qf_ax +
          qf_aufnia +
          qf_auflia +
          qf_aufbvfp +
          qf_aufbv +
          qf_ania +
          qf_alia +
          qf_abvfplra +
          qf_abvfp +
          qf_abv +
          nra +
          nia +
          lra +
          lia +
          fplra +
          fp +
          bvfplra +
          bvfp +
          bv +
          aufnira +
          aufnia +
          auflira +
          auflia +
          auffpdtnira +
          aufdtnira +
          aufdtlira +
          aufdtlia +
          aufbvfp +
          aufbvdtnira +
          aufbvdtnia +
          aufbvdtlia +
          aufbv +
          ania +
          alia +
          abvfplra +
          abvfp +
          abv

  // S-Expressions

  /* maps to an implementation of SpecConstant */
  private val specConstant =
      (decimal.map { decimal: BigDecimal -> DecimalConstant(decimal) } +
          numeral.map { numeral: String -> NumeralConstant(numeral) } +
          hexadecimal.map { hexadecimal: String -> HexConstant(hexadecimal) } +
          binary.map { binary: String -> BinaryConstant(binary) } +
          string.map { string: String -> StringConstant(string) }) trim whitespaceCat
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
      (numeral.map { numeral: String -> NumeralIndex(numeral.toInt()) } +
          symbol.map { symbol: ParseSymbol -> SymbolIndex(symbol.symbol) }) trim whitespaceCat

  /* maps to an implementation of Identifier */
  private val identifier =
      symbol.map { symbol: ParseSymbol -> SymbolIdentifier(symbol) } +
          (lparen * of("_") * symbol * index.plus() * rparen).map { results: List<Any> ->
            IndexedIdentifier(results[2] as ParseSymbol, results[3] as List<Index>)
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
        Attribute((results[0] as Token).getValue(), results[1] as AttributeValue)
      } + keyword.map { keyword: Token -> Attribute(keyword.getValue(), null) }

  // Terms

  internal val term = undefined()

  /* maps to an implementation of QualIdentifier */
  private val qualIdentifier =
      identifier.map { identifier: Identifier -> SimpleQualIdentifier(identifier) } +
          (lparen * asKW * identifier * sort * rparen).map { results: List<Any> ->
            AsQualIdentifier(results[2] as Identifier, results[3] as ProtoSort)
          }

  /* maps to VarBinding */
  internal val varBinding =
      (lparen * symbol * term * rparen).map { results: List<Any> ->
        ProtoVarBinding(results[1] as ParseSymbol, results[2] as ProtoTerm)
      }

  /* maps to SortedVar */
  private val sortedVar =
      (lparen * symbol * sort * rparen).map { results: List<Any> ->
        ProtoSortedVar(results[1] as ParseSymbol, results[2] as ProtoSort)
      }

  /* maps to pattern */
  private val pattern =
      symbol.map { symbol: ParseSymbol -> Pattern(listOf(symbol)) } +
          (lparen * symbol * symbol.plus() * rparen).map { results: List<Any> ->
            Pattern(
                listOf(listOf(results[1] as ParseSymbol), results[2] as List<ParseSymbol>)
                    .flatten())
            // results[2] is guaranteed to be a list of Symbol
          }

  /* maps to match case */
  private val matchCase =
      (lparen * pattern * term * rparen).map { results: List<Any> ->
        MatchCase(results[1] as Pattern, results[2] as ProtoTerm)
      }

  init {
    term.set(
        (lparen * letKW * lparen * varBinding.plus() * rparen * term * rparen).map {
            results: List<Any> ->
          ProtoLet(results[3] as List<ProtoVarBinding>, results[5] as ProtoTerm)
          // results[3] is guaranteed to be a list of VarBinding
        } + /* maps to ProtoLet */
            (lparen * forallKW * lparen * sortedVar.plus() * rparen * term * rparen).map {
                results: List<Any> ->
              ProtoForAll(results[3] as List<ProtoSortedVar>, results[5] as ProtoTerm)
              // results[3] is guaranteed to be a list of SortedVar
            } + /* maps to ProtoForAll */
            (lparen * existsKW * lparen * sortedVar.plus() * rparen * term * rparen).map {
                results: List<Any> ->
              ProtoExists(results[3] as List<ProtoSortedVar>, results[5] as ProtoTerm)
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
            } /* maps to ProtoExclamation */ +
            specConstant.map { constant: SpecConstant ->
              SpecConstantTerm(constant)
            } + /* maps to SpecConstantTerm */
            qualIdentifier /* Results is either SymbolTree or ProtoAs */ +
            (lparen * qualIdentifier * term.plus() * rparen).map { results: List<Any> ->
              /* Results contains QualIdentifier follow by list of ProtoTerm */
              BracketedProtoTerm(results[1] as QualIdentifier, results[2] as List<ProtoTerm>)
            } /* maps to GenericProtoTerm */)
  }

  // Theories
  // TODO

  // Logics
  // TODO

  // Info flags
  // TODO

  // Command options
  private val b_value = of("true").flatten() + of("false").flatten()

  private val diagnosticOutputChannelOption =
      (of(":diagnostic-output-channel") trim whitespaceCat).token()
  private val globalDeclarationsOption = (of(":global-declarations") trim whitespaceCat).token()
  private val interactiveModelOption = (of(":interactive-model") trim whitespaceCat).token()
  private val printSuccessOption = (of(":print-success") trim whitespaceCat).token()
  private val produceAssertionsOption = (of(":produce-assertions") trim whitespaceCat).token()
  private val produceAssignmentsOption = (of(":produce-assignments") trim whitespaceCat).token()
  private val produceModelsOption = (of(":produce-models") trim whitespaceCat).token()
  private val produceProofsOption = (of(":produce-proofs") trim whitespaceCat).token()
  private val produceUnsatAssumptionsOption =
      (of(":produce-unsat-assumptions") trim whitespaceCat).token()
  private val produceUnsatCoresOption = (of(":produce-unsat-cores") trim whitespaceCat).token()
  private val randomSeedOption = (of(":random-seed") trim whitespaceCat).token()
  private val regularOutputChannelOption =
      (of(":regular-output-channel") trim whitespaceCat).token()
  private val reproducibleResourceLimitOption =
      (of(":reproducible-resource-limit") trim whitespaceCat).token()
  private val verbosityOption = (of(":verbosity") trim whitespaceCat).token()
  private val option =
      ((globalDeclarationsOption * b_value) +
              (interactiveModelOption * b_value) +
              (printSuccessOption * b_value) +
              (produceAssertionsOption * b_value) +
              (produceAssignmentsOption * b_value) +
              (produceModelsOption * b_value) +
              (produceProofsOption * b_value) +
              (produceUnsatAssumptionsOption * b_value) +
              (produceUnsatCoresOption * b_value))
          .map { results: List<Any> ->
            listOf(results[0] as Token, BooleanOptionValue((results[1] as String).toBoolean()))
          } +
          ((diagnosticOutputChannelOption * string) + (regularOutputChannelOption * string)).map {
              results: List<Any> ->
            listOf(results[0] as Token, StringOptionValue(results[1] as String))
          } +
          /* use numeralBase here to have the number as string makes parsing later easier */
          ((randomSeedOption * numeral) +
                  (reproducibleResourceLimitOption * numeral) +
                  (verbosityOption * numeral))
              .map { results: List<Any> ->
                listOf(results[0] as Token, NumeralOptionValue(results[1] as Int))
              } +
          attribute.map { result: Attribute ->
            // set-option requires
            listOf(result.keyword, AttributeOptionValue(result))
          }

  // Commands
  private val sortDec = lparen * symbol * numeral * rparen
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
  private val functionDef =
      (symbol * lparen * sortedVar.star() * rparen * sort * term).map { result: ArrayList<Any> ->
        ProtoFunctionDef(
            result[0] as ParseSymbol,
            result.filterIsInstance<ProtoSortedVar>(),
            result[result.size - 2] as ProtoSort,
            result[result.size - 1] as ProtoTerm)
      }

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

  private val exitCMD = (lparen * exitKW * rparen).map { results: ArrayList<Any> -> Exit }

  private val setInfoCMD =
      (lparen * setInfoKW * attribute * rparen).map { results: ArrayList<Any> ->
        SetInfo(results[2] as Attribute)
      }

  private val setLogicCMD =
      (lparen * setLogicKW * logic * rparen).map { results: ArrayList<Any> ->
        ProtoSetLogic(results[2] as Logic)
      }

  private val setOptionCMD =
      (lparen * setOptionKW * option * rparen).map { results: ArrayList<Any> ->
        SetOption(
            (results[2] as List<Any>)[0] as String, (results[2] as List<Any>)[0] as OptionValue)
      }

  private val declareSortCMD =
      (lparen * declareSortKW * symbol * numeral * rparen).map { results: ArrayList<Any> ->
        ProtoDeclareSort(results[2] as ParseSymbol, (results[3] as String).toInt())
      }

  private val getModelCMD = (lparen * getModelKW * rparen).map { _: Any -> GetModel }

  private val defineFunCMD =
      (lparen * defineFunKW * functionDef * rparen).map { results: ArrayList<Any> ->
        ProtoDefineFun(results[2] as ProtoFunctionDef)
      }

  val command =
      ChoiceParser(
          FailureJoiner.SelectFarthest(),
          assertCMD,
          checkSatCMD,
          declareConstCMD,
          declareFunCMD,
          exitCMD,
          setInfoCMD,
          setLogicCMD,
          declareSortCMD,
          getModelCMD)

  val script = command.star().end()

  // TODO missing commands

  // Command responses
  // TODO

  fun parse(program: String): SMTProgram {
    val parseTreeVisitor = ParseTreeVisitor()

    // TODO parse each command individually, fail on the first command that can not be parsed
    // this will lead to better error messages but requires some preprocessing to split the input
    // input individual commands (this may be done in linear time by searching the input from
    // left to right counting the number of opening an closing brackets)
    val commands = splitInput(program)
    val protoCommands =
        commands.map {
          val temp = command.parse(it)

          if (temp.isSuccess) {
            temp
          } else {
            throw ParseException(temp.message, temp.position, temp.buffer)
          }
        }

    return DefaultSMTProgram(
        protoCommands
            .map { result -> result.get<Any>() }
            .map { command ->
              when (command) {
                is ProtoCommand -> parseTreeVisitor.visit(command)
                is Command -> command
                else -> throw IllegalStateException("Illegal type in parse tree $command!")
              }
            },
        parseTreeVisitor.context!!)
  }

  private fun splitInput(program: String): List<String> {
    val commands = mutableListOf<String>()
    var count = 0
    var position = 0

    program.forEachIndexed { index, c ->
      if (c == '(') {
        if (count == 0) {
          position = index
        }

        count++
      } else if (c == ')') {
        count--

        if (count == 0) {
          commands.add(program.substring(position, index + 1))
        }
      }
    }

    return commands
  }

  private fun preprocess(program: String): List<String> {
    val temp = preprocessingParser.parse(program)

    if (temp.isSuccess) {
      return temp.get()
    } else {
      throw ParseException(temp.message, temp.position, temp.buffer)
    }
  }

  val commandSplitter = undefined()
  val preprocessingParser = commandSplitter.star()

  init {
    commandSplitter.set(
        ((specConstant.map { constant: SpecConstant -> constant.toString() } +
            reserved.map { reserved: Token -> reserved.getValue<Any>() } +
            symbol.map { symbol: ParseSymbol -> symbol.toString() } +
            keyword.map { keyword: Token -> keyword }) trim whitespaceCat) +
            ((lparen * commandSplitter.star() * rparen).map { results: List<Any> ->
              print(results)
            } trim whitespaceCat))
  }
}

class ParseException(message: String, position: Int, buffer: String) :
    RuntimeException(
        "Parser failed with message $message at position $position: ${buffer.substring(position)}")
