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
import org.petitparser.utils.FailureJoiner
import tools.aqua.konstraints.*

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
  private val keyword = (of(':') * simpleSymbol).trim(whitespaceCat).flatten().token()

  // Logics

  private val auflia = of("AUFLIA").map { _: Any -> Logic.AUFLIA }
  private val auflira = of("AUFLIRA").map { _: Any -> Logic.AUFLIRA }
  private val aufnira = of("AUFNIRA").map { _: Any -> Logic.AUFNIRA }
  private val lia = of("LIA").map { _: Any -> Logic.LIA }
  private val lra = of("LRA").map { _: Any -> Logic.LRA }
  private val qf_abv = of("QF_ABV").map { _: Any -> Logic.QF_ABV }
  private val qf_aufbv = of("QF_AUFBV").map { _: Any -> Logic.QF_AUFBV }
  private val qf_auflia = of("QF_AUFLIA").map { _: Any -> Logic.QF_AUFLIA }
  private val qf_ax = of("QF_AX").map { _: Any -> Logic.QF_AX }
  private val qf_bv = of("QF_BV").map { _: Any -> Logic.QF_BV }
  private val qf_idl = of("QF_IDL").map { _: Any -> Logic.QF_IDL }
  private val qf_lia = of("QF_LIA").map { _: Any -> Logic.QF_LIA }
  private val qf_lra = of("QF_LRA").map { _: Any -> Logic.QF_LRA }
  private val qf_nia = of("QF_NIA").map { _: Any -> Logic.QF_NIA }
  private val qf_nra = of("QF_NRA").map { _: Any -> Logic.QF_NRA }
  private val qf_rdl = of("QF_RDL").map { _: Any -> Logic.QF_RDL }
  private val qf_uf = of("QF_UF").map { _: Any -> Logic.QF_UF }
  private val qf_ufbv = of("QF_UFBV").map { _: Any -> Logic.QF_UFBV }
  private val qf_ufidl = of("QF_UFIDL").map { _: Any -> Logic.QF_UFIDL }
  private val qf_uflia = of("QF_UFLIA").map { _: Any -> Logic.QF_UFLIA }
  private val qf_uflra = of("QF_UFLRA").map { _: Any -> Logic.QF_UFLRA }
  private val qf_ufnra = of("QF_UFNRA").map { _: Any -> Logic.QF_UFNRA }
  private val uflra = of("UFLRA").map { _: Any -> Logic.UFLRA }
  private val ufnia = of("UFNIA").map { _: Any -> Logic.UFNIA }

  internal val logic =
      auflia +
          auflira +
          aufnira +
          lia +
          lra +
          qf_abv +
          qf_aufbv +
          qf_auflia +
          qf_ax +
          qf_bv +
          qf_idl +
          qf_lia +
          qf_lra +
          qf_nia +
          qf_nra +
          qf_rdl +
          qf_ufbv +
          qf_ufidl +
          qf_uflia +
          qf_uflra +
          qf_ufnra +
          uflra +
          ufnia +
          qf_uf

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
            symbol.map { symbol: ParseSymbol -> SExpressionSymbol(symbol.toSymbol()) } +
            keyword.map { keyword: Token -> SExpressionKeyword(keyword) }) trim whitespaceCat) +
            ((lparen * sExpression.star() * rparen).map { results: List<Any> ->
              SubSExpression(results.slice(1..results.size - 2) as List<SExpression>)
              // results is guaranteed to be a list of SExpression except the first and last entry
            } trim whitespaceCat))
  }

  // Identifiers

  /* maps to an implementation of Index */
  private val index =
      (numeral.map { numeral: Int -> NumeralParseIndex(numeral) } +
          symbol.map { symbol: ParseSymbol -> SymbolParseIndex(symbol) }) trim whitespaceCat

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
          symbol.map { symbol: ParseSymbol -> SymbolAttributeValue(symbol.toSymbol()) } +
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

  private val exitCMD = (lparen * exitKW * rparen).map { results: ArrayList<Any> -> Exit }
  private val setInfoCMD =
      (lparen * setInfoKW * attribute * rparen).map { results: ArrayList<Any> ->
        SetInfo(results[2] as Attribute)
      }
  private val setLogicCMD =
      (lparen * setLogicKW * logic * rparen).map { results: ArrayList<Any> ->
        SetLogic(results[2] as Logic)
      }
  private val setOptionCMD =
      (lparen * setOptionKW * option * rparen).map { results: ArrayList<Any> ->
        SetOption(
            (results[2] as List<Any>)[0] as String, (results[2] as List<Any>)[0] as OptionValue)
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
          setLogicCMD)

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
    val protoCommands = script.parse(program)

    if (protoCommands.isSuccess) {
      val commands =
          (protoCommands.get<List<Any>>()).map { command ->
            when (command) {
              is ProtoCommand -> parseTreeVisitor.visit(command)
              is Command -> command
              else -> throw IllegalStateException("Illegal type in parse tree $command!")
            }
          }

      return SMTProgram(commands)
    } else {
      throw ParseException(protoCommands.message, protoCommands.position)
    }
  }
}

class ParseException(message: String, position: Int) :
    RuntimeException("Parser failed with message $message at position $position!")
