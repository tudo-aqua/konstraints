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
import java.math.BigInteger
import org.petitparser.context.Token
import org.petitparser.parser.Parser
import org.petitparser.parser.combinators.ChoiceParser
import org.petitparser.parser.combinators.SequenceParser
import org.petitparser.parser.combinators.SettableParser.undefined
import org.petitparser.parser.primitive.CharacterParser.*
import org.petitparser.parser.primitive.StringParser.of
import org.petitparser.utils.FailureJoiner
import tools.aqua.konstraints.smt.*
import tools.aqua.konstraints.smt.BVLiteral
import tools.aqua.konstraints.smt.BVSort
import tools.aqua.konstraints.smt.IntLiteral
import tools.aqua.konstraints.smt.RealLiteral
import tools.aqua.konstraints.smt.Theories

operator fun Parser.plus(other: Parser): ChoiceParser = or(other)

operator fun Parser.times(other: Parser): SequenceParser = seq(other)

infix fun Parser.trim(both: Parser): Parser = trim(both)

class Parser {
  val program = MutableSMTProgram()

  companion object {
    private val whitespaceCat = anyOf(" \t\r\n", "space, tab, or newline expected")
    private val printableCat = range('\u0020', '\u007E') + range('\u0080', '\u00FF')
    private val digitCat = range('0', '9')
    private val letterCat = range('A', 'Z') + range('a', 'z')

    // Tokens: Reserved Words: General

    private val exclamationKW = of('!') trim whitespaceCat
    private val underscoreKW = of('_') trim whitespaceCat
    // .end() parser is important here to avoid issues when symbols start with 'as'
    private val asKW = (of("as") trim whitespaceCat).end()
    private val binaryKW = of("BINARY") trim whitespaceCat
    private val decimalKW = of("DECIMAL") trim whitespaceCat
    private val existsKW = of("exists") trim whitespaceCat
    private val hexadecimalKW = of("HEXADECIMAL") trim whitespaceCat
    private val forallKW = of("forall") trim whitespaceCat
    private val letKW = (of("let") trim whitespaceCat)
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
    private val decimal = (numeral * of('.') * numeral.plus()).flatten()
    private val hexadecimal =
        (of("#x") * (digitCat + range('A', 'F') + range('a', 'f')).plus()).flatten()
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
        (decimal.map { decimal: String -> DecimalConstant(decimal.toBigDecimal()) } +
            numeral.map { numeral: String -> NumeralConstant(numeral.toBigInteger()) } +
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
    /*
     * important to parse indexed identifier as "(_ " (note the space) or otherwise names that begin
     * with _ do get truncated
     */
    private val identifier =
        symbol.map { symbol: ParseSymbol -> SymbolIdentifier(symbol) } +
            (lparen * of("_ ") * symbol * index.plus() * rparen).map { results: List<Any> ->
              IndexedIdentifier(results[2] as ParseSymbol, results[3] as List<Index>)
              // results[3] is guaranteed to be a list of Index
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

    /* maps to pattern */
    private val pattern =
        symbol.map { symbol: ParseSymbol -> Pattern(listOf(symbol)) } +
            (lparen * symbol * symbol.plus() * rparen).map { results: List<Any> ->
              Pattern(
                  listOf(listOf(results[1] as ParseSymbol), results[2] as List<ParseSymbol>)
                      .flatten())
              // results[2] is guaranteed to be a list of Symbol
            }

    // Command options
    private val b_value = of("true").flatten() + of("false").flatten()

    private val diagnosticOutputChannelOption =
        (of(":diagnostic-output-channel") trim whitespaceCat).flatten()
    private val globalDeclarationsOption = (of(":global-declarations") trim whitespaceCat).flatten()
    private val interactiveModelOption = (of(":interactive-model") trim whitespaceCat).flatten()
    private val printSuccessOption = (of(":print-success") trim whitespaceCat).flatten()
    private val produceAssertionsOption = (of(":produce-assertions") trim whitespaceCat).flatten()
    private val produceAssignmentsOption = (of(":produce-assignments") trim whitespaceCat).flatten()
    private val produceModelsOption = (of(":produce-models") trim whitespaceCat).flatten()
    private val produceProofsOption = (of(":produce-proofs") trim whitespaceCat).flatten()
    private val produceUnsatAssumptionsOption =
        (of(":produce-unsat-assumptions") trim whitespaceCat).flatten()
    private val produceUnsatCoresOption = (of(":produce-unsat-cores") trim whitespaceCat).flatten()
    private val randomSeedOption = (of(":random-seed") trim whitespaceCat).flatten()
    private val regularOutputChannelOption =
        (of(":regular-output-channel") trim whitespaceCat).flatten()
    private val reproducibleResourceLimitOption =
        (of(":reproducible-resource-limit") trim whitespaceCat).flatten()
    private val verbosityOption = (of(":verbosity") trim whitespaceCat).flatten()
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
            ((diagnosticOutputChannelOption * string) + (regularOutputChannelOption * string))
                .map { results: List<Any> ->
                  listOf(results[0] as Token, StringOptionValue(results[1] as String))
                } +
            /* use numeralBase here to have the number as string makes parsing later easier */
            ((randomSeedOption * numeral) +
                    (reproducibleResourceLimitOption * numeral) +
                    (verbosityOption * numeral))
                .map { results: List<Any> ->
                  listOf(results[0] as Token, NumeralOptionValue(results[1] as BigInteger))
                } +
            attribute.map { result: Attribute ->
              // set-option requires
              listOf(result.keyword, AttributeOptionValue(result))
            }

    // Commands
    private val sortDec = lparen * symbol * numeral * rparen

    /*
     * The spec lists "not" as reserved here, but it is not reserved in any other context
     */
    private val propLiteral = symbol + (lparen * of("not") * symbol * rparen)
  }

  internal val sort = undefined()

  init {
    /* maps to ProtoSort */
    sort.set(
        identifier.map { identifier: Identifier ->
          // check if sort is in the current context
          require(program.context.containsSort(identifier.symbol)) {
            "Unexpected sort symbol ${identifier.symbol}"
          }
          when (identifier) {
            is IndexedIdentifier ->
                program.context
                    .getSort(identifier.symbol)
                    .build(emptyList(), identifier.indices as List<NumeralIndex>)

            is SymbolIdentifier ->
                program.context.getSort(identifier.symbol).build(emptyList(), emptyList())
          }
        } +
            (lparen * identifier * sort.plus() * rparen).map { results: List<Any> ->
              val identifier = results[1] as Identifier
              val sorts = results[2] as List<Sort>

              require(program.context.containsSort(identifier.symbol))
              when (identifier) {
                is IndexedIdentifier ->
                    program.context
                        .getSort(identifier.symbol)
                        .build(sorts, identifier.indices as List<NumeralIndex>)

                is SymbolIdentifier ->
                    program.context.getSort(identifier.symbol).build(sorts, emptyList())
              }
            })
  }

  // Terms

  internal val term = undefined()

  /* maps to an instance of SMTFunction and a list of indices */
  private val qualIdentifier =
      identifier.map { identifier: Identifier ->
        if (identifier.symbol.value.startsWith("bv") &&
            identifier.symbol.value.substring(2).all { ch -> ch.isDigit() }) {
          require(program.context.containsSort("BitVec".toSymbolAsIs()))

          listOf(
              /*
               * On the fly construction of BVLiteral factory as such an object does not exist since literals are no
               * SMT functions
               */
              object : SMTFunction<BVSort>() {
                override val symbol = identifier.symbol
                override val sort =
                    BVSort(((identifier as IndexedIdentifier).indices[0] as NumeralIndex).numeral)
                override val parameters = emptyList<Sort>()

                override fun constructDynamic(
                    args: List<Expression<*>>,
                    indices: List<Index>
                ): Expression<BVSort> {
                  require(args.isEmpty())
                  require(indices.size == 1)

                  return BVLiteral(
                      "#b${identifier.symbol.value.substring(2).toBigInteger().toString(2)}",
                      sort.bits)
                }
              },
              identifier.indices)
        } else {
          when (identifier) {
            is SymbolIdentifier ->
                listOf(program.context.getFunc(identifier.symbol), emptyList<Index>())

            is IndexedIdentifier ->
                listOf(program.context.getFunc(identifier.symbol), identifier.indices)
          }
        }
      } +
          (lparen * asKW * identifier * sort * rparen).map { results: List<Any> ->
            TODO("Implement As")
          }

  /* maps to VarBinding */
  internal val varBinding =
      (lparen * symbol * term * rparen).map { results: List<Any> ->
        VarBinding(results[1] as Symbol, results[2] as Expression<*>)
      }

  /* maps to SortedVar */
  private val sortedVar =
      (lparen * symbol * sort * rparen).map { results: List<Any> ->
        SortedVar(results[1] as Symbol, results[2] as Sort)
      }

  /* maps to match case */
  private val matchCase =
      (lparen * pattern * term * rparen).map { results: List<Any> ->
        TODO("Match case not implemented yet!")
      }

  init {
    term.set(
        (lparen *
                letKW *
                lparen *
                varBinding.plus().map { bindings: List<VarBinding<*>> ->
                  21
                  // bind variables in the context
                  program.context.bindVariables(bindings)
                  // return bindings to they can be added to LetExpression and unbound later
                  bindings
                } *
                rparen *
                term *
                rparen)
            .map { results: List<Any> ->
              program.context.unbindVariables()
              LetExpression(results[3] as List<VarBinding<*>>, results[5] as Expression<*>)
              // results[3] is guaranteed to be a list of VarBinding
            } + /* maps to LetExpression */
            (lparen *
                    forallKW *
                    lparen *
                    sortedVar.plus().map { bindings: List<SortedVar<*>> ->
                      // bind variables in the context
                      program.context.bindVariables(bindings)
                      // return bindings to they can be added to LetExpression and unbound later
                      bindings
                    } *
                    rparen *
                    term *
                    rparen)
                .map { results: List<Any> ->
                  program.context.unbindVariables()
                  ForallExpression(
                      results[3] as List<SortedVar<*>>, (results[5] as Expression<*>).cast())
                  // results[3] is guaranteed to be a list of SortedVar
                } + /* maps to ForallExpression */
            (lparen *
                    existsKW *
                    lparen *
                    sortedVar.plus().map { bindings: List<SortedVar<*>> ->
                      // bind variables in the context
                      program.context.bindVariables(bindings)
                      // return bindings to they can be added to LetExpression and unbound later
                      bindings
                    } *
                    rparen *
                    term *
                    rparen)
                .map { results: List<Any> ->
                  program.context.unbindVariables()
                  ExistsExpression(
                      results[3] as List<SortedVar<*>>, (results[5] as Expression<*>).cast())
                  // results[3] is guaranteed to be a list of SortedVar
                } + /* maps to ExistsExpression */
            (lparen * matchKW * term * lparen * matchCase.plus() * rparen * rparen).map {
                results: List<Any> ->
              TODO("Match not implemented yet!")
              // results[3] is guaranteed to be a list of MatchCase
            } + /* maps to ProtoMatch */
            (lparen * exclamationKW * term * attribute.plus() * rparen).map { results: List<Any> ->
              AnnotatedExpression(results[2] as Expression<*>, results[3] as List<Attribute>)
              // results[3] is guaranteed to be a list of Attributes
            } /* maps to AnnotatedExpression */ +
            specConstant.map { constant: SpecConstant ->
              when (constant) {
                is BinaryConstant -> BVLiteral(constant.binary)
                is DecimalConstant -> RealLiteral(constant.decimal)
                is HexConstant -> BVLiteral(constant.hexadecimal)
                is NumeralConstant ->
                    if (Theories.INTS in program.logic!!.theories ||
                        Theories.REALS_INTS in program.logic!!.theories) IntLiteral(constant.numeral)
                    else if (Theories.REALS in program.logic!!.theories)
                        RealLiteral(BigDecimal(constant.numeral))
                    else throw RuntimeException("Unsupported numeral literal!")

                is StringConstant -> TODO("String constant not implemented yet!")
              }
            } + /* maps to Literal */
            qualIdentifier.map { results: List<Any> ->
              /* Results is an SMTFunction without any parameters */
              (results[0] as SMTFunction<*>).constructDynamic(
                  emptyList(), results[1] as List<Index>)
            } /* maps to Expression */ +
            (lparen * qualIdentifier * term.plus() * rparen).map { results: List<Any> ->
              /* Results contains list of SMTFunction and indices follow by list of its arguments as Expressions */
              val function = (results[1] as List<Any>)[0] as SMTFunction<*>
              val indices = (results[1] as List<Any>)[1] as List<Index>

              function.constructDynamic(results[2] as List<Expression<*>>, indices)
            } /* maps to Expression */)
  }

  private val selectorDec = lparen * symbol * sort * rparen
  private val functionDec = lparen * symbol * lparen * sortedVar.star() * rparen * sort * rparen
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
  private val functionDef =
      (symbol *
              lparen *
              sortedVar.star().map { bindings: List<SortedVar<*>> ->
                // set special locals field where context stores locally used sorted vars
                // to construct defined expression
                program.context.locals = bindings
                bindings
              } *
              rparen *
              sort *
              term)
          .map { result: ArrayList<Any> ->
            // clear locals
            program.context.locals = emptyList()
            FunctionDef(
                result[0] as ParseSymbol,
                result[2] as List<SortedVar<*>>,
                result[4] as Sort,
                result[5] as Expression<*>)
          }

  private val assertCMD =
      (lparen * assertKW * term * rparen).map { results: List<Any> ->
        program.assert((results[2] as Expression<*>).cast())
      }

  private val checkSatCMD = (lparen * checkSatKW * rparen).map { _: Any -> program.add(CheckSat) }

  private val declareConstCMD =
      (lparen * declareConstKW * symbol * sort * rparen).map { results: ArrayList<Any> ->
        program.declareConst(results[2] as ParseSymbol, results[3] as Sort)
      }

  private val declareFunCMD =
      (lparen * declareFunKW * symbol * lparen * sort.star() * rparen * sort * rparen).map {
          results: ArrayList<Any> ->
        program.declareFun(results[2] as ParseSymbol, results[4] as List<Sort>, results[6] as Sort)
        // results[4] is guaranteed to be a List of Sort
      }

  private val exitCMD = (lparen * exitKW * rparen).map { results: ArrayList<Any> -> Exit }

  private val setInfoCMD =
      (lparen * setInfoKW * attribute * rparen).map { results: ArrayList<Any> ->
        program.setInfo(SetInfo(results[2] as Attribute))
      }

  private val setLogicCMD =
      (lparen * setLogicKW * logic * rparen).map { results: ArrayList<Any> ->
        program.setLogic(results[2] as Logic)
      }

  private val setOptionCMD =
      (lparen * setOptionKW * option * rparen).map { results: ArrayList<Any> ->
        program.setOption(
            SetOption(
                (results[2] as List<Any>)[0] as String,
                (results[2] as List<Any>)[1] as OptionValue))
      }

  private val declareSortCMD =
      (lparen * declareSortKW * symbol * numeral * rparen).map { results: ArrayList<Any> ->
        program.declareSort(results[2] as Symbol, Integer.parseInt(results[3] as String))
      }

  private val defineSortCMD =
      (lparen *
              defineSortKW *
              symbol *
              lparen *
              symbol.star().map { t: List<Symbol> ->
                program.context.addSortParameters(t)
                t
              } *
              rparen *
              sort *
              rparen)
          .map { results: ArrayList<Any> ->
            program.defineSort(results[2] as Symbol, results[4] as List<Symbol>, results[6] as Sort)
            program.context.clearSortParameters()
          }

  private val getModelCMD = (lparen * getModelKW * rparen).map { _: Any -> program.add(GetModel) }

  private val defineFunCMD =
      (lparen * defineFunKW * functionDef * rparen).map { results: ArrayList<Any> ->
        program.defineFun(results[2] as FunctionDef<*>)
      }

  private val pushCMD =
      (lparen * pushKW * numeral * rparen).map { results: ArrayList<Any> ->
        program.push((results[2] as String).toInt())
      }

  private val popCMD =
      (lparen * popKW * numeral * rparen).map { results: ArrayList<Any> ->
        program.pop((results[2] as String).toInt())
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
          defineSortCMD,
          getModelCMD,
          defineFunCMD,
          setOptionCMD,
          pushCMD,
          popCMD)

  internal val script = command.star().end()

  /**
   * Parses an SMTProgram in string format IMPORTANT linebreak characters ('\n') must be present in
   * the string representation to correctly filter out comments in the smt code
   */
  fun parse(program: String): SMTProgram {
    // TODO parse each command individually, fail on the first command that can not be parsed
    // this will lead to better error messages but requires some preprocessing to split the input
    // into individual commands (this may be done in linear time by searching the input from
    // left to right counting the number of opening an closing brackets)
    // filter out all comments (all lines are truncated after ';')
    splitInput(program.split("\n").joinToString(" ") { line -> line.substringBefore(';') })
        .forEach { cmd ->
          val temp = command.parse(cmd)
          if (!temp.isSuccess) {
            throw ParseException(temp.message, temp.position, temp.buffer)
          }
        }

    return this.program
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
}

class ParseException(message: String, position: Int, buffer: String) :
    RuntimeException(
        "Parser failed with message $message at position $position: ${buffer.substring(position)}")
