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

package tools.aqua.konstraints.parser.lexer

import java.math.BigDecimal
import java.math.BigInteger
import tools.aqua.konstraints.parser.location.AbstractLocalizable
import tools.aqua.konstraints.parser.location.SourceSpan

sealed class Token(source: SourceSpan) : AbstractLocalizable(source)

class EOFToken(source: SourceSpan) : Token(source)

sealed class SemanticToken(source: SourceSpan) : Token(source)

sealed class ReservedWord(val word: String, source: SourceSpan) : SemanticToken(source) {
  override fun toString(): String = word
}

sealed class GeneralReservedWord(word: String, source: SourceSpan) : ReservedWord(word, source)

sealed class CommandName(word: String, source: SourceSpan) : ReservedWord(word, source)

private const val EXCLAMATION = "!"

class ExclamationWord(source: SourceSpan) : GeneralReservedWord(EXCLAMATION, source)

private const val UNDERSCORE = "_"

class UnderscoreWord(source: SourceSpan) : GeneralReservedWord(UNDERSCORE, source)

private const val AS = "as"

class AsWord(source: SourceSpan) : GeneralReservedWord(AS, source)

private const val BINARY = "BINARY"

class BinaryWord(source: SourceSpan) : GeneralReservedWord(BINARY, source)

private const val DECIMAL = "DECIMAL"

class DecimalWord(source: SourceSpan) : GeneralReservedWord(DECIMAL, source)

private const val EXISTS = "exists"

class ExistsWord(source: SourceSpan) : GeneralReservedWord(EXISTS, source)

private const val HEXADECIMAL = "HEXADECIMAL"

class HexadecimalWord(source: SourceSpan) : GeneralReservedWord(HEXADECIMAL, source)

private const val FORALL = "forall"

class ForallWord(source: SourceSpan) : GeneralReservedWord(FORALL, source)

private const val LAMBDA = "lambda"

class LambdaWord(source: SourceSpan) : GeneralReservedWord(LAMBDA, source)

private const val LET = "let"

class LetWord(source: SourceSpan) : GeneralReservedWord(LET, source)

private const val MATCH = "match"

class MatchWord(source: SourceSpan) : GeneralReservedWord(MATCH, source)

private const val NUMERAL = "NUMERAL"

class NumeralWord(source: SourceSpan) : GeneralReservedWord(NUMERAL, source)

private const val PAR = "par"

class ParWord(source: SourceSpan) : GeneralReservedWord(PAR, source)

private const val STRING = "STRING"

class StringWord(source: SourceSpan) : GeneralReservedWord(STRING, source)

private const val ASSERT = "assert"

class AssertWord(source: SourceSpan) : CommandName(ASSERT, source)

private const val CHECK_SAT = "check-sat"

class CheckSatWord(source: SourceSpan) : CommandName(CHECK_SAT, source)

private const val CHECK_SAT_ASSUMING = "check-sat-assuming"

class CheckSatAssumingWord(source: SourceSpan) : CommandName(CHECK_SAT_ASSUMING, source)

private const val DECLARE_CONST = "declare-const"

class DeclareConstWord(source: SourceSpan) : CommandName(DECLARE_CONST, source)

private const val DECLARE_DATATYPE = "declare-datatype"

class DeclareDatatypeWord(source: SourceSpan) : CommandName(DECLARE_DATATYPE, source)

private const val DECLARE_DATATYPES = "declare-datatypes"

class DeclareDatatypesWord(source: SourceSpan) : CommandName(DECLARE_DATATYPES, source)

private const val DECLARE_FUN = "declare-fun"

class DeclareFunWord(source: SourceSpan) : CommandName(DECLARE_FUN, source)

private const val DECLARE_SORT = "declare-sort"

class DeclareSortWord(source: SourceSpan) : CommandName(DECLARE_SORT, source)

private const val DECLARE_SORT_PARAMETER = "declare-sort-parameter"

class DeclareSortParameterWord(source: SourceSpan) : CommandName(DECLARE_SORT_PARAMETER, source)

private const val DEFINE_CONST = "define-const"

class DefineConstWord(source: SourceSpan) : CommandName(DEFINE_CONST, source)

private const val DEFINE_FUN = "define-fun"

class DefineFunWord(source: SourceSpan) : CommandName(DEFINE_FUN, source)

private const val DEFINE_FUN_REC = "define-fun-rec"

class DefineFunRecWord(source: SourceSpan) : CommandName(DEFINE_FUN_REC, source)

private const val DEFINE_SORT = "define-sort"

class DefineSortWord(source: SourceSpan) : CommandName(DEFINE_SORT, source)

private const val ECHO = "echo"

class EchoWord(source: SourceSpan) : CommandName(ECHO, source)

private const val EXIT = "exit"

class ExitWord(source: SourceSpan) : CommandName(EXIT, source)

private const val GET_ASSERTIONS = "get-assertions"

class GetAssertionsWord(source: SourceSpan) : CommandName(GET_ASSERTIONS, source)

private const val GET_ASSIGNMENT = "get-assignment"

class GetAssignmentWord(source: SourceSpan) : CommandName(GET_ASSIGNMENT, source)

private const val GET_INFO = "get-info"

class GetInfoWord(source: SourceSpan) : CommandName(GET_INFO, source)

private const val GET_MODEL = "get-model"

class GetModelWord(source: SourceSpan) : CommandName(GET_MODEL, source)

private const val GET_OPTION = "get-option"

class GetOptionWord(source: SourceSpan) : CommandName(GET_OPTION, source)

private const val GET_PROOF = "get-proof"

class GetProofWord(source: SourceSpan) : CommandName(GET_PROOF, source)

private const val GET_UNSAT_ASSUMPTIONS = "get-unsat-assumptions"

class GetUnsatAssumptionsWord(source: SourceSpan) : CommandName(GET_UNSAT_ASSUMPTIONS, source)

private const val GET_UNSAT_CORE = "get-unsat-core"

class GetUnsatCoreWord(source: SourceSpan) : CommandName(GET_UNSAT_CORE, source)

private const val GET_VALUE = "get-value"

class GetValueWord(source: SourceSpan) : CommandName(GET_VALUE, source)

private const val POP = "pop"

class PopWord(source: SourceSpan) : CommandName(POP, source)

private const val PUSH = "push"

class PushWord(source: SourceSpan) : CommandName(PUSH, source)

private const val RESET = "reset"

class ResetWord(source: SourceSpan) : CommandName(RESET, source)

private const val RESET_ASSERTIONS = "reset-assertions"

class ResetAssertionsWord(source: SourceSpan) : CommandName(RESET_ASSERTIONS, source)

private const val SET_INFO = "set-info"

class SetInfoWord(source: SourceSpan) : CommandName(SET_INFO, source)

private const val SET_LOGIC = "set-logic"

class SetLogicWord(source: SourceSpan) : CommandName(SET_LOGIC, source)

private const val SET_OPTION = "set-option"

class SetOptionWord(source: SourceSpan) : CommandName(SET_OPTION, source)

internal val reservedWords =
    mapOf(
        EXCLAMATION to ::ExclamationWord,
        UNDERSCORE to ::UnderscoreWord,
        AS to ::AsWord,
        BINARY to ::BinaryWord,
        DECIMAL to ::DecimalWord,
        EXISTS to ::ExistsWord,
        HEXADECIMAL to ::HexadecimalWord,
        FORALL to ::ForallWord,
        /* LAMBDA to ::LambdaWord, */
        // since we implement smt 2.6 and not 2.7 yet lambda is not a reserved word
        LET to ::LetWord,
        MATCH to ::MatchWord,
        NUMERAL to ::NumeralWord,
        PAR to ::ParWord,
        STRING to ::StringWord,
        ASSERT to ::AssertWord,
        CHECK_SAT to ::CheckSatWord,
        CHECK_SAT_ASSUMING to ::CheckSatAssumingWord,
        DECLARE_CONST to ::DeclareConstWord,
        DECLARE_DATATYPE to ::DeclareDatatypeWord,
        DECLARE_DATATYPES to ::DeclareDatatypesWord,
        DECLARE_FUN to ::DeclareFunWord,
        DECLARE_SORT to ::DeclareSortWord,
        DECLARE_SORT_PARAMETER to ::DeclareSortParameterWord,
        DEFINE_CONST to ::DefineConstWord,
        DEFINE_FUN to ::DefineFunWord,
        DEFINE_FUN_REC to ::DefineFunRecWord,
        DEFINE_SORT to ::DefineSortWord,
        ECHO to ::EchoWord,
        EXIT to ::ExitWord,
        GET_ASSERTIONS to ::GetAssertionsWord,
        GET_ASSIGNMENT to ::GetAssignmentWord,
        GET_INFO to ::GetInfoWord,
        GET_MODEL to ::GetModelWord,
        GET_OPTION to ::GetOptionWord,
        GET_PROOF to ::GetProofWord,
        GET_UNSAT_ASSUMPTIONS to ::GetUnsatAssumptionsWord,
        GET_UNSAT_CORE to ::GetUnsatCoreWord,
        GET_VALUE to ::GetValueWord,
        POP to ::PopWord,
        PUSH to ::PushWord,
        RESET to ::ResetWord,
        RESET_ASSERTIONS to ::ResetAssertionsWord,
        SET_INFO to ::SetInfoWord,
        SET_LOGIC to ::SetLogicWord,
        SET_OPTION to ::SetOptionWord,
    )

sealed class WhitespaceLike(source: SourceSpan) : Token(source)

class Whitespace(val contents: String, source: SourceSpan) : WhitespaceLike(source) {
  init {
    require(contents.all(Char::isSMTWhiteSpace)) {
      "all characters in $contents must be SMT whitespace"
    }
  }

  override fun toString(): String = contents
}

class Comment(val contents: String, source: SourceSpan) : WhitespaceLike(source) {
  init {
    require(contents.all(Char::isNotSMTLineBreak)) {
      "characters in $contents must not be SMT line breaks"
    }
  }

  override fun toString(): String = ";$contents"
}

class OpeningBracket(source: SourceSpan) : SemanticToken(source) {
  override fun toString(): String = "("
}

class ClosingBracket(source: SourceSpan) : SemanticToken(source) {
  override fun toString(): String = ")"
}

sealed class SpecConstantToken(source: SourceSpan) : SemanticToken(source)

sealed class IntegerSpecConstantToken(val number: BigInteger, source: SourceSpan) :
    SpecConstantToken(source) {
  init {
    require(number.signum() >= 0) { "SMT constant cannot be negative" }
  }
}

class Numeral(number: BigInteger, source: SourceSpan) : IntegerSpecConstantToken(number, source) {
  override fun toString(): String = number.toString()
}

class Decimal(val number: BigDecimal, source: SourceSpan) : SpecConstantToken(source) {
  init {
    require(number.signum() >= 0) { "SMT constant cannot be negative" }
  }

  override fun toString(): String = number.toPlainString()
}

// number is stored as string to not drop leading zeros which leads to incorrect bit width in
// vectors
class Hexadecimal(val number: String, source: SourceSpan) : SpecConstantToken(source) {
  override fun toString() = "#x$number"
}

class Binary(val number: String, source: SourceSpan) : SpecConstantToken(source) {
  override fun toString() = "#b$number"
}

class SMTString(val contents: String, source: SourceSpan) : SpecConstantToken(source) {
  init {
    require(contents.all(Char::isStringLetter)) {
      "all characters in $contents must be SMT string letters"
    }
  }

  override fun toString(): String = "\"${contents}\""
}

sealed class SymbolToken(source: SourceSpan) : SemanticToken(source)

class SimpleSymbolToken(val contents: String, source: SourceSpan) : SymbolToken(source) {
  init {
    require(contents.first().isNotDigit) { "$contents must not start with a digit" }
    require(contents.all(Char::isSimpleSymbolLetter)) {
      "all characters in $contents must be SMT simple symbol letters"
    }
    require(contents !in reservedWords) { "$contents must not be reserved" }
  }

  override fun toString(): String = contents
}

class QuotedSymbolToken(val contents: String, source: SourceSpan) : SymbolToken(source) {
  init {
    require(contents.all(Char::isQuotedSymbolLetter)) {
      "all characters in $contents must be SMT quoted symbol letters"
    }
    // quoted simples should be allowed to use reserved words as content
    // require(contents !in reservedWords) { "$contents must not be reserved" }
  }

  override fun toString(): String = "|$contents|"
}

class KeywordToken(val contents: String, source: SourceSpan) : SemanticToken(source) {
  init {
    require(contents.first().isNotDigit) { "$contents must not start with a digit" }
    require(contents.all(Char::isSimpleSymbolLetter)) {
      "all characters in $contents must be SMT simple symbol letters"
    }
    require(contents !in reservedWords) { "$contents must not be reserved" }
  }

  override fun toString(): String = ":$contents"
}
