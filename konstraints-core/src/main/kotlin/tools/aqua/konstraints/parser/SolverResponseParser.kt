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
import tools.aqua.konstraints.parser.lexer.ClosingBracket
import tools.aqua.konstraints.parser.lexer.DefineFunWord
import tools.aqua.konstraints.parser.lexer.ErrorToken
import tools.aqua.konstraints.parser.lexer.OpeningBracket
import tools.aqua.konstraints.parser.lexer.SMTStringToken
import tools.aqua.konstraints.parser.lexer.SMTTokenizer
import tools.aqua.konstraints.parser.lexer.SatToken
import tools.aqua.konstraints.parser.lexer.SuccessToken
import tools.aqua.konstraints.parser.lexer.Token
import tools.aqua.konstraints.parser.lexer.UnknownToken
import tools.aqua.konstraints.parser.lexer.UnsatToken
import tools.aqua.konstraints.parser.lexer.UnsupportedToken
import tools.aqua.konstraints.parser.util.PeekableIterator
import tools.aqua.konstraints.parser.util.peekable
import tools.aqua.konstraints.smt.FunctionDef
import tools.aqua.konstraints.smt.Model
import tools.aqua.konstraints.smt.SMTProgram
import tools.aqua.konstraints.smt.SatStatus
import tools.aqua.konstraints.solvers.UnexpectedSolverResponseException

object ResponseParser {
  fun parseGeneralResponse(reader: Reader): SolverResponse {
    val lexer = SMTTokenizer(reader, true).peekable()
    return parseGeneralResponseOrNull(lexer) ?: throw UnexpectedSolverResponseException("")
  }

  /**
   * Parse a general response (success, unsupported or (error <string>)) or return null if none of
   * these match. If no match is found, no tokens will be consumed.
   */
  @OptIn(ExperimentalContracts::class)
  internal fun parseGeneralResponseOrNull(lexer: PeekableIterator<Token>): SolverResponse? {
    when (val token = lexer.peek()) {
      is SuccessToken -> {
        lexer.consume()
        return SuccessResponse
      }
      is UnsupportedToken -> {
        lexer.consume()
        return UnsupportedResponse
      }
      is OpeningBracket -> {
        // important to not consume the token before we are sure that we have an error response
        if (lexer.peek(1) is ErrorToken) {
          // consume both the opening bracket and the error token
          lexer.consume(2)

          val content = lexer.next()
          requireIsInstance<SMTStringToken>(content)
          requireIsInstance<ClosingBracket>(lexer.next())

          return ErrorResponse(content.contents)
        }

        return null
      }
      else -> return null
    }
  }

  fun parseCheckSatResponse(reader: Reader): SolverResponse {
    val lexer = SMTTokenizer(reader, true).peekable()
    parseGeneralResponseOrNull(lexer)?.let {
      return it
    }

    return when (val token = lexer.next()) {
      is SatToken -> CheckSatResponse(SatStatus.SAT)
      is UnknownToken -> CheckSatResponse(SatStatus.UNKNOWN)
      is UnsatToken -> CheckSatResponse(SatStatus.UNSAT)
      else ->
          throw UnexpectedTokenException(
              token,
              "Expected any of sat, unsat or unknown",
          )
    }
  }

  fun parseEchoResponse(reader: Reader): SolverResponse {
    val lexer = SMTTokenizer(reader, true).peekable()
    parseGeneralResponseOrNull(lexer)?.let {
      return it
    }

    return when (val token = lexer.next()) {
      is SMTStringToken -> EchoResponse(token.contents)
      else ->
          throw UnexpectedTokenException(
              token,
              "Expected SMTStringToken but got $token at ${token.source}",
          )
    }
  }

  @OptIn(ExperimentalContracts::class)
  fun parseModelResponse(reader: Reader, program: SMTProgram): SolverResponse {
    val lexer = SMTTokenizer(reader, true).peekable()
    parseGeneralResponseOrNull(lexer)?.let {
      return it
    }

    requireIsInstance<OpeningBracket>(lexer.next())

    val model =
        GetModelResponse(
            Model(
                star<ClosingBracket, SMTProgram, FunctionDef<*>>(
                    lexer,
                    program,
                ) { lexer, program ->
                  requireIsInstance<OpeningBracket>(lexer.next())
                  requireIsInstance<DefineFunWord>(lexer.next())
                  val def = SMTScriptParser.parseFuncDef(lexer, program)
                  requireIsInstance<ClosingBracket>(lexer.next())

                  def
                }
            )
        )

    requireIsInstance<ClosingBracket>(lexer.next())

    return model
  }
}
