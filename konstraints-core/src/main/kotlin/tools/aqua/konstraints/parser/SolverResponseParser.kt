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
import tools.aqua.konstraints.parser.lexer.DefineFunRecWord
import tools.aqua.konstraints.parser.lexer.DefineFunWord
import tools.aqua.konstraints.parser.lexer.DefineFunsRecWord
import tools.aqua.konstraints.parser.lexer.EOFToken
import tools.aqua.konstraints.parser.lexer.ErrorToken
import tools.aqua.konstraints.parser.lexer.KeywordToken
import tools.aqua.konstraints.parser.lexer.OpeningBracket
import tools.aqua.konstraints.parser.lexer.QuotedSymbolToken
import tools.aqua.konstraints.parser.lexer.SMTStringToken
import tools.aqua.konstraints.parser.lexer.SMTTokenizer
import tools.aqua.konstraints.parser.lexer.SatToken
import tools.aqua.konstraints.parser.lexer.SimpleSymbolToken
import tools.aqua.konstraints.parser.lexer.SuccessToken
import tools.aqua.konstraints.parser.lexer.SymbolToken
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

object ResponseParser {
  fun parse(response: String, program: SMTProgram): List<SolverResponse> {
    val lexer = SMTTokenizer(response.reader()).peekable()
    val result = mutableListOf<SolverResponse>()

    while (lexer.peek() !is EOFToken) {
      result.add(parseGeneralResponse(lexer, program))
    }

    return result.toList()
  }

  /** Parse a single response from [reader]. */
  fun parse(reader: Reader, program: SMTProgram): SolverResponse {
    val lexer = SMTTokenizer(reader).peekable()
    return parseGeneralResponse(lexer, program)
  }

  @OptIn(ExperimentalContracts::class)
  private fun parseGeneralResponse(
      lexer: PeekableIterator<Token>,
      program: SMTProgram,
  ): SolverResponse {
    val token = lexer.next()

    if (token is SimpleSymbolToken && token.isPredefinedToken()) {
      // cases check_sat_response, succes, unsupported, error
      val predefinedToken = token.toPredefinedToken()

      when (predefinedToken) {
        is SuccessToken -> return SuccessResponse
        is UnsupportedToken -> return UnsupportedResponse
        is SatToken -> return CheckSatResponse(SatStatus.SAT)
        is UnknownToken -> return CheckSatResponse(SatStatus.UNKNOWN)
        is UnsatToken -> return CheckSatResponse(SatStatus.UNSAT)
        else -> throw UnexpectedTokenException(token, "")
      }
    } else if (token is OpeningBracket) {
      val response =
          when (lexer.peek()) {
            is OpeningBracket -> {
              // get_assertions_response, get_model_response, get_unsat_assump_response,
              // get_value_response
              val token = lexer.peek(1)
              val response =
                  when (token) {
                    is DefineFunWord -> {
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
                          ) // get_model_response
                      requireIsInstance<ClosingBracket>(lexer.next())
                      model
                    }
                    is DefineFunRecWord -> TODO() // get_model_response
                    is DefineFunsRecWord -> TODO() // get_model_response
                    else -> TODO()
                  }
              return response
            }
            is SymbolToken -> {
              val token = lexer.next() as SymbolToken

              when (token) {
                is QuotedSymbolToken -> TODO()
                is SimpleSymbolToken -> {
                  if (token.isPredefinedToken()) {
                    // must be error token here
                    requireIsInstance<ErrorToken>(token.toPredefinedToken())
                    parseErrorResponse(lexer)
                  } else {
                    TODO()
                  }
                }
              }
            } // get_unsat_core_response, error response
            is KeywordToken -> TODO() // get_info_response
            else ->
                throw UnexpectedTokenException(
                    lexer.peek(),
                    "any of OpeningBracket, Symbol or Keyword",
                )
          }
      requireIsInstance<ClosingBracket>(lexer.next())
      return response
    } else {
      TODO()
    }

    TODO()
  }

  @OptIn(ExperimentalContracts::class)
  private fun parseErrorResponse(lexer: PeekableIterator<Token>): SolverResponse {
    val token = lexer.next()
    requireIsInstance<SMTStringToken>(token)

    return ErrorResponse(token.contents)
  }
}
