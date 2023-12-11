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

package tools.aqua.konstraints.visitors

import com.microsoft.z3.BoolSort
import com.microsoft.z3.Expr
import com.microsoft.z3.Sort
import tools.aqua.konstraints.Expression

/**
 * This interface implements methods to "unroll" functions with certain attributes if the solver
 * interface does not have a vararg constructor available
 */

// TODO this currently only returns Z3 Expressions and needs to be generalized
interface AssociativeVisitor {
  /**
   * Build a left associative expression using [operation] (e.g. BVADD) S1 and S2 are Z3 target
   * sorts, R is a konstraints sort of the original expression
   */
  fun <R : tools.aqua.konstraints.Sort, S1 : Sort, S2 : Sort> makeLeftAssoc(
      expressions: List<Expression<R>>,
      visit: (Expression<R>) -> Expr<*>,
      operation: (Expr<S1>, Expr<S2>) -> Expr<S1>
  ): Expr<S1> {
    return if (expressions.size == 2) {
      operation(visit(expressions[0]) as Expr<S1>, visit(expressions[1]) as Expr<S2>)
    } else {
      operation(
          makeLeftAssoc(expressions.dropLast(1), visit, operation),
          visit(expressions.last()) as Expr<S2>)
    }
  }

  /**
   * Build a right associative expression using [operation] (e.g. =>) S1 and S2 are Z3 target sorts,
   * R is a konstraints sort of the original expression
   */
  fun <R : tools.aqua.konstraints.Sort, S1 : Sort, S2 : Sort> makeRightAssoc(
      expressions: List<Expression<R>>,
      visit: (Expression<R>) -> Expr<*>,
      operation: (Expr<S1>, Expr<S2>) -> Expr<S2>
  ): Expr<S2> {
    return if (expressions.size == 2) {
      operation(visit(expressions[0]) as Expr<S1>, visit(expressions[1]) as Expr<S2>)
    } else {
      operation(
          visit(expressions.first()) as Expr<S1>,
          makeRightAssoc(expressions.drop(1), visit, operation))
    }
  }

  /**
   * Unrolls a chainable expression of any type into a list e.g. (= A B C D) will be unrolled to
   * [(= A B), (= B C), (= C D)]
   */
  fun <S : Sort> makeChainable(
      expressions: List<Expression<*>>,
      visit: (Expression<*>) -> Expr<*>,
      operation: (Expr<S>, Expr<S>) -> Expr<BoolSort>
  ): List<Expr<BoolSort>> {
    if (expressions.size == 2) {
      return listOf(operation(visit(expressions[0]) as Expr<S>, visit(expressions[1]) as Expr<S>))
    } else {
      return expressions.zipWithNext { a, b -> operation(visit(a) as Expr<S>, visit(b) as Expr<S>) }
    }
  }
}
