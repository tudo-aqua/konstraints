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

package tools.aqua.konstraints.dsl

import java.util.*
import tools.aqua.konstraints.smt.*

/** Exists quantifier with one bound variable of [sort]. */
fun <S : Sort> exists(sort: S, block: (Expression<S>) -> Expression<BoolSort>): ExistsExpression {
  val boundVar = SortedVar("|$sort!${UUID.randomUUID()}|".toSymbolWithQuotes(), sort)

  return ExistsExpression(listOf(boundVar), block(boundVar.instance))
}

/** Exists quantifier with two bound variable of [sort1], [sort2]. */
fun <S1 : Sort, S2 : Sort> exists(
    sort1: S1,
    sort2: S2,
    block: (Expression<S1>, Expression<S2>) -> Expression<BoolSort>
): ExistsExpression {
  val boundVar1 = SortedVar("|$sort1!${UUID.randomUUID()}|".toSymbolWithQuotes(), sort1)
  val boundVar2 = SortedVar("|$sort2!${UUID.randomUUID()}|".toSymbolWithQuotes(), sort2)

  return ExistsExpression(
      listOf(boundVar1, boundVar2), block(boundVar1.instance, boundVar2.instance))
}

/** Exists quantifier with three bound variable of [sort1], [sort2], [sort3]. */
fun <S1 : Sort, S2 : Sort, S3 : Sort> exists(
    sort1: S1,
    sort2: S2,
    sort3: S3,
    block: (Expression<S1>, Expression<S2>, Expression<S3>) -> Expression<BoolSort>
): ExistsExpression {
  val boundVar1 = SortedVar("|$sort1!${UUID.randomUUID()}|".toSymbolWithQuotes(), sort1)
  val boundVar2 = SortedVar("|$sort2!${UUID.randomUUID()}|".toSymbolWithQuotes(), sort2)
  val boundVar3 = SortedVar("|$sort3!${UUID.randomUUID()}|".toSymbolWithQuotes(), sort3)

  return ExistsExpression(
      listOf(boundVar1, boundVar2, boundVar3),
      block(boundVar1.instance, boundVar2.instance, boundVar3.instance))
}

/** Exists quantifier with four bound variable of [sort1], [sort2], [sort3], [sort4]. */
fun <S1 : Sort, S2 : Sort, S3 : Sort, S4 : Sort> exists(
    sort1: S1,
    sort2: S2,
    sort3: S3,
    sort4: S4,
    block: (Expression<S1>, Expression<S2>, Expression<S3>, Expression<S4>) -> Expression<BoolSort>
): ExistsExpression {
  val boundVar1 = SortedVar("|$sort1!${UUID.randomUUID()}|".toSymbolWithQuotes(), sort1)
  val boundVar2 = SortedVar("|$sort2!${UUID.randomUUID()}|".toSymbolWithQuotes(), sort2)
  val boundVar3 = SortedVar("|$sort3!${UUID.randomUUID()}|".toSymbolWithQuotes(), sort3)
  val boundVar4 = SortedVar("|$sort4!${UUID.randomUUID()}|".toSymbolWithQuotes(), sort4)

  return ExistsExpression(
      listOf(boundVar1, boundVar2, boundVar3, boundVar4),
      block(boundVar1.instance, boundVar2.instance, boundVar3.instance, boundVar4.instance))
}

/** Exists quantifier with five bound variable of [sort1], [sort2], [sort3], [sort4], [sort5]. */
fun <S1 : Sort, S2 : Sort, S3 : Sort, S4 : Sort, S5 : Sort> exists(
    sort1: S1,
    sort2: S2,
    sort3: S3,
    sort4: S4,
    sort5: S5,
    block:
        (
            Expression<S1>,
            Expression<S2>,
            Expression<S3>,
            Expression<S4>,
            Expression<S5>) -> Expression<BoolSort>
): ExistsExpression {
  val boundVar1 = SortedVar("|$sort1!${UUID.randomUUID()}|".toSymbolWithQuotes(), sort1)
  val boundVar2 = SortedVar("|$sort2!${UUID.randomUUID()}|".toSymbolWithQuotes(), sort2)
  val boundVar3 = SortedVar("|$sort3!${UUID.randomUUID()}|".toSymbolWithQuotes(), sort3)
  val boundVar4 = SortedVar("|$sort4!${UUID.randomUUID()}|".toSymbolWithQuotes(), sort4)
  val boundVar5 = SortedVar("|$sort5!${UUID.randomUUID()}|".toSymbolWithQuotes(), sort5)

  return ExistsExpression(
      listOf(boundVar1, boundVar2, boundVar3, boundVar4, boundVar5),
      block(
          boundVar1.instance,
          boundVar2.instance,
          boundVar3.instance,
          boundVar4.instance,
          boundVar5.instance))
}

/** Exists quantifier with at least 6 bound variable of any sort. */
fun exists(
    sort1: Sort,
    sort2: Sort,
    sort3: Sort,
    sort4: Sort,
    sort5: Sort,
    vararg sorts: Sort,
    block: (List<Expression<*>>) -> Expression<BoolSort>
): ExistsExpression {
  val boundVars =
      listOf(
          SortedVar("|$sort1!${UUID.randomUUID()}|".toSymbolWithQuotes(), sort1),
          SortedVar("|$sort2!${UUID.randomUUID()}|".toSymbolWithQuotes(), sort2),
          SortedVar("|$sort3!${UUID.randomUUID()}|".toSymbolWithQuotes(), sort3),
          SortedVar("|$sort4!${UUID.randomUUID()}|".toSymbolWithQuotes(), sort4),
          SortedVar("|$sort5!${UUID.randomUUID()}|".toSymbolWithQuotes(), sort5)) +
          sorts.map { sort -> SortedVar("|$sort!${UUID.randomUUID()}|".toSymbolWithQuotes(), sort) }

  return ExistsExpression(boundVars, block(boundVars.map { it.instance }))
}

/** Exists quantifier with any number of bound variable of any sort. */
fun exists(
    sorts: List<Sort>,
    block: (List<Expression<*>>) -> Expression<BoolSort>
): ExistsExpression {
  val boundVars =
      sorts.map { sort -> SortedVar("|$sort!${UUID.randomUUID()}|".toSymbolWithQuotes(), sort) }

  return ExistsExpression(boundVars, block(boundVars.map { it.instance }))
}

/** Universal quantifier with one bound variable of [sort]. */
fun <S : Sort> forall(sort: S, block: (Expression<S>) -> Expression<BoolSort>): ForallExpression {
  val boundVar = SortedVar("|$sort!${UUID.randomUUID()}|".toSymbolWithQuotes(), sort)

  return ForallExpression(listOf(boundVar), block(boundVar.instance))
}

/** Universal quantifier with two bound variable of [sort1], [sort2]. */
fun <S1 : Sort, S2 : Sort> forall(
    sort1: S1,
    sort2: S2,
    block: (Expression<S1>, Expression<S2>) -> Expression<BoolSort>
): ForallExpression {
  val boundVar1 = SortedVar("|$sort1!${UUID.randomUUID()}|".toSymbolWithQuotes(), sort1)
  val boundVar2 = SortedVar("|$sort2!${UUID.randomUUID()}|".toSymbolWithQuotes(), sort2)

  return ForallExpression(
      listOf(boundVar1, boundVar2), block(boundVar1.instance, boundVar2.instance))
}

/** Universal quantifier with three bound variable of [sort1], [sort2], [sort3]. */
fun <S1 : Sort, S2 : Sort, S3 : Sort> forall(
    sort1: S1,
    sort2: S2,
    sort3: S3,
    block: (Expression<S1>, Expression<S2>, Expression<S3>) -> Expression<BoolSort>
): ForallExpression {
  val boundVar1 = SortedVar("|$sort1!${UUID.randomUUID()}|".toSymbolWithQuotes(), sort1)
  val boundVar2 = SortedVar("|$sort2!${UUID.randomUUID()}|".toSymbolWithQuotes(), sort2)
  val boundVar3 = SortedVar("|$sort3!${UUID.randomUUID()}|".toSymbolWithQuotes(), sort3)

  return ForallExpression(
      listOf(boundVar1, boundVar2, boundVar3),
      block(boundVar1.instance, boundVar2.instance, boundVar3.instance))
}

/** Universal quantifier with four bound variable of [sort1], [sort2], [sort3], [sort4]. */
fun <S1 : Sort, S2 : Sort, S3 : Sort, S4 : Sort> forall(
    sort1: S1,
    sort2: S2,
    sort3: S3,
    sort4: S4,
    block: (Expression<S1>, Expression<S2>, Expression<S3>, Expression<S4>) -> Expression<BoolSort>
): ForallExpression {
  val boundVar1 = SortedVar("|$sort1!${UUID.randomUUID()}|".toSymbolWithQuotes(), sort1)
  val boundVar2 = SortedVar("|$sort2!${UUID.randomUUID()}|".toSymbolWithQuotes(), sort2)
  val boundVar3 = SortedVar("|$sort3!${UUID.randomUUID()}|".toSymbolWithQuotes(), sort3)
  val boundVar4 = SortedVar("|$sort4!${UUID.randomUUID()}|".toSymbolWithQuotes(), sort4)

  return ForallExpression(
      listOf(boundVar1, boundVar2, boundVar3, boundVar4),
      block(boundVar1.instance, boundVar2.instance, boundVar3.instance, boundVar4.instance))
}

/** Universal quantifier with five bound variable of [sort1], [sort2], [sort3], [sort4], [sort5]. */
fun <S1 : Sort, S2 : Sort, S3 : Sort, S4 : Sort, S5 : Sort> forall(
    sort1: S1,
    sort2: S2,
    sort3: S3,
    sort4: S4,
    sort5: S5,
    block:
        (
            Expression<S1>,
            Expression<S2>,
            Expression<S3>,
            Expression<S4>,
            Expression<S5>) -> Expression<BoolSort>
): ForallExpression {
  val boundVar1 = SortedVar("|$sort1!${UUID.randomUUID()}|".toSymbolWithQuotes(), sort1)
  val boundVar2 = SortedVar("|$sort2!${UUID.randomUUID()}|".toSymbolWithQuotes(), sort2)
  val boundVar3 = SortedVar("|$sort3!${UUID.randomUUID()}|".toSymbolWithQuotes(), sort3)
  val boundVar4 = SortedVar("|$sort4!${UUID.randomUUID()}|".toSymbolWithQuotes(), sort4)
  val boundVar5 = SortedVar("|$sort5!${UUID.randomUUID()}|".toSymbolWithQuotes(), sort5)

  return ForallExpression(
      listOf(boundVar1, boundVar2, boundVar3, boundVar4, boundVar5),
      block(
          boundVar1.instance,
          boundVar2.instance,
          boundVar3.instance,
          boundVar4.instance,
          boundVar5.instance))
}

/** Universal quantifier with at least 6 bound variable of any sort. */
fun forall(
    sort1: Sort,
    sort2: Sort,
    sort3: Sort,
    sort4: Sort,
    sort5: Sort,
    vararg sorts: Sort,
    block: (List<Expression<*>>) -> Expression<BoolSort>
): ForallExpression {
  val boundVars =
      listOf(
          SortedVar("|$sort1!${UUID.randomUUID()}|".toSymbolWithQuotes(), sort1),
          SortedVar("|$sort2!${UUID.randomUUID()}|".toSymbolWithQuotes(), sort2),
          SortedVar("|$sort3!${UUID.randomUUID()}|".toSymbolWithQuotes(), sort3),
          SortedVar("|$sort4!${UUID.randomUUID()}|".toSymbolWithQuotes(), sort4),
          SortedVar("|$sort5!${UUID.randomUUID()}|".toSymbolWithQuotes(), sort5)) +
          sorts.map { sort -> SortedVar("|$sort!${UUID.randomUUID()}|".toSymbolWithQuotes(), sort) }

  return ForallExpression(boundVars, block(boundVars.map { it.instance }))
}

/** Universal quantifier with any number of bound variable of any sort. */
fun forall(
    sorts: List<Sort>,
    block: (List<Expression<*>>) -> Expression<BoolSort>
): ForallExpression {
  val boundVars =
      sorts.map { sort -> SortedVar("|$sort!${UUID.randomUUID()}|".toSymbolWithQuotes(), sort) }

  return ForallExpression(boundVars, block(boundVars.map { it.instance }))
}
