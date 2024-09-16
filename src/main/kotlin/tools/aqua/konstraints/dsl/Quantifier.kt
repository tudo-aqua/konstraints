/*
 * SPDX-License-Identifier: Apache-2.0
 *
 * Copyright 2023-2024 The Konstraints Authors
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
import tools.aqua.konstraints.parser.SortedVar
import tools.aqua.konstraints.smt.*
import tools.aqua.konstraints.theories.*

/** Exists quantifier with one bound variable of [sort] */
fun <S : Sort> Builder<BoolSort>.exists(
    sort: S,
    block: Builder<BoolSort>.(Expression<S>) -> Expression<BoolSort>
): ExistsExpression {
  val boundVar = SortedVar("|$sort!${UUID.randomUUID()}|".symbol(), sort)

  children.add(ExistsExpression(listOf(boundVar), Builder<BoolSort>().block(boundVar.instance)))

  return children.last() as ExistsExpression
}

/** Exists quantifier with two bound variable of [sort1], [sort2] */
fun <S1 : Sort, S2 : Sort> Builder<BoolSort>.exists(
    sort1: S1,
    sort2: S2,
    block: Builder<BoolSort>.(Expression<S1>, Expression<S2>) -> Expression<BoolSort>
): ExistsExpression {
  val boundVar1 = SortedVar("|$sort1!${UUID.randomUUID()}|".symbol(), sort1)
  val boundVar2 = SortedVar("|$sort2!${UUID.randomUUID()}|".symbol(), sort2)

  children.add(
      ExistsExpression(
          listOf(boundVar1, boundVar2),
          Builder<BoolSort>().block(boundVar1.instance, boundVar2.instance)))

  return children.last() as ExistsExpression
}

/** Exists quantifier with three bound variable of [sort1], [sort2], [sort3] */
fun <S1 : Sort, S2 : Sort, S3 : Sort> Builder<BoolSort>.exists(
    sort1: S1,
    sort2: S2,
    sort3: S3,
    block:
        Builder<BoolSort>.(Expression<S1>, Expression<S2>, Expression<S3>) -> Expression<BoolSort>
): ExistsExpression {
  val boundVar1 = SortedVar("|$sort1!${UUID.randomUUID()}|".symbol(), sort1)
  val boundVar2 = SortedVar("|$sort2!${UUID.randomUUID()}|".symbol(), sort2)
  val boundVar3 = SortedVar("|$sort3!${UUID.randomUUID()}|".symbol(), sort3)

  children.add(
      ExistsExpression(
          listOf(boundVar1, boundVar2, boundVar3),
          Builder<BoolSort>().block(boundVar1.instance, boundVar2.instance, boundVar3.instance)))

  return children.last() as ExistsExpression
}

/** Exists quantifier with four bound variable of [sort1], [sort2], [sort3], [sort4] */
fun <S1 : Sort, S2 : Sort, S3 : Sort, S4 : Sort> Builder<BoolSort>.exists(
    sort1: S1,
    sort2: S2,
    sort3: S3,
    sort4: S4,
    block:
        Builder<BoolSort>.(
            Expression<S1>, Expression<S2>, Expression<S3>, Expression<S4>) -> Expression<BoolSort>
): ExistsExpression {
  val boundVar1 = SortedVar("|$sort1!${UUID.randomUUID()}|".symbol(), sort1)
  val boundVar2 = SortedVar("|$sort2!${UUID.randomUUID()}|".symbol(), sort2)
  val boundVar3 = SortedVar("|$sort3!${UUID.randomUUID()}|".symbol(), sort3)
  val boundVar4 = SortedVar("|$sort4!${UUID.randomUUID()}|".symbol(), sort4)

  children.add(
      ExistsExpression(
          listOf(boundVar1, boundVar2, boundVar3, boundVar4),
          Builder<BoolSort>()
              .block(
                  boundVar1.instance, boundVar2.instance, boundVar3.instance, boundVar4.instance)))

  return children.last() as ExistsExpression
}

/** Exists quantifier with five bound variable of [sort1], [sort2], [sort3], [sort4], [sort5] */
fun <S1 : Sort, S2 : Sort, S3 : Sort, S4 : Sort, S5 : Sort> Builder<BoolSort>.exists(
    sort1: S1,
    sort2: S2,
    sort3: S3,
    sort4: S4,
    sort5: S5,
    block:
        Builder<BoolSort>.(
            Expression<S1>,
            Expression<S2>,
            Expression<S3>,
            Expression<S4>,
            Expression<S5>) -> Expression<BoolSort>
): ExistsExpression {
  val boundVar1 = SortedVar("|$sort1!${UUID.randomUUID()}|".symbol(), sort1)
  val boundVar2 = SortedVar("|$sort2!${UUID.randomUUID()}|".symbol(), sort2)
  val boundVar3 = SortedVar("|$sort3!${UUID.randomUUID()}|".symbol(), sort3)
  val boundVar4 = SortedVar("|$sort4!${UUID.randomUUID()}|".symbol(), sort4)
  val boundVar5 = SortedVar("|$sort5!${UUID.randomUUID()}|".symbol(), sort5)

  children.add(
      ExistsExpression(
          listOf(boundVar1, boundVar2, boundVar3, boundVar4, boundVar5),
          Builder<BoolSort>()
              .block(
                  boundVar1.instance,
                  boundVar2.instance,
                  boundVar3.instance,
                  boundVar4.instance,
                  boundVar5.instance)))

  return children.last() as ExistsExpression
}

/** Exists quantifier with at least 6 bound variable of any sort */
fun Builder<BoolSort>.exists(
    sort1: Sort,
    sort2: Sort,
    sort3: Sort,
    sort4: Sort,
    sort5: Sort,
    vararg sorts: Sort,
    block: Builder<BoolSort>.(List<Expression<*>>) -> Expression<BoolSort>
): ExistsExpression {
  val boundVars =
      listOf(
          SortedVar("|$sort1!${UUID.randomUUID()}|".symbol(), sort1),
          SortedVar("|$sort2!${UUID.randomUUID()}|".symbol(), sort2),
          SortedVar("|$sort3!${UUID.randomUUID()}|".symbol(), sort3),
          SortedVar("|$sort4!${UUID.randomUUID()}|".symbol(), sort4),
          SortedVar("|$sort5!${UUID.randomUUID()}|".symbol(), sort5)) +
          sorts.map { sort -> SortedVar("|$sort!${UUID.randomUUID()}|".symbol(), sort) }

  children.add(
      ExistsExpression(boundVars, Builder<BoolSort>().block(boundVars.map { it.instance })))

  return children.last() as ExistsExpression
}

/** Exists quantifier with any number of bound variable of any sort */
fun Builder<BoolSort>.exists(
    sorts: List<Sort>,
    block: Builder<BoolSort>.(List<Expression<*>>) -> Expression<BoolSort>
): ExistsExpression {
  val boundVars = sorts.map { sort -> SortedVar("|$sort!${UUID.randomUUID()}|".symbol(), sort) }

  children.add(
      ExistsExpression(boundVars, Builder<BoolSort>().block(boundVars.map { it.instance })))

  return children.last() as ExistsExpression
}

/** Universal quantifier with one bound variable of [sort] */
fun <S : Sort> Builder<BoolSort>.forall(
    sort: S,
    block: Builder<BoolSort>.(Expression<S>) -> Expression<BoolSort>
): ForallExpression {
  val boundVar = SortedVar("|$sort!${UUID.randomUUID()}|".symbol(), sort)

  children.add(ForallExpression(listOf(boundVar), Builder<BoolSort>().block(boundVar.instance)))

  return children.last() as ForallExpression
}

/** Universal quantifier with two bound variable of [sort1], [sort2] */
fun <S1 : Sort, S2 : Sort> Builder<BoolSort>.forall(
    sort1: S1,
    sort2: S2,
    block: Builder<BoolSort>.(Expression<S1>, Expression<S2>) -> Expression<BoolSort>
): ForallExpression {
  val boundVar1 = SortedVar("|$sort1!${UUID.randomUUID()}|".symbol(), sort1)
  val boundVar2 = SortedVar("|$sort2!${UUID.randomUUID()}|".symbol(), sort2)

  children.add(
      ForallExpression(
          listOf(boundVar1, boundVar2),
          Builder<BoolSort>().block(boundVar1.instance, boundVar2.instance)))

  return children.last() as ForallExpression
}

/** Universal quantifier with three bound variable of [sort1], [sort2], [sort3] */
fun <S1 : Sort, S2 : Sort, S3 : Sort> Builder<BoolSort>.forall(
    sort1: S1,
    sort2: S2,
    sort3: S3,
    block:
        Builder<BoolSort>.(Expression<S1>, Expression<S2>, Expression<S3>) -> Expression<BoolSort>
): ForallExpression {
  val boundVar1 = SortedVar("|$sort1!${UUID.randomUUID()}|".symbol(), sort1)
  val boundVar2 = SortedVar("|$sort2!${UUID.randomUUID()}|".symbol(), sort2)
  val boundVar3 = SortedVar("|$sort3!${UUID.randomUUID()}|".symbol(), sort3)

  children.add(
      ForallExpression(
          listOf(boundVar1, boundVar2, boundVar3),
          Builder<BoolSort>().block(boundVar1.instance, boundVar2.instance, boundVar3.instance)))

  return children.last() as ForallExpression
}

/** Universal quantifier with four bound variable of [sort1], [sort2], [sort3], [sort4] */
fun <S1 : Sort, S2 : Sort, S3 : Sort, S4 : Sort> Builder<BoolSort>.forall(
    sort1: S1,
    sort2: S2,
    sort3: S3,
    sort4: S4,
    block:
        Builder<BoolSort>.(
            Expression<S1>, Expression<S2>, Expression<S3>, Expression<S4>) -> Expression<BoolSort>
): ForallExpression {
  val boundVar1 = SortedVar("|$sort1!${UUID.randomUUID()}|".symbol(), sort1)
  val boundVar2 = SortedVar("|$sort2!${UUID.randomUUID()}|".symbol(), sort2)
  val boundVar3 = SortedVar("|$sort3!${UUID.randomUUID()}|".symbol(), sort3)
  val boundVar4 = SortedVar("|$sort4!${UUID.randomUUID()}|".symbol(), sort4)

  children.add(
      ForallExpression(
          listOf(boundVar1, boundVar2, boundVar3, boundVar4),
          Builder<BoolSort>()
              .block(
                  boundVar1.instance, boundVar2.instance, boundVar3.instance, boundVar4.instance)))

  return children.last() as ForallExpression
}

/** Universal quantifier with five bound variable of [sort1], [sort2], [sort3], [sort4], [sort5] */
fun <S1 : Sort, S2 : Sort, S3 : Sort, S4 : Sort, S5 : Sort> Builder<BoolSort>.forall(
    sort1: S1,
    sort2: S2,
    sort3: S3,
    sort4: S4,
    sort5: S5,
    block:
        Builder<BoolSort>.(
            Expression<S1>,
            Expression<S2>,
            Expression<S3>,
            Expression<S4>,
            Expression<S5>) -> Expression<BoolSort>
): ForallExpression {
  val boundVar1 = SortedVar("|$sort1!${UUID.randomUUID()}|".symbol(), sort1)
  val boundVar2 = SortedVar("|$sort2!${UUID.randomUUID()}|".symbol(), sort2)
  val boundVar3 = SortedVar("|$sort3!${UUID.randomUUID()}|".symbol(), sort3)
  val boundVar4 = SortedVar("|$sort4!${UUID.randomUUID()}|".symbol(), sort4)
  val boundVar5 = SortedVar("|$sort5!${UUID.randomUUID()}|".symbol(), sort5)

  children.add(
      ForallExpression(
          listOf(boundVar1, boundVar2, boundVar3, boundVar4, boundVar5),
          Builder<BoolSort>()
              .block(
                  boundVar1.instance,
                  boundVar2.instance,
                  boundVar3.instance,
                  boundVar4.instance,
                  boundVar5.instance)))

  return children.last() as ForallExpression
}

/** Universal quantifier with at least 6 bound variable of any sort */
fun Builder<BoolSort>.forall(
    sort1: Sort,
    sort2: Sort,
    sort3: Sort,
    sort4: Sort,
    sort5: Sort,
    vararg sorts: Sort,
    block: Builder<BoolSort>.(List<Expression<*>>) -> Expression<BoolSort>
): ForallExpression {
  val boundVars =
      listOf(
          SortedVar("|$sort1!${UUID.randomUUID()}|".symbol(), sort1),
          SortedVar("|$sort2!${UUID.randomUUID()}|".symbol(), sort2),
          SortedVar("|$sort3!${UUID.randomUUID()}|".symbol(), sort3),
          SortedVar("|$sort4!${UUID.randomUUID()}|".symbol(), sort4),
          SortedVar("|$sort5!${UUID.randomUUID()}|".symbol(), sort5)) +
          sorts.map { sort -> SortedVar("|$sort!${UUID.randomUUID()}|".symbol(), sort) }

  children.add(
      ForallExpression(boundVars, Builder<BoolSort>().block(boundVars.map { it.instance })))

  return children.last() as ForallExpression
}

/** Universal quantifier with any number of bound variable of any sort */
fun Builder<BoolSort>.forall(
    sorts: List<Sort>,
    block: Builder<BoolSort>.(List<Expression<*>>) -> Expression<BoolSort>
): ForallExpression {
  val boundVars = sorts.map { sort -> SortedVar("|$sort!${UUID.randomUUID()}|".symbol(), sort) }

  children.add(
      ForallExpression(boundVars, Builder<BoolSort>().block(boundVars.map { it.instance })))

  return children.last() as ForallExpression
}
