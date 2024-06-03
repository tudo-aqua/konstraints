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

package tools.aqua.konstraints.smt

import tools.aqua.konstraints.parser.Theory
import tools.aqua.konstraints.theories.*

interface Logic {
  val theories: List<Theory>
}

/**
 * Closed formulas built over arbitrary expansions of the Ints and ArraysEx signatures with free
 * sort and function symbols, but with the following restrictions:
 * - all terms of sort Int are linear, that is, have no occurrences of the function symbols *, /,
 *   div, mod, and abs, except as specified in the :extensions attributes;
 * - all array terms have sort (Array Int Int).
 */
data object AUFLIA : Logic {
  override val theories = listOf(CoreTheory, IntsTheory, ArrayExTheory)
}

/**
 * Closed formulas built over arbitrary expansions of the Reals_Ints and ArraysEx signatures with
 * free sort and function symbols, but with the following restrictions:
 * - all terms of sort Int are linear, that is, have no occurrences of the function symbols *, /,
 *   div, mod, and abs, except as specified in the :extensions attributes;
 * - all terms of sort Real are linear, that is, have no occurrences of the function symbols * and
 *   /, except as specified in the :extensions attribute;
 * - all array terms have sort (Array Int Real) or (Array Int (Array Int Real)).
 */
data object AUFLIRA : Logic {
  override val theories = listOf(CoreTheory, RealsIntsTheory, ArrayExTheory)
}

/**
 * Closed formulas built over arbitrary expansions of the Reals_Ints and ArraysEx signatures with
 * free sort and function symbols.
 */
data object AUFNIRA : Logic {
  override val theories = listOf(CoreTheory, RealsIntsTheory, ArrayExTheory)
}

/**
 * Closed formulas built over an arbitrary expansion of the Ints signature with free constant
 * symbols, but whose terms of sort Int are all linear, that is, have no occurrences of the function
 * symbols *, /, div, mod, and abs, except as specified the :extensions attribute.
 */
data object LIA : Logic {
  override val theories = listOf(CoreTheory, IntsTheory)
}

/**
 * Closed formulas built over arbitrary expansions of the Reals signature with free constant
 * symbols, but containing only linear atoms, that is, atoms with no occurrences of the function
 * symbols * and /, except as specified the :extensions attribute.
 */
data object LRA : Logic {
  override val theories = listOf(CoreTheory, RealsTheory)
}

/**
 * Closed quantifier-free formulas built over the FixedSizeBitVectors and ArraysEx signatures, with
 * the restriction that all array terms have sort of the form (Array (_ BitVec i) (_ BitVec j)) for
 * some i, j > 0.
 */
data object QF_ABV : Logic {
  override val theories = listOf(CoreTheory, BitVectorExpressionTheory, ArrayExTheory)
}

/**
 * Closed quantifier-free formulas built over an arbitrary expansion of the FixedSizeBitVectors and
 * ArraysEx signatures with free sort and function symbols, but with the restriction that all array
 * terms have sort of the form (Array (_ BitVec i) (_ BitVec j)) for some i, j > 0.
 */
data object QF_AUFBV : Logic {
  override val theories = listOf(CoreTheory, BitVectorExpressionTheory, ArrayExTheory)
}

/**
 * Closed quantifier-free formulas built over arbitrary expansions of the Ints and ArraysEx
 * signatures with free sort and function symbols, but with the following restrictions:
 * - all terms of sort Int are linear, that is, have no occurrences of the function symbols *, /,
 *   div, mod, and abs, except as specified in the :extensions attributes;
 * - all array terms have sort (Array Int Int).
 */
data object QF_AUFLIA : Logic {
  override val theories = listOf(CoreTheory, IntsTheory, ArrayExTheory)
}

/**
 * Closed quantifier-free formulas built over an arbitrary expansion of the ArraysEx signature with
 * free sort and constant symbols.
 */
data object QF_AX : Logic {
  override val theories = listOf(CoreTheory, ArrayExTheory)
}

/**
 * Closed quantifier-free formulas built over an arbitrary expansion of the FixedSizeBitVectors
 * signature with free constant symbols over the sorts (_ BitVec m) for 0 < m. Formulas in ite terms
 * must satisfy the same restriction as well, with the exception that they need not be closed
 * (because they may be in the scope of a let binder).
 */
data object QF_BV : Logic {
  override val theories = listOf(CoreTheory, BitVectorExpressionTheory)
}

/**
 * Closed quantifier-free formulas with atoms of the form:
 * - q
 * - (op (- x y) n),
 * - (op (- x y) (- n)), or
 * - (op x y)
 *
 * where
 * - q is a variable or free constant symbol of sort Bool,
 * - op is <, <=, >, >=, =, or distinct,
 * - x, y are free constant symbols of sort Int,
 * - n is a numeral.
 */
data object QF_IDL : Logic {
  override val theories = listOf(CoreTheory, IntsTheory)
}

/**
 * Closed quantifier-free formulas built over an arbitrary expansion of the Ints signature with free
 * constant symbols, but whose terms of sort Int are all linear, that is, have no occurrences of the
 * function symbols /, div, mod, and abs, and no occurrences of the function symbol *, except as
 * specified in the :extensions attribute.
 */
data object QF_LIA : Logic {
  override val theories = listOf(CoreTheory, IntsTheory)
}

/**
 * Closed quantifier-free formulas built over an arbitrary expansion of the Ints signature with free
 * constant symbols.
 */
data object QF_NIA : Logic {
  override val theories = listOf(CoreTheory, IntsTheory)
}

/**
 * Closed quantifier-free formulas built over arbitrary expansions of the Reals signature with free
 * constant symbols.
 */
data object QF_NRA : Logic {
  override val theories = listOf(CoreTheory, RealsTheory)
}

/**
 * Closed quantifier-free formulas built over arbitrary expansions of the Reals signature with free
 * constant symbols, but containing only linear atoms, that is, atoms with no occurrences of the
 * function symbols * and /, except as specified the :extensions attribute.
 */
data object QF_LRA : Logic {
  override val theories = listOf(CoreTheory, RealsTheory)
}

/**
 * Closed quantifier-free formulas with atoms of the form:
 * - p
 * - (op (- x y) c),
 * - (op x y),
 * - (op (- (+ x ... x) (+ y ... y)) c) with n > 1 occurrences of x and of y,
 *
 *   where
 * - p is a variable or free constant symbol of sort Bool,
 * - c is an expression of the form m or (- m) for some numeral m,
 * - op is <, <=, >, >=, =, or distinct,
 * - x, y are free constant symbols of sort Real.
 */
data object QF_RDL : Logic {
  override val theories = listOf(CoreTheory, RealsTheory)
}

/**
 * Closed quantifier-free formulas built over an arbitrary expansion of the Core signature with free
 * sort and function symbols.
 */
data object QF_UF : Logic {
  override val theories: List<Theory> = listOf(CoreTheory)
}

/**
 * Closed quantifier-free formulas built over arbitrary expansions of the FixedSizeBitVectors
 * signature with free sort and function symbols.
 */
data object QF_UFBV : Logic {
  override val theories = listOf(CoreTheory, BitVectorExpressionTheory)
}

/**
 * Closed quantifier-free formulas built over an arbitrary expansion with free sort and function
 * symbols of the signature consisting of
 * - all the sort and function symbols of Core and
 * - the following symbols of Int:
 *
 *     - :sorts ((Int 0))
 *     - :funs
 *       - (NUMERAL Int)
 *       - (- Int Int Int)
 *       - (+ Int Int Int)
 *       - (<= Int Int Bool)
 *       - (< Int Int Bool)
 *       - (>= Int Int Bool)
 *       - (> Int Int Bool)
 *
 * Additionally, for every term of the form (op t1 t2) with op in {+, -}, at least one of t1 and t2
 * is a numeral.
 */
data object QF_UFIDL : Logic {
  override val theories = listOf(CoreTheory, IntsTheory)
}

/**
 * Closed quantifier-free formulas built over arbitrary expansions of the Ints signatures with free
 * sort and function symbols, but with the following restrictions:
 * - all terms of sort Int are linear, that is, have no occurrences of the function symbols *, /,
 *   div, mod, and abs, except as specified in the :extensions attributes;
 */
data object QF_UFLIA : Logic {
  override val theories = listOf(CoreTheory, IntsTheory)
}

/**
 * Closed quantifier-free formulas built over arbitrary expansions of the Reals signature with free
 * sort and function symbols, but containing only linear atoms, that is, atoms with no occurrences
 * of the function symbols * and /, except as specified the :extensions attribute.
 */
data object QF_UFLRA : Logic {
  override val theories = listOf(CoreTheory, RealsTheory)
}

/**
 * Closed quantifier-free formulas built over arbitrary expansions of the Reals signature with free
 * sort and function symbols.
 */
data object QF_UFNRA : Logic {
  override val theories = listOf(CoreTheory, RealsTheory)
}

/**
 * Closed formulas built over arbitrary expansions of the Reals signature with free sort and
 * function symbols, but containing only linear atoms, that is, atoms with no occurrences of the
 * function symbols * and /, except as specified the :extensions attribute.
 */
data object UFLRA : Logic {
  override val theories = listOf(CoreTheory, RealsTheory)
}

/**
 * Closed formulas built over an arbitrary expansion of the Ints signature with free sort and
 * function symbols.
 */
data object UFNIA : Logic {
  override val theories = listOf(CoreTheory, IntsTheory)
}

/** Quantifier-free formulas over floating point arithmetic */
data object QF_FP : Logic {
  override val theories = listOf(CoreTheory, FloatingPointTheory)
}
