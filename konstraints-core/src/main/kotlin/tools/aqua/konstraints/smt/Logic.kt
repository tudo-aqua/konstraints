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

package tools.aqua.konstraints.smt

/** Interface for all logics. */
sealed interface Logic {
  companion object {
    val logics =
        mutableMapOf(
            "ABV" to ABV,
            "ABVFP" to ABVFP,
            "ABVFPLRA" to ABVFPLRA,
            "ALIA" to ALIA,
            "ANIA" to ANIA,
            "AUFBV" to AUFBV,
            "AUFBVDTLIA" to AUFBVDTLIA,
            "AUFBVDTNIA" to AUFBVDTNIA,
            "AUFBVDTNIRA" to AUFBVDTNIRA,
            "AUFBVFP" to AUFBVFP,
            "AUFDTLIA" to AUFDTLIA,
            "AUFDTLIRA" to AUFDTLIRA,
            "AUFDTNIRA" to AUFDTNIRA,
            "AUFFPDTNIRA" to AUFFPDTNIRA,
            "AUFLIA" to AUFLIA,
            "AUFLIRA" to AUFLIRA,
            "AUFNIA" to AUFNIA,
            "AUFNIRA" to AUFNIRA,
            "BV" to BV,
            "BVFP" to BVFP,
            "BVFPLRA" to BVFPLRA,
            "FP" to FP,
            "FPLRA" to FPLRA,
            "LIA" to LIA,
            "LRA" to LRA,
            "NIA" to NIA,
            "NRA" to NRA,
            "QF_ABV" to QF_ABV,
            "QF_ABVFP" to QF_ABVFP,
            "QF_ABVFPLRA" to QF_ABVFPLRA,
            "QF_ALIA" to QF_ALIA,
            "QF_ANIA" to QF_ANIA,
            "QF_AUFBV" to QF_AUFBV,
            "QF_AUFBVFP" to QF_AUFBVFP,
            "QF_AUFLIA" to QF_AUFLIA,
            "QF_AUFNIA" to QF_AUFNIA,
            "QF_AX" to QF_AX,
            "QF_BV" to QF_BV,
            "QF_BVFP" to QF_BVFP,
            "QF_BVFPLRA" to QF_BVFPLRA,
            "QF_DT" to QF_DT,
            "QF_FP" to QF_FP,
            "QF_FPLRA" to QF_FPLRA,
            "QF_IDL" to QF_IDL,
            "QF_LIA" to QF_LIA,
            "QF_LIRA" to QF_LIRA,
            "QF_LRA" to QF_LRA,
            "QF_NIA" to QF_NIA,
            "QF_NIRA" to QF_NIRA,
            "QF_NRA" to QF_NRA,
            "QF_RDL" to QF_RDL,
            "QF_S" to QF_S,
            "QF_SLIA" to QF_SLIA,
            "QF_SNIA" to QF_SNIA,
            "QF_UF" to QF_UF,
            "QF_UFBV" to QF_UFBV,
            "QF_UFBVDT" to QF_UFBVDT,
            "QF_UFDT" to QF_UFDT,
            "QF_UFDTLIA" to QF_UFDTLIA,
            "QF_UFDTLIRA" to QF_UFDTLIRA,
            "QF_UFDTNIA" to QF_UFDTNIA,
            "QF_UFFP" to QF_UFFP,
            "QF_UFFPDTNIRA" to QF_UFFPDTNIRA,
            "QF_UFIDL" to QF_UFIDL,
            "QF_UFLIA" to QF_UFLIA,
            "QF_UFLRA" to QF_UFLRA,
            "QF_UFNIA" to QF_UFNIA,
            "QF_UFNRA" to QF_UFNRA,
            "UF" to UF,
            "UFBV" to UFBV,
            "UFBVDT" to UFBVDT,
            "UFBVFP" to UFBVFP,
            "UFBVLIA" to UFBVLIA,
            "UFDT" to UFDT,
            "UFDTLIA" to UFDTLIA,
            "UFDTLIRA" to UFDTLIRA,
            "UFDTNIA" to UFDTNIA,
            "UFDTNIRA" to UFDTNIRA,
            "UFFPDTNIRA" to UFFPDTNIRA,
            "UFIDL" to UFIDL,
            "UFLIA" to UFLIA,
            "UFLRA" to UFLRA,
            "UFNIA" to UFNIA,
            "UFNIRA" to UFNIRA,
            "QF_ASLIA" to QF_ASLIA,
        )
  }

  val theories: Set<Theories>
  val datatypes: Boolean
  val quantifierFree: Boolean
  val linearArithmetic: Boolean
  val nonlinearArithmetic: Boolean
  val differentialArithmetic: Boolean
  val freeSortFunctionSymbols: Boolean
}

/**
 * This logic does not yet provide an offical documentation, but has the following properties:
 *
 * This logic includes the following theories:
 * - FixedSizeBitVectors
 * - FloatingPoint
 */
data object BVFP : Logic {
  override val theories =
      setOf(Theories.CORE, Theories.FIXED_SIZE_BIT_VECTORS, Theories.FLOATING_POINT)
  override val datatypes = false
  override val quantifierFree = false
  override val linearArithmetic = false
  override val nonlinearArithmetic = false
  override val differentialArithmetic = false
  override val freeSortFunctionSymbols = false
}

/**
 * This logic does not yet provide an offical documentation, but has the following properties:
 * - Linear arithmetic
 * - Nonlinear arithmetic
 * - Differential logics
 *
 * This logic includes the following theories:
 * - Reals
 */
data object NRA : Logic {
  override val theories = setOf(Theories.CORE, Theories.REALS)
  override val datatypes = false
  override val quantifierFree = false
  override val linearArithmetic = true
  override val nonlinearArithmetic = true
  override val differentialArithmetic = true
  override val freeSortFunctionSymbols = false
}

/**
 * This logic does not yet provide an offical documentation, but has the following properties:
 * - Free sort and function symbols
 * - Quantifier free
 *
 * This logic includes the following theories:
 * - FixedSizeBitVectors
 * - FloatingPoint
 * - ArraysEx
 */
data object QF_AUFBVFP : Logic {
  override val theories =
      setOf(
          Theories.CORE,
          Theories.FIXED_SIZE_BIT_VECTORS,
          Theories.FLOATING_POINT,
          Theories.ARRAYS_EX,
      )
  override val datatypes = false
  override val quantifierFree = true
  override val linearArithmetic = false
  override val nonlinearArithmetic = false
  override val differentialArithmetic = false
  override val freeSortFunctionSymbols = true
}

/**
 * This logic does not yet provide an offical documentation, but has the following properties:
 * - Free sort and function symbols
 *
 * This logic includes the following theories:
 * - FixedSizeBitVectors
 * - FloatingPoint
 * - ArraysEx
 */
data object AUFBVFP : Logic {
  override val theories =
      setOf(
          Theories.CORE,
          Theories.FIXED_SIZE_BIT_VECTORS,
          Theories.FLOATING_POINT,
          Theories.ARRAYS_EX,
      )
  override val datatypes = false
  override val quantifierFree = false
  override val linearArithmetic = false
  override val nonlinearArithmetic = false
  override val differentialArithmetic = false
  override val freeSortFunctionSymbols = true
}

/**
 * Closed formulas built over an arbitrary expansion of the Ints signature with free sort and
 * function symbols.
 */
data object UFNIA : Logic {
  override val theories = setOf(Theories.CORE, Theories.INTS)
  override val datatypes = false
  override val quantifierFree = false
  override val linearArithmetic = true
  override val nonlinearArithmetic = true
  override val differentialArithmetic = true
  override val freeSortFunctionSymbols = true
}

/**
 * This logic does not yet provide an offical documentation, but has the following properties:
 * - Free sort and function symbols
 * - Quantifier free
 * - Linear arithmetic
 * - Nonlinear arithmetic
 * - Differential logics
 *
 * This logic includes the following theories:
 * - Ints
 */
data object QF_UFNIA : Logic {
  override val theories = setOf(Theories.CORE, Theories.INTS)
  override val datatypes = false
  override val quantifierFree = true
  override val linearArithmetic = true
  override val nonlinearArithmetic = true
  override val differentialArithmetic = true
  override val freeSortFunctionSymbols = true
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
  override val theories = setOf(Theories.CORE, Theories.REALS)
  override val datatypes = false
  override val quantifierFree = true
  override val linearArithmetic = false
  override val nonlinearArithmetic = false
  override val differentialArithmetic = true
  override val freeSortFunctionSymbols = false
}

/**
 * Closed quantifier-free formulas built over an arbitrary expansion of the Ints signature with free
 * constant symbols, but whose terms of sort Int are all linear, that is, have no occurrences of the
 * function symbols /, div, mod, and abs, and no occurrences of the function symbol *, except as
 * specified in the :extensions attribute.
 */
data object QF_LIA : Logic {
  override val theories = setOf(Theories.CORE, Theories.INTS)
  override val datatypes = false
  override val quantifierFree = true
  override val linearArithmetic = true
  override val nonlinearArithmetic = false
  override val differentialArithmetic = true
  override val freeSortFunctionSymbols = false
}

/**
 * This logic does not yet provide an offical documentation, but has the following properties:
 * - Quantifier free
 *
 * This logic includes the following theories:
 * - FixedSizeBitVectors
 * - FloatingPoint
 */
data object QF_BVFP : Logic {
  override val theories =
      setOf(Theories.CORE, Theories.FIXED_SIZE_BIT_VECTORS, Theories.FLOATING_POINT)
  override val datatypes = false
  override val quantifierFree = true
  override val linearArithmetic = false
  override val nonlinearArithmetic = false
  override val differentialArithmetic = false
  override val freeSortFunctionSymbols = false
}

/**
 * Closed formulas built over arbitrary expansions of the Ints and ArraysEx signatures with free
 * sort and function symbols, but with the following restrictions:
 * - all terms of sort Int are linear, that is, have no occurrences of the function symbols *, /,
 *   div, mod, and abs, except as specified in the :extensions attributes;
 * - all array terms have sort (Array Int Int).
 */
data object AUFLIA : Logic {
  override val theories = setOf(Theories.CORE, Theories.ARRAYS_EX, Theories.INTS)
  override val datatypes = false
  override val quantifierFree = false
  override val linearArithmetic = true
  override val nonlinearArithmetic = false
  override val differentialArithmetic = true
  override val freeSortFunctionSymbols = true
}

/**
 * Closed quantifier-free formulas built over an arbitrary expansion of the Ints signature with free
 * constant symbols.
 */
data object QF_NIA : Logic {
  override val theories = setOf(Theories.CORE, Theories.INTS)
  override val datatypes = false
  override val quantifierFree = true
  override val linearArithmetic = true
  override val nonlinearArithmetic = true
  override val differentialArithmetic = true
  override val freeSortFunctionSymbols = false
}

/**
 * This logic does not yet provide an offical documentation, but has the following properties:
 * - Free sort and function symbols
 * - Datatype support
 * - Quantifier free
 * - Linear arithmetic
 * - Differential logics
 *
 * This logic includes the following theories:
 * - Ints
 */
data object QF_UFDTLIA : Logic {
  override val theories = setOf(Theories.CORE, Theories.INTS)
  override val datatypes = true
  override val quantifierFree = true
  override val linearArithmetic = true
  override val nonlinearArithmetic = false
  override val differentialArithmetic = true
  override val freeSortFunctionSymbols = true
}

/**
 * This logic does not yet provide an offical documentation, but has the following properties:
 * - Free sort and function symbols
 * - Datatype support
 *
 * This logic includes the following theories:
 * - FixedSizeBitVectors
 */
data object UFBVDT : Logic {
  override val theories = setOf(Theories.CORE, Theories.FIXED_SIZE_BIT_VECTORS)
  override val datatypes = true
  override val quantifierFree = false
  override val linearArithmetic = false
  override val nonlinearArithmetic = false
  override val differentialArithmetic = false
  override val freeSortFunctionSymbols = true
}

/**
 * This logic does not yet provide an offical documentation, but has the following properties:
 * - Free sort and function symbols
 *
 * This logic includes the following theories:
 * - FixedSizeBitVectors
 */
data object UFBV : Logic {
  override val theories = setOf(Theories.CORE, Theories.FIXED_SIZE_BIT_VECTORS)
  override val datatypes = false
  override val quantifierFree = false
  override val linearArithmetic = false
  override val nonlinearArithmetic = false
  override val differentialArithmetic = false
  override val freeSortFunctionSymbols = true
}

/**
 * Closed quantifier-free formulas built over arbitrary expansions of the Reals signature with free
 * sort and function symbols, but containing only linear atoms, that is, atoms with no occurrences
 * of the function symbols * and /, except as specified the :extensions attribute.
 */
data object QF_UFLRA : Logic {
  override val theories = setOf(Theories.CORE, Theories.REALS)
  override val datatypes = false
  override val quantifierFree = true
  override val linearArithmetic = true
  override val nonlinearArithmetic = false
  override val differentialArithmetic = true
  override val freeSortFunctionSymbols = true
}

/**
 * This logic does not yet provide an offical documentation, but has the following properties:
 * - Quantifier free
 *
 * This logic includes the following theories:
 * - FloatingPoint
 */
data object QF_FP : Logic {
  override val theories = setOf(Theories.CORE, Theories.FLOATING_POINT)
  override val datatypes = false
  override val quantifierFree = true
  override val linearArithmetic = false
  override val nonlinearArithmetic = false
  override val differentialArithmetic = false
  override val freeSortFunctionSymbols = false
}

/**
 * This logic does not yet provide an offical documentation, but has the following properties:
 * - Quantifier free
 * - Linear arithmetic
 * - Nonlinear arithmetic
 * - Differential logics
 *
 * This logic includes the following theories:
 * - Ints
 * - Strings
 */
data object QF_SNIA : Logic {
  override val theories = setOf(Theories.CORE, Theories.INTS, Theories.STRINGS)
  override val datatypes = false
  override val quantifierFree = true
  override val linearArithmetic = true
  override val nonlinearArithmetic = true
  override val differentialArithmetic = true
  override val freeSortFunctionSymbols = false
}

/**
 * This logic does not yet provide an offical documentation, but has the following properties:
 * - Free sort and function symbols
 * - Datatype support
 * - Quantifier free
 * - Linear arithmetic
 * - Nonlinear arithmetic
 * - Differential logics
 *
 * This logic includes the following theories:
 * - Ints
 */
data object QF_UFDTNIA : Logic {
  override val theories = setOf(Theories.CORE, Theories.INTS)
  override val datatypes = true
  override val quantifierFree = true
  override val linearArithmetic = true
  override val nonlinearArithmetic = true
  override val differentialArithmetic = true
  override val freeSortFunctionSymbols = true
}

/**
 * This logic does not yet provide an offical documentation, but has the following properties:
 * - Quantifier free
 * - Linear arithmetic
 * - Differential logics
 *
 * This logic includes the following theories:
 * - FixedSizeBitVectors
 * - FloatingPoint
 * - Reals
 */
data object QF_BVFPLRA : Logic {
  override val theories =
      setOf(Theories.CORE, Theories.FIXED_SIZE_BIT_VECTORS, Theories.FLOATING_POINT, Theories.REALS)
  override val datatypes = false
  override val quantifierFree = true
  override val linearArithmetic = true
  override val nonlinearArithmetic = false
  override val differentialArithmetic = true
  override val freeSortFunctionSymbols = false
}

/**
 * This logic does not yet provide an offical documentation, but has the following properties:
 *
 * This logic includes the following theories:
 * - FixedSizeBitVectors
 * - ArraysEx
 */
data object ABV : Logic {
  override val theories = setOf(Theories.CORE, Theories.FIXED_SIZE_BIT_VECTORS, Theories.ARRAYS_EX)
  override val datatypes = false
  override val quantifierFree = false
  override val linearArithmetic = false
  override val nonlinearArithmetic = false
  override val differentialArithmetic = false
  override val freeSortFunctionSymbols = false
}

/**
 * Closed formulas built over arbitrary expansions of the Reals signature with free constant
 * symbols, but containing only linear atoms, that is, atoms with no occurrences of the function
 * symbols * and /, except as specified the :extensions attribute.
 */
data object LRA : Logic {
  override val theories = setOf(Theories.CORE, Theories.REALS)
  override val datatypes = false
  override val quantifierFree = false
  override val linearArithmetic = true
  override val nonlinearArithmetic = false
  override val differentialArithmetic = true
  override val freeSortFunctionSymbols = false
}

/**
 * This logic does not yet provide an offical documentation, but has the following properties:
 * - Free sort and function symbols
 * - Linear arithmetic
 * - Nonlinear arithmetic
 * - Differential logics
 *
 * This logic includes the following theories:
 * - Reals_Ints
 */
data object UFNIRA : Logic {
  override val theories = setOf(Theories.CORE, Theories.REALS_INTS)
  override val datatypes = false
  override val quantifierFree = false
  override val linearArithmetic = true
  override val nonlinearArithmetic = true
  override val differentialArithmetic = true
  override val freeSortFunctionSymbols = true
}

/**
 * This logic does not yet provide an offical documentation, but has the following properties:
 * - Free sort and function symbols
 * - Quantifier free
 *
 * This logic includes the following theories:
 * - FloatingPoint
 */
data object QF_UFFP : Logic {
  override val theories = setOf(Theories.CORE, Theories.FLOATING_POINT)
  override val datatypes = false
  override val quantifierFree = true
  override val linearArithmetic = false
  override val nonlinearArithmetic = false
  override val differentialArithmetic = false
  override val freeSortFunctionSymbols = true
}

/**
 * This logic does not yet provide an offical documentation, but has the following properties:
 * - Free sort and function symbols
 * - Datatype support
 * - Linear arithmetic
 * - Differential logics
 *
 * This logic includes the following theories:
 * - Reals_Ints
 */
data object UFDTLIRA : Logic {
  override val theories = setOf(Theories.CORE, Theories.REALS_INTS)
  override val datatypes = true
  override val quantifierFree = false
  override val linearArithmetic = true
  override val nonlinearArithmetic = false
  override val differentialArithmetic = true
  override val freeSortFunctionSymbols = true
}

/**
 * This logic does not yet provide an offical documentation, but has the following properties:
 * - Free sort and function symbols
 * - Linear arithmetic
 * - Differential logics
 *
 * This logic includes the following theories:
 * - Ints
 */
data object UFLIA : Logic {
  override val theories = setOf(Theories.CORE, Theories.INTS)
  override val datatypes = false
  override val quantifierFree = false
  override val linearArithmetic = true
  override val nonlinearArithmetic = false
  override val differentialArithmetic = true
  override val freeSortFunctionSymbols = true
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
  override val theories = setOf(Theories.CORE, Theories.ARRAYS_EX, Theories.REALS_INTS)
  override val datatypes = false
  override val quantifierFree = false
  override val linearArithmetic = true
  override val nonlinearArithmetic = false
  override val differentialArithmetic = true
  override val freeSortFunctionSymbols = true
}

/**
 * Closed formulas built over an arbitrary expansion of the Ints signature with free constant
 * symbols, but whose terms of sort Int are all linear, that is, have no occurrences of the function
 * symbols *, /, div, mod, and abs, except as specified the :extensions attribute.
 */
data object LIA : Logic {
  override val theories = setOf(Theories.CORE, Theories.INTS)
  override val datatypes = false
  override val quantifierFree = false
  override val linearArithmetic = true
  override val nonlinearArithmetic = false
  override val differentialArithmetic = true
  override val freeSortFunctionSymbols = false
}

/**
 * Closed quantifier-free formulas built over the FixedSizeBitVectors and ArraysEx signatures, with
 * the restriction that all array terms have sort of the form (Array (_ BitVec i) (_ BitVec j)) for
 * some i, j > 0.
 */
data object QF_ABV : Logic {
  override val theories = setOf(Theories.CORE, Theories.FIXED_SIZE_BIT_VECTORS, Theories.ARRAYS_EX)
  override val datatypes = false
  override val quantifierFree = true
  override val linearArithmetic = false
  override val nonlinearArithmetic = false
  override val differentialArithmetic = false
  override val freeSortFunctionSymbols = false
}

/**
 * Closed quantifier-free formulas built over an arbitrary expansion of the FixedSizeBitVectors and
 * ArraysEx signatures with free sort and function symbols, but with the restriction that all array
 * terms have sort of the form (Array (_ BitVec i) (_ BitVec j)) for some i, j > 0.
 */
data object QF_AUFBV : Logic {
  override val theories = setOf(Theories.CORE, Theories.FIXED_SIZE_BIT_VECTORS, Theories.ARRAYS_EX)
  override val datatypes = false
  override val quantifierFree = true
  override val linearArithmetic = false
  override val nonlinearArithmetic = false
  override val differentialArithmetic = false
  override val freeSortFunctionSymbols = true
}

/**
 * Closed quantifier-free formulas built over an arbitrary expansion of the FixedSizeBitVectors
 * signature with free constant symbols over the sorts (_ BitVec m) for 0 < m. Formulas in ite terms
 * must satisfy the same restriction as well, with the exception that they need not be closed
 * (because they may be in the scope of a let binder).
 */
data object QF_BV : Logic {
  override val theories = setOf(Theories.CORE, Theories.FIXED_SIZE_BIT_VECTORS)
  override val datatypes = false
  override val quantifierFree = true
  override val linearArithmetic = false
  override val nonlinearArithmetic = false
  override val differentialArithmetic = false
  override val freeSortFunctionSymbols = false
}

/**
 * Closed quantifier-free formulas built over arbitrary expansions of the Reals signature with free
 * constant symbols.
 */
data object QF_NRA : Logic {
  override val theories = setOf(Theories.CORE, Theories.REALS)
  override val datatypes = false
  override val quantifierFree = true
  override val linearArithmetic = true
  override val nonlinearArithmetic = true
  override val differentialArithmetic = true
  override val freeSortFunctionSymbols = false
}

/**
 * This logic does not yet provide an offical documentation, but has the following properties:
 * - Free sort and function symbols
 * - Datatype support
 * - Quantifier free
 *
 * This logic includes the following theories:
 */
data object QF_UFDT : Logic {
  override val theories = setOf(Theories.CORE)
  override val datatypes = true
  override val quantifierFree = true
  override val linearArithmetic = false
  override val nonlinearArithmetic = false
  override val differentialArithmetic = false
  override val freeSortFunctionSymbols = true
}

/**
 * This logic does not yet provide an offical documentation, but has the following properties:
 *
 * This logic includes the following theories:
 * - FixedSizeBitVectors
 */
data object BV : Logic {
  override val theories = setOf(Theories.CORE, Theories.FIXED_SIZE_BIT_VECTORS)
  override val datatypes = false
  override val quantifierFree = false
  override val linearArithmetic = false
  override val nonlinearArithmetic = false
  override val differentialArithmetic = false
  override val freeSortFunctionSymbols = false
}

/**
 * This logic does not yet provide an offical documentation, but has the following properties:
 * - Free sort and function symbols
 * - Datatype support
 * - Quantifier free
 * - Linear arithmetic
 * - Differential logics
 *
 * This logic includes the following theories:
 * - Reals_Ints
 */
data object QF_UFDTLIRA : Logic {
  override val theories = setOf(Theories.CORE, Theories.REALS_INTS)
  override val datatypes = true
  override val quantifierFree = true
  override val linearArithmetic = true
  override val nonlinearArithmetic = false
  override val differentialArithmetic = true
  override val freeSortFunctionSymbols = true
}

/**
 * This logic does not yet provide an offical documentation, but has the following properties:
 * - Free sort and function symbols
 * - Datatype support
 * - Linear arithmetic
 * - Nonlinear arithmetic
 * - Differential logics
 *
 * This logic includes the following theories:
 * - FixedSizeBitVectors
 * - ArraysEx
 * - Reals_Ints
 */
data object AUFBVDTNIRA : Logic {
  override val theories =
      setOf(Theories.CORE, Theories.FIXED_SIZE_BIT_VECTORS, Theories.ARRAYS_EX, Theories.REALS_INTS)
  override val datatypes = true
  override val quantifierFree = false
  override val linearArithmetic = true
  override val nonlinearArithmetic = true
  override val differentialArithmetic = true
  override val freeSortFunctionSymbols = true
}

/**
 * This logic does not yet provide an offical documentation, but has the following properties:
 * - Quantifier free
 * - Linear arithmetic
 * - Differential logics
 *
 * This logic includes the following theories:
 * - FixedSizeBitVectors
 * - FloatingPoint
 * - ArraysEx
 * - Reals
 */
data object QF_ABVFPLRA : Logic {
  override val theories =
      setOf(
          Theories.CORE,
          Theories.FIXED_SIZE_BIT_VECTORS,
          Theories.FLOATING_POINT,
          Theories.ARRAYS_EX,
          Theories.REALS,
      )
  override val datatypes = false
  override val quantifierFree = true
  override val linearArithmetic = true
  override val nonlinearArithmetic = false
  override val differentialArithmetic = true
  override val freeSortFunctionSymbols = false
}

/**
 * This logic does not yet provide an offical documentation, but has the following properties:
 * - Quantifier free
 * - Linear arithmetic
 * - Differential logics
 *
 * This logic includes the following theories:
 * - ArraysEx
 * - Ints
 */
data object QF_ALIA : Logic {
  override val theories = setOf(Theories.CORE, Theories.ARRAYS_EX, Theories.INTS)
  override val datatypes = false
  override val quantifierFree = true
  override val linearArithmetic = true
  override val nonlinearArithmetic = false
  override val differentialArithmetic = true
  override val freeSortFunctionSymbols = false
}

/**
 * This logic does not yet provide an offical documentation, but has the following properties:
 *
 * This logic includes the following theories:
 * - FixedSizeBitVectors
 * - FloatingPoint
 * - ArraysEx
 */
data object ABVFP : Logic {
  override val theories =
      setOf(
          Theories.CORE,
          Theories.FIXED_SIZE_BIT_VECTORS,
          Theories.FLOATING_POINT,
          Theories.ARRAYS_EX,
      )
  override val datatypes = false
  override val quantifierFree = false
  override val linearArithmetic = false
  override val nonlinearArithmetic = false
  override val differentialArithmetic = false
  override val freeSortFunctionSymbols = false
}

/**
 * This logic does not yet provide an offical documentation, but has the following properties:
 * - Free sort and function symbols
 * - Quantifier free
 * - Linear arithmetic
 * - Nonlinear arithmetic
 * - Differential logics
 *
 * This logic includes the following theories:
 * - ArraysEx
 * - Ints
 */
data object QF_AUFNIA : Logic {
  override val theories = setOf(Theories.CORE, Theories.ARRAYS_EX, Theories.INTS)
  override val datatypes = false
  override val quantifierFree = true
  override val linearArithmetic = true
  override val nonlinearArithmetic = true
  override val differentialArithmetic = true
  override val freeSortFunctionSymbols = true
}

/**
 * This logic does not yet provide an offical documentation, but has the following properties:
 * - Free sort and function symbols
 * - Datatype support
 * - Linear arithmetic
 * - Differential logics
 *
 * This logic includes the following theories:
 * - Ints
 */
data object UFDTLIA : Logic {
  override val theories = setOf(Theories.CORE, Theories.INTS)
  override val datatypes = true
  override val quantifierFree = false
  override val linearArithmetic = true
  override val nonlinearArithmetic = false
  override val differentialArithmetic = true
  override val freeSortFunctionSymbols = true
}

/**
 * Closed formulas built over arbitrary expansions of the Reals signature with free sort and
 * function symbols, but containing only linear atoms, that is, atoms with no occurrences of the
 * function symbols * and /, except as specified the :extensions attribute.
 */
data object UFLRA : Logic {
  override val theories = setOf(Theories.CORE, Theories.REALS)
  override val datatypes = false
  override val quantifierFree = false
  override val linearArithmetic = true
  override val nonlinearArithmetic = false
  override val differentialArithmetic = true
  override val freeSortFunctionSymbols = true
}

/**
 * This logic does not yet provide an offical documentation, but has the following properties:
 * - Linear arithmetic
 * - Nonlinear arithmetic
 * - Differential logics
 *
 * This logic includes the following theories:
 * - ArraysEx
 * - Ints
 */
data object ANIA : Logic {
  override val theories = setOf(Theories.CORE, Theories.ARRAYS_EX, Theories.INTS)
  override val datatypes = false
  override val quantifierFree = false
  override val linearArithmetic = true
  override val nonlinearArithmetic = true
  override val differentialArithmetic = true
  override val freeSortFunctionSymbols = false
}

/**
 * This logic does not yet provide an offical documentation, but has the following properties:
 * - Free sort and function symbols
 * - Datatype support
 * - Linear arithmetic
 * - Nonlinear arithmetic
 * - Differential logics
 *
 * This logic includes the following theories:
 * - FloatingPoint
 * - ArraysEx
 * - Reals_Ints
 */
data object AUFFPDTNIRA : Logic {
  override val theories =
      setOf(Theories.CORE, Theories.FLOATING_POINT, Theories.ARRAYS_EX, Theories.REALS_INTS)
  override val datatypes = true
  override val quantifierFree = false
  override val linearArithmetic = true
  override val nonlinearArithmetic = true
  override val differentialArithmetic = true
  override val freeSortFunctionSymbols = true
}

/**
 * This logic does not yet provide an offical documentation, but has the following properties:
 * - Free sort and function symbols
 * - Datatype support
 * - Linear arithmetic
 * - Differential logics
 *
 * This logic includes the following theories:
 * - FixedSizeBitVectors
 * - ArraysEx
 * - Ints
 */
data object AUFBVDTLIA : Logic {
  override val theories =
      setOf(Theories.CORE, Theories.FIXED_SIZE_BIT_VECTORS, Theories.ARRAYS_EX, Theories.INTS)
  override val datatypes = true
  override val quantifierFree = false
  override val linearArithmetic = true
  override val nonlinearArithmetic = false
  override val differentialArithmetic = true
  override val freeSortFunctionSymbols = true
}

/**
 * This logic does not yet provide an offical documentation, but has the following properties:
 * - Free sort and function symbols
 * - Datatype support
 * - Linear arithmetic
 * - Nonlinear arithmetic
 * - Differential logics
 *
 * This logic includes the following theories:
 * - FixedSizeBitVectors
 * - ArraysEx
 * - Ints
 */
data object AUFBVDTNIA : Logic {
  override val theories =
      setOf(Theories.CORE, Theories.FIXED_SIZE_BIT_VECTORS, Theories.ARRAYS_EX, Theories.INTS)
  override val datatypes = true
  override val quantifierFree = false
  override val linearArithmetic = true
  override val nonlinearArithmetic = true
  override val differentialArithmetic = true
  override val freeSortFunctionSymbols = true
}

/**
 * This logic does not yet provide an offical documentation, but has the following properties:
 * - Linear arithmetic
 * - Differential logics
 *
 * This logic includes the following theories:
 * - FixedSizeBitVectors
 * - FloatingPoint
 * - ArraysEx
 * - Reals
 */
data object ABVFPLRA : Logic {
  override val theories =
      setOf(
          Theories.CORE,
          Theories.FIXED_SIZE_BIT_VECTORS,
          Theories.FLOATING_POINT,
          Theories.ARRAYS_EX,
          Theories.REALS,
      )
  override val datatypes = false
  override val quantifierFree = false
  override val linearArithmetic = true
  override val nonlinearArithmetic = false
  override val differentialArithmetic = true
  override val freeSortFunctionSymbols = false
}

/**
 * This logic does not yet provide an offical documentation, but has the following properties:
 * - Linear arithmetic
 * - Differential logics
 *
 * This logic includes the following theories:
 * - ArraysEx
 * - Ints
 */
data object ALIA : Logic {
  override val theories = setOf(Theories.CORE, Theories.ARRAYS_EX, Theories.INTS)
  override val datatypes = false
  override val quantifierFree = false
  override val linearArithmetic = true
  override val nonlinearArithmetic = false
  override val differentialArithmetic = true
  override val freeSortFunctionSymbols = false
}

/**
 * This logic does not yet provide an offical documentation, but has the following properties:
 * - Free sort and function symbols
 * - Datatype support
 * - Linear arithmetic
 * - Nonlinear arithmetic
 * - Differential logics
 *
 * This logic includes the following theories:
 * - ArraysEx
 * - Reals_Ints
 */
data object AUFDTNIRA : Logic {
  override val theories = setOf(Theories.CORE, Theories.ARRAYS_EX, Theories.REALS_INTS)
  override val datatypes = true
  override val quantifierFree = false
  override val linearArithmetic = true
  override val nonlinearArithmetic = true
  override val differentialArithmetic = true
  override val freeSortFunctionSymbols = true
}

/**
 * This logic does not yet provide an offical documentation, but has the following properties:
 * - Free sort and function symbols
 * - Datatype support
 * - Linear arithmetic
 * - Differential logics
 *
 * This logic includes the following theories:
 * - ArraysEx
 * - Reals_Ints
 */
data object AUFDTLIRA : Logic {
  override val theories = setOf(Theories.CORE, Theories.ARRAYS_EX, Theories.REALS_INTS)
  override val datatypes = true
  override val quantifierFree = false
  override val linearArithmetic = true
  override val nonlinearArithmetic = false
  override val differentialArithmetic = true
  override val freeSortFunctionSymbols = true
}

/**
 * Closed formulas built over arbitrary expansions of the Reals_Ints and ArraysEx signatures with
 * free sort and function symbols.
 */
data object AUFNIRA : Logic {
  override val theories = setOf(Theories.CORE, Theories.ARRAYS_EX, Theories.REALS_INTS)
  override val datatypes = false
  override val quantifierFree = false
  override val linearArithmetic = true
  override val nonlinearArithmetic = true
  override val differentialArithmetic = true
  override val freeSortFunctionSymbols = true
}

/**
 * This logic does not yet provide an offical documentation, but has the following properties:
 * - Linear arithmetic
 * - Differential logics
 *
 * This logic includes the following theories:
 * - FixedSizeBitVectors
 * - FloatingPoint
 * - Reals
 */
data object BVFPLRA : Logic {
  override val theories =
      setOf(Theories.CORE, Theories.FIXED_SIZE_BIT_VECTORS, Theories.FLOATING_POINT, Theories.REALS)
  override val datatypes = false
  override val quantifierFree = false
  override val linearArithmetic = true
  override val nonlinearArithmetic = false
  override val differentialArithmetic = true
  override val freeSortFunctionSymbols = false
}

/**
 * This logic does not yet provide an offical documentation, but has the following properties:
 * - Linear arithmetic
 * - Differential logics
 *
 * This logic includes the following theories:
 * - FloatingPoint
 * - Reals
 */
data object FPLRA : Logic {
  override val theories = setOf(Theories.CORE, Theories.FLOATING_POINT, Theories.REALS)
  override val datatypes = false
  override val quantifierFree = false
  override val linearArithmetic = true
  override val nonlinearArithmetic = false
  override val differentialArithmetic = true
  override val freeSortFunctionSymbols = false
}

/**
 * Closed quantifier-free formulas built over arbitrary expansions of the Ints and ArraysEx
 * signatures with free sort and function symbols, but with the following restrictions:
 * - all terms of sort Int are linear, that is, have no occurrences of the function symbols *, /,
 *   div, mod, and abs, except as specified in the :extensions attributes;
 * - all array terms have sort (Array Int Int).
 */
data object QF_AUFLIA : Logic {
  override val theories = setOf(Theories.CORE, Theories.ARRAYS_EX, Theories.INTS)
  override val datatypes = false
  override val quantifierFree = true
  override val linearArithmetic = true
  override val nonlinearArithmetic = false
  override val differentialArithmetic = true
  override val freeSortFunctionSymbols = true
}

/**
 * This logic does not yet provide an offical documentation, but has the following properties:
 * - Quantifier free
 * - Linear arithmetic
 * - Nonlinear arithmetic
 * - Differential logics
 *
 * This logic includes the following theories:
 * - Reals_Ints
 */
data object QF_NIRA : Logic {
  override val theories = setOf(Theories.CORE, Theories.REALS_INTS)
  override val datatypes = false
  override val quantifierFree = true
  override val linearArithmetic = true
  override val nonlinearArithmetic = true
  override val differentialArithmetic = true
  override val freeSortFunctionSymbols = false
}

/**
 * This logic does not yet provide an offical documentation, but has the following properties:
 *
 * This logic includes the following theories:
 * - FloatingPoint
 */
data object FP : Logic {
  override val theories = setOf(Theories.CORE, Theories.FLOATING_POINT)
  override val datatypes = false
  override val quantifierFree = false
  override val linearArithmetic = false
  override val nonlinearArithmetic = false
  override val differentialArithmetic = false
  override val freeSortFunctionSymbols = false
}

/**
 * This logic does not yet provide an offical documentation, but has the following properties:
 * - Quantifier free
 *
 * This logic includes the following theories:
 * - FixedSizeBitVectors
 * - FloatingPoint
 * - ArraysEx
 */
data object QF_ABVFP : Logic {
  override val theories =
      setOf(
          Theories.CORE,
          Theories.FIXED_SIZE_BIT_VECTORS,
          Theories.FLOATING_POINT,
          Theories.ARRAYS_EX,
      )
  override val datatypes = false
  override val quantifierFree = true
  override val linearArithmetic = false
  override val nonlinearArithmetic = false
  override val differentialArithmetic = false
  override val freeSortFunctionSymbols = false
}

/**
 * This logic does not yet provide an offical documentation, but has the following properties:
 * - Linear arithmetic
 * - Nonlinear arithmetic
 * - Differential logics
 *
 * This logic includes the following theories:
 * - Ints
 */
data object NIA : Logic {
  override val theories = setOf(Theories.CORE, Theories.INTS)
  override val datatypes = false
  override val quantifierFree = false
  override val linearArithmetic = true
  override val nonlinearArithmetic = true
  override val differentialArithmetic = true
  override val freeSortFunctionSymbols = false
}

/**
 * This logic does not yet provide an offical documentation, but has the following properties:
 * - Quantifier free
 *
 * This logic includes the following theories:
 * - Strings
 */
data object QF_S : Logic {
  override val theories = setOf(Theories.CORE, Theories.STRINGS)
  override val datatypes = false
  override val quantifierFree = true
  override val linearArithmetic = false
  override val nonlinearArithmetic = false
  override val differentialArithmetic = false
  override val freeSortFunctionSymbols = false
}

/**
 * This logic does not yet provide an offical documentation, but has the following properties:
 * - Free sort and function symbols
 * - Datatype support
 * - Linear arithmetic
 * - Nonlinear arithmetic
 * - Differential logics
 *
 * This logic includes the following theories:
 * - FloatingPoint
 * - Reals_Ints
 */
data object UFFPDTNIRA : Logic {
  override val theories = setOf(Theories.CORE, Theories.FLOATING_POINT, Theories.REALS_INTS)
  override val datatypes = true
  override val quantifierFree = false
  override val linearArithmetic = true
  override val nonlinearArithmetic = true
  override val differentialArithmetic = true
  override val freeSortFunctionSymbols = true
}

/**
 * This logic does not yet provide an offical documentation, but has the following properties:
 * - Quantifier free
 * - Linear arithmetic
 * - Nonlinear arithmetic
 * - Differential logics
 *
 * This logic includes the following theories:
 * - ArraysEx
 * - Ints
 */
data object QF_ANIA : Logic {
  override val theories = setOf(Theories.CORE, Theories.ARRAYS_EX, Theories.INTS)
  override val datatypes = false
  override val quantifierFree = true
  override val linearArithmetic = true
  override val nonlinearArithmetic = true
  override val differentialArithmetic = true
  override val freeSortFunctionSymbols = false
}

/**
 * Closed quantifier-free formulas built over an arbitrary expansion of the ArraysEx signature with
 * free sort and constant symbols.
 */
data object QF_AX : Logic {
  override val theories = setOf(Theories.CORE, Theories.ARRAYS_EX)
  override val datatypes = false
  override val quantifierFree = true
  override val linearArithmetic = false
  override val nonlinearArithmetic = false
  override val differentialArithmetic = false
  override val freeSortFunctionSymbols = false
}

/**
 * This logic does not yet provide an offical documentation, but has the following properties:
 * - Free sort and function symbols
 *
 * This logic includes the following theories:
 * - FixedSizeBitVectors
 * - ArraysEx
 */
data object AUFBV : Logic {
  override val theories = setOf(Theories.CORE, Theories.FIXED_SIZE_BIT_VECTORS, Theories.ARRAYS_EX)
  override val datatypes = false
  override val quantifierFree = false
  override val linearArithmetic = false
  override val nonlinearArithmetic = false
  override val differentialArithmetic = false
  override val freeSortFunctionSymbols = true
}

/**
 * This logic does not yet provide an offical documentation, but has the following properties:
 * - Free sort and function symbols
 * - Datatype support
 * - Linear arithmetic
 * - Differential logics
 *
 * This logic includes the following theories:
 * - ArraysEx
 * - Ints
 */
data object AUFDTLIA : Logic {
  override val theories = setOf(Theories.CORE, Theories.ARRAYS_EX, Theories.INTS)
  override val datatypes = true
  override val quantifierFree = false
  override val linearArithmetic = true
  override val nonlinearArithmetic = false
  override val differentialArithmetic = true
  override val freeSortFunctionSymbols = true
}

/**
 * This logic does not yet provide an offical documentation, but has the following properties:
 * - Free sort and function symbols
 * - Linear arithmetic
 * - Differential logics
 *
 * This logic includes the following theories:
 * - FixedSizeBitVectors
 * - Ints
 */
data object UFBVLIA : Logic {
  override val theories = setOf(Theories.CORE, Theories.FIXED_SIZE_BIT_VECTORS, Theories.INTS)
  override val datatypes = false
  override val quantifierFree = false
  override val linearArithmetic = true
  override val nonlinearArithmetic = false
  override val differentialArithmetic = true
  override val freeSortFunctionSymbols = true
}

/**
 * This logic does not yet provide an offical documentation, but has the following properties:
 * - Free sort and function symbols
 * - Datatype support
 *
 * This logic includes the following theories:
 */
data object UFDT : Logic {
  override val theories = setOf(Theories.CORE)
  override val datatypes = true
  override val quantifierFree = false
  override val linearArithmetic = false
  override val nonlinearArithmetic = false
  override val differentialArithmetic = false
  override val freeSortFunctionSymbols = true
}

/**
 * This logic does not yet provide an offical documentation, but has the following properties:
 * - Datatype support
 * - Quantifier free
 *
 * This logic includes the following theories:
 */
data object QF_DT : Logic {
  override val theories = setOf(Theories.CORE)
  override val datatypes = true
  override val quantifierFree = true
  override val linearArithmetic = false
  override val nonlinearArithmetic = false
  override val differentialArithmetic = false
  override val freeSortFunctionSymbols = false
}

/**
 * This logic does not yet provide an offical documentation, but has the following properties:
 * - Quantifier free
 * - Linear arithmetic
 * - Differential logics
 *
 * This logic includes the following theories:
 * - Ints
 * - Strings
 */
data object QF_SLIA : Logic {
  override val theories = setOf(Theories.CORE, Theories.INTS, Theories.STRINGS)
  override val datatypes = false
  override val quantifierFree = true
  override val linearArithmetic = true
  override val nonlinearArithmetic = false
  override val differentialArithmetic = true
  override val freeSortFunctionSymbols = false
}

/**
 * Closed quantifier-free formulas built over an arbitrary expansion of the Core signature with free
 * sort and function symbols.
 */
data object QF_UF : Logic {
  override val theories = setOf(Theories.CORE)
  override val datatypes = false
  override val quantifierFree = true
  override val linearArithmetic = false
  override val nonlinearArithmetic = false
  override val differentialArithmetic = false
  override val freeSortFunctionSymbols = true
}

/**
 * Closed quantifier-free formulas built over arbitrary expansions of the FixedSizeBitVectors
 * signature with free sort and function symbols.
 */
data object QF_UFBV : Logic {
  override val theories = setOf(Theories.CORE, Theories.FIXED_SIZE_BIT_VECTORS)
  override val datatypes = false
  override val quantifierFree = true
  override val linearArithmetic = false
  override val nonlinearArithmetic = false
  override val differentialArithmetic = false
  override val freeSortFunctionSymbols = true
}

/**
 * This logic does not yet provide an offical documentation, but has the following properties:
 * - Free sort and function symbols
 * - Datatype support
 * - Linear arithmetic
 * - Nonlinear arithmetic
 * - Differential logics
 *
 * This logic includes the following theories:
 * - Ints
 */
data object UFDTNIA : Logic {
  override val theories = setOf(Theories.CORE, Theories.INTS)
  override val datatypes = true
  override val quantifierFree = false
  override val linearArithmetic = true
  override val nonlinearArithmetic = true
  override val differentialArithmetic = true
  override val freeSortFunctionSymbols = true
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
  override val theories = setOf(Theories.CORE, Theories.INTS)
  override val datatypes = false
  override val quantifierFree = true
  override val linearArithmetic = false
  override val nonlinearArithmetic = false
  override val differentialArithmetic = true
  override val freeSortFunctionSymbols = false
}

/**
 * This logic does not yet provide an offical documentation, but has the following properties:
 * - Free sort and function symbols
 * - Linear arithmetic
 * - Nonlinear arithmetic
 * - Differential logics
 *
 * This logic includes the following theories:
 * - ArraysEx
 * - Ints
 */
data object AUFNIA : Logic {
  override val theories = setOf(Theories.CORE, Theories.ARRAYS_EX, Theories.INTS)
  override val datatypes = false
  override val quantifierFree = false
  override val linearArithmetic = true
  override val nonlinearArithmetic = true
  override val differentialArithmetic = true
  override val freeSortFunctionSymbols = true
}

/**
 * This logic does not yet provide an offical documentation, but has the following properties:
 * - Free sort and function symbols
 *
 * This logic includes the following theories:
 * - FixedSizeBitVectors
 * - FloatingPoint
 */
data object UFBVFP : Logic {
  override val theories =
      setOf(Theories.CORE, Theories.FIXED_SIZE_BIT_VECTORS, Theories.FLOATING_POINT)
  override val datatypes = false
  override val quantifierFree = false
  override val linearArithmetic = false
  override val nonlinearArithmetic = false
  override val differentialArithmetic = false
  override val freeSortFunctionSymbols = true
}

/**
 * This logic does not yet provide an offical documentation, but has the following properties:
 * - Free sort and function symbols
 * - Datatype support
 * - Linear arithmetic
 * - Nonlinear arithmetic
 * - Differential logics
 *
 * This logic includes the following theories:
 * - Reals_Ints
 */
data object UFDTNIRA : Logic {
  override val theories = setOf(Theories.CORE, Theories.REALS_INTS)
  override val datatypes = true
  override val quantifierFree = false
  override val linearArithmetic = true
  override val nonlinearArithmetic = true
  override val differentialArithmetic = true
  override val freeSortFunctionSymbols = true
}

/**
 * This logic does not yet provide an offical documentation, but has the following properties:
 * - Free sort and function symbols
 * - Differential logics
 *
 * This logic includes the following theories:
 */
data object UFIDL : Logic {
  override val theories = setOf(Theories.CORE, Theories.INTS)
  override val datatypes = false
  override val quantifierFree = false
  override val linearArithmetic = false
  override val nonlinearArithmetic = false
  override val differentialArithmetic = true
  override val freeSortFunctionSymbols = true
}

/**
 * Closed quantifier-free formulas built over arbitrary expansions of the Reals signature with free
 * constant symbols, but containing only linear atoms, that is, atoms with no occurrences of the
 * function symbols * and /, except as specified the :extensions attribute.
 */
data object QF_LRA : Logic {
  override val theories = setOf(Theories.CORE, Theories.REALS)
  override val datatypes = false
  override val quantifierFree = true
  override val linearArithmetic = true
  override val nonlinearArithmetic = false
  override val differentialArithmetic = true
  override val freeSortFunctionSymbols = false
}

/**
 * This logic does not yet provide an offical documentation, but has the following properties:
 * - Free sort and function symbols
 * - Datatype support
 * - Quantifier free
 *
 * This logic includes the following theories:
 * - FixedSizeBitVectors
 */
data object QF_UFBVDT : Logic {
  override val theories = setOf(Theories.CORE, Theories.FIXED_SIZE_BIT_VECTORS)
  override val datatypes = true
  override val quantifierFree = true
  override val linearArithmetic = false
  override val nonlinearArithmetic = false
  override val differentialArithmetic = false
  override val freeSortFunctionSymbols = true
}

/**
 * This logic does not yet provide an offical documentation, but has the following properties:
 * - Free sort and function symbols
 * - Datatype support
 * - Quantifier free
 * - Linear arithmetic
 * - Nonlinear arithmetic
 * - Differential logics
 *
 * This logic includes the following theories:
 * - FloatingPoint
 * - Reals_Ints
 */
data object QF_UFFPDTNIRA : Logic {
  override val theories = setOf(Theories.CORE, Theories.FLOATING_POINT, Theories.REALS_INTS)
  override val datatypes = true
  override val quantifierFree = true
  override val linearArithmetic = true
  override val nonlinearArithmetic = true
  override val differentialArithmetic = true
  override val freeSortFunctionSymbols = true
}

/**
 * Closed quantifier-free formulas built over arbitrary expansions of the Ints signatures with free
 * sort and function symbols, but with the following restrictions:
 * - all terms of sort Int are linear, that is, have no occurrences of the function symbols *, /,
 *   div, mod, and abs, except as specified in the :extensions attributes;
 */
data object QF_UFLIA : Logic {
  override val theories = setOf(Theories.CORE, Theories.INTS)
  override val datatypes = false
  override val quantifierFree = true
  override val linearArithmetic = true
  override val nonlinearArithmetic = false
  override val differentialArithmetic = true
  override val freeSortFunctionSymbols = true
}

/**
 * This logic does not yet provide an offical documentation, but has the following properties:
 * - Free sort and function symbols
 *
 * This logic includes the following theories:
 */
data object UF : Logic {
  override val theories = setOf(Theories.CORE)
  override val datatypes = false
  override val quantifierFree = false
  override val linearArithmetic = false
  override val nonlinearArithmetic = false
  override val differentialArithmetic = false
  override val freeSortFunctionSymbols = true
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
  override val theories = setOf(Theories.CORE, Theories.INTS)
  override val datatypes = false
  override val quantifierFree = true
  override val linearArithmetic = false
  override val nonlinearArithmetic = false
  override val differentialArithmetic = true
  override val freeSortFunctionSymbols = true
}

/**
 * Closed quantifier-free formulas built over arbitrary expansions of the Reals signature with free
 * sort and function symbols.
 */
data object QF_UFNRA : Logic {
  override val theories = setOf(Theories.CORE, Theories.REALS)
  override val datatypes = false
  override val quantifierFree = true
  override val linearArithmetic = true
  override val nonlinearArithmetic = true
  override val differentialArithmetic = true
  override val freeSortFunctionSymbols = true
}

/**
 * This logic does not yet provide an offical documentation, but has the following properties:
 * - Quantifier free
 * - Linear arithmetic
 * - Differential logics
 *
 * This logic includes the following theories:
 * - FloatingPoint
 * - Reals
 */
data object QF_FPLRA : Logic {
  override val theories = setOf(Theories.CORE, Theories.FLOATING_POINT, Theories.REALS)
  override val datatypes = false
  override val quantifierFree = true
  override val linearArithmetic = true
  override val nonlinearArithmetic = false
  override val differentialArithmetic = true
  override val freeSortFunctionSymbols = false
}

/**
 * This logic does not yet provide an offical documentation, but has the following properties:
 * - Quantifier free
 * - Linear arithmetic
 * - Differential logics
 *
 * This logic includes the following theories:
 * - Reals_Ints
 */
data object QF_LIRA : Logic {
  override val theories = setOf(Theories.CORE, Theories.REALS_INTS)
  override val datatypes = false
  override val quantifierFree = true
  override val linearArithmetic = true
  override val nonlinearArithmetic = false
  override val differentialArithmetic = true
  override val freeSortFunctionSymbols = false
}

data object QF_ASLIA : Logic {
  override val theories = setOf(Theories.CORE, Theories.ARRAYS_EX, Theories.STRINGS, Theories.INTS)
  override val datatypes = false
  override val quantifierFree = true
  override val linearArithmetic = true
  override val nonlinearArithmetic = false
  override val differentialArithmetic = true
  override val freeSortFunctionSymbols = false
}
