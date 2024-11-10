package tools.aqua.konstraints.smt

import java.math.BigDecimal

sealed interface SpecConstant
data class StringConstant(val string: String) : SpecConstant
data class NumeralConstant(val numeral: String) : SpecConstant

/* BinaryConstant of the form #b followed by a non-empty sequence of 0 and 1 characters */
data class BinaryConstant(val binary: String) : SpecConstant {
  /* Number of bits for this binary */
  val bits = binary.length - 2
}

/* Hexadecimal constant of the form
 * #x followed by a non-empty sequence of digits and letters from A to F , capitalized or not
 */
data class HexConstant(val hexadecimal: String) : SpecConstant {
  /* Number of bits for this hexadecimal */
  val bits = (hexadecimal.length - 2) * 4
}

data class DecimalConstant(val decimal: BigDecimal) : SpecConstant