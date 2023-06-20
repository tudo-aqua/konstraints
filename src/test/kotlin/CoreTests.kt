import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.TestInstance
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.Arguments.arguments
import org.junit.jupiter.params.provider.MethodSource
import java.util.stream.Stream

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class CoreTests {
    private val A = BasicExpression("A", BoolSort)
    private val B = BasicExpression("B", BoolSort)
    private val C = BasicExpression("C", BoolSort)

    @ParameterizedTest
    @MethodSource("testCoreSerializationParameterization")
    fun testCoreSerialization(expected : String, expression : Expression<BoolSort>) {
        Assertions.assertEquals(expected, expression.toString())
    }

    private fun testCoreSerializationParameterization() : Stream<Arguments> {
        return Stream.of(
            arguments("true", True),
            arguments("false", False),
            arguments("(not A)", Not(A)),
            arguments("(=> A B)", Implies(A, B)),
            arguments("(=> A B C)", Implies(A, B, C)),
            arguments("(and A B)", And(A, B)),
            arguments("(and A B C)", And(A, B, C)),
            arguments("(or A B)", Or(A, B)),
            arguments("(or A B C)", Or(A, B, C)),
            arguments("(xor A B)", XOr(A, B)),
            arguments("(xor A B C)", XOr(A, B, C)),
            arguments("(= A B)", Equals(A, B)),
            arguments("(= A B C)", Equals(A, B, C)),
            arguments("(distinct A B)", Distinct(A, B)),
            arguments("(distinct A B C)", Distinct(A, B, C)),
            arguments("(ite A B C)", Ite(A, B, C)),
            arguments("(and A (or B C))", And(A, Or(B, C))),
            arguments("(and (or A B) C)", And(Or(A, B), C))
        )
    }
}