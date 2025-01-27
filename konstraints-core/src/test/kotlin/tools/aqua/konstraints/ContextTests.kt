package tools.aqua.konstraints

import tools.aqua.konstraints.dsl.*
import tools.aqua.konstraints.smt.*
import tools.aqua.konstraints.theories.*
import org.junit.jupiter.api.*
import org.junit.jupiter.api.Assertions.*
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.Arguments.arguments
import org.junit.jupiter.params.provider.MethodSource
import java.util.stream.Stream

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class ContextTests {
    val boolFunc1 = SMTFunction0("A".symbol(), BoolSort, null)
    val boolFunc2 = SMTFunction2("B".symbol(), BoolSort, BVSort(8), BVSort(8), null)
    val boolFunc2Overloaded = SMTFunction2("B".symbol(), BoolSort, BVSort(16), BVSort(16), null)

    @ParameterizedTest
    @MethodSource("getContextAndNames")
    fun testContains(context: Context, func: String) {
        assertTrue(context.contains(func))
    }

    private fun getContextAndNames() : Stream<Arguments> = Stream.of(
        arguments(createContext(), "A"),
        arguments(createContext(), "B")
    )

    @Test
    fun test() {
        assertFalse(boolFunc2 == boolFunc2Overloaded)
    }

    @ParameterizedTest
    @MethodSource("getContextAndFunctions")
    fun testGetFunction(context: Context, func: SMTFunction<*>) {
        assertTrue(context.getFunc(func.name, func.sort, func.parameters) == func)
    }

    private fun getContextAndFunctions() : Stream<Arguments> = Stream.of(
        arguments(createContext(), boolFunc1),
        arguments(createContext(), boolFunc2),
        arguments(createContext(), boolFunc2Overloaded)
    )

    @ParameterizedTest
    @MethodSource("getContextAndIllegalFunctions")
    fun testAddFails(context: Context, func: SMTFunction<*>) {
        assertThrows<IllegalArgumentException> {
            context.addFun(func)
        }
    }

    private fun getContextAndIllegalFunctions() : Stream<Arguments> = Stream.of(
        arguments(createContext(), boolFunc1),
        arguments(createContext(), boolFunc2),
        arguments(createContext(), boolFunc2Overloaded),
    )

    @ParameterizedTest
    @MethodSource("getContextAndIllegalNameFunctions")
    fun testAddIllegalNameFails(context: Context, func: SMTFunction<*>) {
        assertThrows<IllegalArgumentException> {
            context.addFun(func)
        }
    }

    private fun getContextAndIllegalNameFunctions() : Stream<Arguments> = Stream.of(
        arguments(createContext(), SMTFunction0("and".symbol(), BoolSort, null)),
        arguments(createContext(), SMTFunction0("true".symbol(), BoolSort, null)),
        arguments(createContext(), SMTFunction0("distinct".symbol(), BoolSort, null)),
        arguments(createContext(), SMTFunction0("bvadd".symbol(), BoolSort, null)),
        arguments(createContext(), SMTFunction0("extract".symbol(), BoolSort, null))
    )

    @Test
    fun testPopFailsOnContextWithOnlyOneLevel() {
        val context = createContext()

        assertThrows<IllegalArgumentException> { context.pop(1) }
    }

    @ParameterizedTest
    @MethodSource("getContextAndNewFunction")
    fun testPopRemovesFunction(context: Context, func: SMTFunction<*>) {
        context.push {
            addFun(func)

            assertTrue(context.contains(func.name))
        }

        assertFalse(context.contains(func.name))
    }

    private fun getContextAndNewFunction() = Stream.of(
        arguments(createContext(), SMTFunction0("C".symbol(), BoolSort, null)),
    )

    private fun createContext() : Context {
        val context = Context()
        context.setLogic(QF_BV)

        context.addFun(boolFunc1)
        context.addFun(boolFunc2)

        return context
    }
}