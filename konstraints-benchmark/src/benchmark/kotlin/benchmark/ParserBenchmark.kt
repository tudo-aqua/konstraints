package benchmark

import kotlinx.benchmark.Benchmark
import kotlinx.benchmark.BenchmarkMode
import kotlinx.benchmark.BenchmarkTimeUnit
import kotlinx.benchmark.Measurement
import kotlinx.benchmark.Mode
import kotlinx.benchmark.OutputTimeUnit
import kotlinx.benchmark.Scope
import kotlinx.benchmark.Warmup
import org.openjdk.jmh.annotations.State
import tools.aqua.konstraints.parser.Parser
import tools.aqua.konstraints.smt.AnnotatedExpression
import tools.aqua.konstraints.smt.Assert
import tools.aqua.konstraints.smt.ExistsExpression
import tools.aqua.konstraints.smt.Expression
import tools.aqua.konstraints.smt.ForallExpression
import tools.aqua.konstraints.smt.LetExpression
import tools.aqua.konstraints.smt.SMTProgram
import tools.aqua.konstraints.util.StackOperation
import tools.aqua.konstraints.util.StackOperationType
import java.util.concurrent.TimeUnit
import kotlin.DeepRecursiveFunction

@State(Scope.Benchmark)
class ParserBenchmark {
    private val qfsliaSmall = Parser(javaClass.getResourceAsStream("/benchmark/01345ce7f43a623122a1d9ab0c16fa071a19d8d238535428051e63b4.smt2")!!.bufferedReader())
    private val qfsliaMedium = Parser(javaClass.getResourceAsStream("/benchmark/18d12f8794d1f00b4b8227d322a06cfa43b565042cba6a8877515fb7.smt2")!!.bufferedReader())
    private val qfsliaLarge = Parser(javaClass.getResourceAsStream("/benchmark/354180e356896fe27745d49b6aeb7e365e7c7f5a054c3bc1d274990e.smt2")!!.bufferedReader())
    private val qfbvSmall = Parser(javaClass.getResourceAsStream("/benchmark/bench_10559.smt2")!!.bufferedReader())
    private val qfbvMedium = Parser(javaClass.getResourceAsStream("/benchmark/bench_8378.smt2")!!.bufferedReader())
    private val qfbvLarge = Parser(javaClass.getResourceAsStream("/benchmark/bench_9140.smt2")!!.bufferedReader())

    @Benchmark
    @BenchmarkMode(Mode.AverageTime)
    @OutputTimeUnit(TimeUnit.MICROSECONDS)
    @Warmup(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
    @Measurement(iterations = 20, time = 5, timeUnit = TimeUnit.SECONDS)
    fun qfsLiaSmallDeepContextCheckAverage() {
        qfsliaSmall.commands.filterIsInstance<Assert>().forEach { assert ->
            qfsliaSmall.deepContextCheck(assert.expr)
        }
    }

    @Benchmark
    @BenchmarkMode(Mode.AverageTime)
    @OutputTimeUnit(TimeUnit.MICROSECONDS)
    @Warmup(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
    @Measurement(iterations = 20, time = 5, timeUnit = TimeUnit.SECONDS)
    fun qfsLiaSmallShallowContextCheckAverage() {
        qfsliaSmall.commands.filterIsInstance<Assert>().forEach { assert ->
            qfsliaSmall.shallowContextCheck(assert.expr)
        }
    }

    @Benchmark
    @BenchmarkMode(Mode.AverageTime)
    @OutputTimeUnit(TimeUnit.MICROSECONDS)
    @Warmup(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
    @Measurement(iterations = 20, time = 5, timeUnit = TimeUnit.SECONDS)
    fun qfsLiaSmallIterativeContextCheckAverage() {
        qfsliaSmall.commands.filterIsInstance<Assert>().forEach { assert ->
            qfsliaSmall.iterativeContextCheck(assert.expr)
        }
    }

    @Benchmark
    @BenchmarkMode(Mode.AverageTime)
    @OutputTimeUnit(TimeUnit.MICROSECONDS)
    @Warmup(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
    @Measurement(iterations = 20, time = 5, timeUnit = TimeUnit.SECONDS)
    fun qfbvSmallDeepContextCheckAverage() {
        qfbvSmall.commands.filterIsInstance<Assert>().forEach { assert ->
            qfbvSmall.deepContextCheck(assert.expr)
        }
    }

    @Benchmark
    @BenchmarkMode(Mode.AverageTime)
    @OutputTimeUnit(TimeUnit.MICROSECONDS)
    @Warmup(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
    @Measurement(iterations = 20, time = 5, timeUnit = TimeUnit.SECONDS)
    fun qfbvSmallShallowContextCheckAverage() {
        qfbvSmall.commands.filterIsInstance<Assert>().forEach { assert ->
            qfbvSmall.shallowContextCheck(assert.expr)
        }
    }

    @Benchmark
    @BenchmarkMode(Mode.AverageTime)
    @OutputTimeUnit(TimeUnit.MICROSECONDS)
    @Warmup(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
    @Measurement(iterations = 20, time = 5, timeUnit = TimeUnit.SECONDS)
    fun qfbvSmallIterativeContextCheckAverage() {
        qfbvSmall.commands.filterIsInstance<Assert>().forEach { assert ->
            qfbvSmall.iterativeContextCheck(assert.expr)
        }
    }

    @Benchmark
    @BenchmarkMode(Mode.AverageTime)
    @OutputTimeUnit(TimeUnit.MILLISECONDS)
    @Warmup(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
    @Measurement(iterations = 20, time = 5, timeUnit = TimeUnit.SECONDS)
    fun qfsliaMediumDeepContextCheckAverage() {
        qfsliaMedium.commands.filterIsInstance<Assert>().forEach { assert ->
            qfsliaMedium.deepContextCheck(assert.expr)
        }
    }

    @Benchmark
    @BenchmarkMode(Mode.AverageTime)
    @OutputTimeUnit(TimeUnit.MILLISECONDS)
    @Warmup(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
    @Measurement(iterations = 20, time = 5, timeUnit = TimeUnit.SECONDS)
    fun qfsliaMediumShallowContextCheckAverage() {
        qfsliaMedium.commands.filterIsInstance<Assert>().forEach { assert ->
            qfsliaMedium.shallowContextCheck(assert.expr)
        }
    }

    @Benchmark
    @BenchmarkMode(Mode.AverageTime)
    @OutputTimeUnit(TimeUnit.MILLISECONDS)
    @Warmup(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
    @Measurement(iterations = 20, time = 5, timeUnit = TimeUnit.SECONDS)
    fun qfsliaMediumIterativeContextCheckAverage() {
        qfsliaMedium.commands.filterIsInstance<Assert>().forEach { assert ->
            qfsliaMedium.iterativeContextCheck(assert.expr)
        }
    }

    @Benchmark
    @BenchmarkMode(Mode.AverageTime)
    @OutputTimeUnit(TimeUnit.MILLISECONDS)
    @Warmup(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
    @Measurement(iterations = 20, time = 5, timeUnit = TimeUnit.SECONDS)
    fun qfbvMediumDeepContextCheckAverage() {
        qfbvMedium.commands.filterIsInstance<Assert>().forEach { assert ->
            qfbvMedium.deepContextCheck(assert.expr)
        }
    }

    @Benchmark
    @BenchmarkMode(Mode.AverageTime)
    @OutputTimeUnit(TimeUnit.MILLISECONDS)
    @Warmup(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
    @Measurement(iterations = 20, time = 5, timeUnit = TimeUnit.SECONDS)
    fun qfbvMediumShallowContextCheckAverage() {
        qfbvMedium.commands.filterIsInstance<Assert>().forEach { assert ->
            qfbvMedium.shallowContextCheck(assert.expr)
        }
    }

    @Benchmark
    @BenchmarkMode(Mode.AverageTime)
    @OutputTimeUnit(TimeUnit.MILLISECONDS)
    @Warmup(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
    @Measurement(iterations = 20, time = 5, timeUnit = TimeUnit.SECONDS)
    fun qfbvMediumIterativeContextCheckAverage() {
        qfbvMedium.commands.filterIsInstance<Assert>().forEach { assert ->
            qfbvMedium.iterativeContextCheck(assert.expr)
        }
    }

    @Benchmark
    @BenchmarkMode(Mode.AverageTime)
    @OutputTimeUnit(TimeUnit.MILLISECONDS)
    @Warmup(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
    @Measurement(iterations = 20, time = 5, timeUnit = TimeUnit.SECONDS)
    fun qfsliaLargeDeepContextCheckAverage() {
        qfsliaLarge.commands.filterIsInstance<Assert>().forEach { assert ->
            qfsliaLarge.deepContextCheck(assert.expr)
        }
    }

    @Benchmark
    @BenchmarkMode(Mode.AverageTime)
    @OutputTimeUnit(TimeUnit.MILLISECONDS)
    @Warmup(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
    @Measurement(iterations = 20, time = 5, timeUnit = TimeUnit.SECONDS)
    fun qfsliaLargeShallowContextCheckAverage() {
        qfsliaLarge.commands.filterIsInstance<Assert>().forEach { assert ->
            qfsliaLarge.shallowContextCheck(assert.expr)
        }
    }

    @Benchmark
    @BenchmarkMode(Mode.AverageTime)
    @OutputTimeUnit(TimeUnit.MILLISECONDS)
    @Warmup(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
    @Measurement(iterations = 20, time = 5, timeUnit = TimeUnit.SECONDS)
    fun qfsliaLargeIterativeContextCheckAverage() {
        qfsliaLarge.commands.filterIsInstance<Assert>().forEach { assert ->
            qfsliaLarge.iterativeContextCheck(assert.expr)
        }
    }

    @Benchmark
    @BenchmarkMode(Mode.AverageTime)
    @OutputTimeUnit(TimeUnit.MILLISECONDS)
    @Warmup(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
    @Measurement(iterations = 20, time = 5, timeUnit = TimeUnit.SECONDS)
    fun qfbvLargeDeepContextCheckAverage() {
        qfbvLarge.commands.filterIsInstance<Assert>().forEach { assert ->
            qfbvLarge.deepContextCheck(assert.expr)
        }
    }

    @Benchmark
    @BenchmarkMode(Mode.AverageTime)
    @OutputTimeUnit(TimeUnit.MILLISECONDS)
    @Warmup(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
    @Measurement(iterations = 20, time = 5, timeUnit = TimeUnit.SECONDS)
    fun qfbvLargeShallowContextCheckAverage() {
        qfbvLarge.commands.filterIsInstance<Assert>().forEach { assert ->
            qfbvLarge.shallowContextCheck(assert.expr)
        }
    }

    @Benchmark
    @BenchmarkMode(Mode.AverageTime)
    @OutputTimeUnit(TimeUnit.MILLISECONDS)
    @Warmup(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
    @Measurement(iterations = 20, time = 5, timeUnit = TimeUnit.SECONDS)
    fun qfbvLargeIterativeContextCheckAverage() {
        qfbvLarge.commands.filterIsInstance<Assert>().forEach { assert ->
            qfbvLarge.iterativeContextCheck(assert.expr)
        }
    }

    @Benchmark
    @BenchmarkMode(Mode.Throughput)
    @OutputTimeUnit(TimeUnit.MILLISECONDS)
    @Warmup(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
    @Measurement(iterations = 20, time = 5, timeUnit = TimeUnit.SECONDS)
    fun qfsLiaSmallDeepContextCheckThroughput() {
        qfsliaSmall.commands.filterIsInstance<Assert>().forEach { assert ->
            qfsliaSmall.deepContextCheck(assert.expr)
        }
    }

    @Benchmark
    @BenchmarkMode(Mode.Throughput)
    @OutputTimeUnit(TimeUnit.MILLISECONDS)
    @Warmup(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
    @Measurement(iterations = 20, time = 5, timeUnit = TimeUnit.SECONDS)
    fun qfsLiaSmallShallowContextCheckThroughput() {
        qfsliaSmall.commands.filterIsInstance<Assert>().forEach { assert ->
            qfsliaSmall.shallowContextCheck(assert.expr)
        }
    }

    @Benchmark
    @BenchmarkMode(Mode.Throughput)
    @OutputTimeUnit(TimeUnit.MILLISECONDS)
    @Warmup(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
    @Measurement(iterations = 20, time = 5, timeUnit = TimeUnit.SECONDS)
    fun qfsLiaSmallIterativeContextCheckThroughput() {
        qfsliaSmall.commands.filterIsInstance<Assert>().forEach { assert ->
            qfsliaSmall.iterativeContextCheck(assert.expr)
        }
    }

    @Benchmark
    @BenchmarkMode(Mode.Throughput)
    @OutputTimeUnit(TimeUnit.MILLISECONDS)
    @Warmup(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
    @Measurement(iterations = 20, time = 5, timeUnit = TimeUnit.SECONDS)
    fun qfbvSmallDeepContextCheckThroughput() {
        qfbvSmall.commands.filterIsInstance<Assert>().forEach { assert ->
            qfbvSmall.deepContextCheck(assert.expr)
        }
    }

    @Benchmark
    @BenchmarkMode(Mode.Throughput)
    @OutputTimeUnit(TimeUnit.MILLISECONDS)
    @Warmup(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
    @Measurement(iterations = 20, time = 5, timeUnit = TimeUnit.SECONDS)
    fun qfbvSmallShallowContextCheckThroughput() {
        qfbvSmall.commands.filterIsInstance<Assert>().forEach { assert ->
            qfbvSmall.shallowContextCheck(assert.expr)
        }
    }

    @Benchmark
    @BenchmarkMode(Mode.Throughput)
    @OutputTimeUnit(TimeUnit.MILLISECONDS)
    @Warmup(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
    @Measurement(iterations = 20, time = 5, timeUnit = TimeUnit.SECONDS)
    fun qfbvSmallIterativeContextCheckThroughput() {
        qfbvSmall.commands.filterIsInstance<Assert>().forEach { assert ->
            qfbvSmall.iterativeContextCheck(assert.expr)
        }
    }

    @Benchmark
    @BenchmarkMode(Mode.Throughput)
    @OutputTimeUnit(TimeUnit.MILLISECONDS)
    @Warmup(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
    @Measurement(iterations = 20, time = 5, timeUnit = TimeUnit.SECONDS)
    fun qfsliaMediumDeepContextCheckThroughput() {
        qfsliaMedium.commands.filterIsInstance<Assert>().forEach { assert ->
            qfsliaMedium.deepContextCheck(assert.expr)
        }
    }

    @Benchmark
    @BenchmarkMode(Mode.Throughput)
    @OutputTimeUnit(TimeUnit.MILLISECONDS)
    @Warmup(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
    @Measurement(iterations = 20, time = 5, timeUnit = TimeUnit.SECONDS)
    fun qfsliaMediumShallowContextCheckThroughput() {
        qfsliaMedium.commands.filterIsInstance<Assert>().forEach { assert ->
            qfsliaMedium.shallowContextCheck(assert.expr)
        }
    }

    @Benchmark
    @BenchmarkMode(Mode.Throughput)
    @OutputTimeUnit(TimeUnit.MILLISECONDS)
    @Warmup(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
    @Measurement(iterations = 20, time = 5, timeUnit = TimeUnit.SECONDS)
    fun qfsliaMediumIterativeContextCheckThroughput() {
        qfsliaMedium.commands.filterIsInstance<Assert>().forEach { assert ->
            qfsliaMedium.iterativeContextCheck(assert.expr)
        }
    }

    @Benchmark
    @BenchmarkMode(Mode.Throughput)
    @OutputTimeUnit(TimeUnit.MILLISECONDS)
    @Warmup(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
    @Measurement(iterations = 20, time = 5, timeUnit = TimeUnit.SECONDS)
    fun qfbvMediumDeepContextCheckThroughput() {
        qfbvMedium.commands.filterIsInstance<Assert>().forEach { assert ->
            qfbvMedium.deepContextCheck(assert.expr)
        }
    }

    @Benchmark
    @BenchmarkMode(Mode.Throughput)
    @OutputTimeUnit(TimeUnit.MILLISECONDS)
    @Warmup(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
    @Measurement(iterations = 20, time = 5, timeUnit = TimeUnit.SECONDS)
    fun qfbvMediumShallowContextCheckThroughput() {
        qfbvMedium.commands.filterIsInstance<Assert>().forEach { assert ->
            qfbvMedium.shallowContextCheck(assert.expr)
        }
    }

    @Benchmark
    @BenchmarkMode(Mode.Throughput)
    @OutputTimeUnit(TimeUnit.MILLISECONDS)
    @Warmup(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
    @Measurement(iterations = 20, time = 5, timeUnit = TimeUnit.SECONDS)
    fun qfbvMediumIterativeContextCheckThroughput() {
        qfbvMedium.commands.filterIsInstance<Assert>().forEach { assert ->
            qfbvMedium.iterativeContextCheck(assert.expr)
        }
    }

    @Benchmark
    @BenchmarkMode(Mode.Throughput)
    @OutputTimeUnit(TimeUnit.SECONDS)
    @Warmup(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
    @Measurement(iterations = 20, time = 5, timeUnit = TimeUnit.SECONDS)
    fun qfsliaLargeDeepContextCheckThroughput() {
        qfsliaLarge.commands.filterIsInstance<Assert>().forEach { assert ->
            qfsliaLarge.deepContextCheck(assert.expr)
        }
    }

    @Benchmark
    @BenchmarkMode(Mode.Throughput)
    @OutputTimeUnit(TimeUnit.SECONDS)
    @Warmup(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
    @Measurement(iterations = 20, time = 5, timeUnit = TimeUnit.SECONDS)
    fun qfsliaLargeShallowContextCheckThroughput() {
        qfsliaLarge.commands.filterIsInstance<Assert>().forEach { assert ->
            qfsliaLarge.shallowContextCheck(assert.expr)
        }
    }

    @Benchmark
    @BenchmarkMode(Mode.Throughput)
    @OutputTimeUnit(TimeUnit.SECONDS)
    @Warmup(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
    @Measurement(iterations = 20, time = 5, timeUnit = TimeUnit.SECONDS)
    fun qfsliaLargeIterativeContextCheckThroughput() {
        qfsliaLarge.commands.filterIsInstance<Assert>().forEach { assert ->
            qfsliaLarge.iterativeContextCheck(assert.expr)
        }
    }

    @Benchmark
    @BenchmarkMode(Mode.Throughput)
    @OutputTimeUnit(TimeUnit.SECONDS)
    @Warmup(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
    @Measurement(iterations = 20, time = 5, timeUnit = TimeUnit.SECONDS)
    fun qfbvLargeDeepContextCheckThroughput() {
        qfbvLarge.commands.filterIsInstance<Assert>().forEach { assert ->
            qfbvLarge.deepContextCheck(assert.expr)
        }
    }

    @Benchmark
    @BenchmarkMode(Mode.Throughput)
    @OutputTimeUnit(TimeUnit.SECONDS)
    @Warmup(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
    @Measurement(iterations = 20, time = 5, timeUnit = TimeUnit.SECONDS)
    fun qfbvLargeShallowContextCheckThroughput() {
        qfbvLarge.commands.filterIsInstance<Assert>().forEach { assert ->
            qfbvLarge.shallowContextCheck(assert.expr)
        }
    }

    @Benchmark
    @BenchmarkMode(Mode.Throughput)
    @OutputTimeUnit(TimeUnit.SECONDS)
    @Warmup(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
    @Measurement(iterations = 20, time = 5, timeUnit = TimeUnit.SECONDS)
    fun qfbvLargeIterativeContextCheckThroughput() {
        qfbvLarge.commands.filterIsInstance<Assert>().forEach { assert ->
            qfbvLarge.iterativeContextCheck(assert.expr)
        }
    }
}

val Expression<*>.deepAll : DeepRecursiveFunction<(Expression<*>) -> Boolean, Boolean>
    get() = DeepRecursiveFunction { predicate ->
    // Apply predicate to current node
    if (!predicate(this@deepAll)) return@DeepRecursiveFunction false

    // Recursively check all children using the DeepRecursiveScope
    for (child in this@deepAll.children) {
        if (!child.deepAll.callRecursive(predicate)) return@DeepRecursiveFunction false
    }

    true
}

fun Expression<*>.shallowAll(predicate: (Expression<*>) -> Boolean): Boolean {
    // Apply predicate to current node
    if (!predicate(this)) return false

    // Recursively check all children using the DeepRecursiveScope
    for (child in children) {
        if (!child.shallowAll(predicate)) return false
    }

    return true
}

fun Expression<*>.iterativeAll(predicate: (Expression<*>) -> Boolean): Boolean {
    if (!predicate(this)) return false

    val stack = ArrayDeque<Expression<*>>(children)
    while (stack.isNotEmpty()) {
        if(!predicate(stack.first())) return false

        stack.addAll(stack.removeLast().children)
    }

    return true
}

val Expression<*>.deepToString : DeepRecursiveFunction<StringBuilder, StringBuilder>
    get() = DeepRecursiveFunction { builder ->
        if (children.isEmpty()) {
            builder.append(name)
        } else {
            builder.append("($name ")
            children.forEach { child ->
                child.deepToString.callRecursive(builder)
            }
            builder.append(")")
        }
    }

fun Expression<*>.shallowToString(builder: StringBuilder): StringBuilder =
    if (children.isEmpty()) {
        builder.append(name)
    } else {
        builder.append("($name ")
        children.forEach { child ->
            child.shallowToString(builder)
        }
        builder.append(")")
    }

fun Expression<*>.iterativeToString(builder: StringBuilder): StringBuilder {
    val builder = StringBuilder()
    val stack = ArrayDeque<Expression<*>>()
    stack.add(this)

    do {
        val node = stack.removeLast()

        if (node.children.isEmpty()) {
            builder.append(node.name)
        } else {
            builder.append("(${node.name} ")
        }

        stack.addAll(node.children)
    } while (stack.isNotEmpty())

    return builder
}

val SMTProgram.deepContextCheck: DeepRecursiveFunction<Expression<*>, Boolean>
    get () =
        DeepRecursiveFunction<Expression<*>, Boolean> { expr ->
            return@DeepRecursiveFunction if (expr is ExistsExpression) {
                context.bindVariables(expr.vars)
                val result = deepContextCheck.callRecursive(expr.term)
                context.unbindVariables()

                result
            } else if (expr is ForallExpression) {
                context.bindVariables(expr.vars)
                val result = deepContextCheck.callRecursive(expr.term)
                context.unbindVariables()

                result
            } else if (expr is LetExpression) {
                context.bindVariables(expr.bindings)
                val result = deepContextCheck.callRecursive(expr.inner)
                context.unbindVariables()

                result
            } else if (expr is AnnotatedExpression) {
                deepContextCheck.callRecursive(expr.term)
            } else {
                val result =
                    (expr.theories.isNotEmpty() || expr in context) &&
                            expr.children.all { deepContextCheck.callRecursive(it) }

                if (!result)
                    println(
                        "Not in theories ${logic?.theories}: ($expr ${expr.children.joinToString(" ")}) is in ${expr.theories}"
                    )

                result
            }
        }

fun SMTProgram.shallowContextCheck(expr : Expression<*>): Boolean {
    return if (expr is ExistsExpression) {
        context.bindVariables(expr.vars)
        val result = shallowContextCheck(expr.term)
        context.unbindVariables()

        result
    } else if (expr is ForallExpression) {
        context.bindVariables(expr.vars)
        val result = shallowContextCheck(expr.term)
        context.unbindVariables()

        result
    } else if (expr is LetExpression) {
        context.bindVariables(expr.bindings)
        val result = shallowContextCheck(expr.inner)
        context.unbindVariables()

        result
    } else if (expr is AnnotatedExpression) {
        shallowContextCheck(expr.term)
    } else {
        val result =
            (expr.theories.isNotEmpty() || expr in context) &&
                    expr.children.all { shallowContextCheck(it) }

        if (!result)
            println(
                "Not in theories ${logic?.theories}: ($expr ${expr.children.joinToString(" ")}) is in ${expr.theories}"
            )

        result
    }
}

fun SMTProgram.iterativeContextCheck(root : Expression<*>) {

}