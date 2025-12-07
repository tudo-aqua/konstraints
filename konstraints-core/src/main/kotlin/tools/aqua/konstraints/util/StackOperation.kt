package tools.aqua.konstraints.util

enum class StackOperationType {
    NONE, BIND, UNBIND
}

data class StackOperation<T>(val operation: StackOperationType, val value: T) {
    fun unbind() = StackOperation(StackOperationType.UNBIND, value)
}