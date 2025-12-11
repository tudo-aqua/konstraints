package tools.aqua.konstraints.util

enum class StackOperationType {
    NONE, BIND, UNBIND, OPEN_BINDING, CLOSE_BINDING
}

data class StackOperation<T>(val operation: StackOperationType, val value: T) {
    fun unbind() = StackOperation(StackOperationType.UNBIND, value)
    fun close() = StackOperation(StackOperationType.CLOSE_BINDING, value)
}