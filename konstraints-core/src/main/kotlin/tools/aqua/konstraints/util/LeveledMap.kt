package tools.aqua.konstraints.util

class LeveledMap<K, V> : MutableMap<K, V> {
    private val map = mutableMapOf<K, V>()
    private val stack = Stack<MutableList<K>>()

    fun push() {
        stack.push(mutableListOf())
    }

    fun pop() {
        stack.pop().forEach { key ->
            map.remove(key)
        }
    }

    override val keys = map.keys
    override val values = map.values
    override val entries = map.entries

    override fun put(key: K, value: V): V? {
        stack.peek().add(key)
        return map.put(key, value)
    }

    override fun remove(key: K): V? {
        return map.remove(key)
    }

    override fun putAll(from: Map<out K, V>) {
        map.putAll(from)
        stack.peek().addAll(from.keys)
    }

    override fun clear() {
        map.clear()
        stack.clear()
    }

    override val size = map.size

    override fun isEmpty() = map.isEmpty()

    override fun containsKey(key: K) = map.containsKey(key)

    override fun containsValue(value: V) = map.containsValue(value)

    override fun get(key: K) = map[key]
}