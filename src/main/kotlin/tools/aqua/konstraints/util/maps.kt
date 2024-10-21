package tools.aqua.konstraints.util

/**
 * Reentrant version of [MutableMap.computeIfAbsent]. If this map contains [key], the corresponding entry is returned. Else, [mapping] is applied to the [key]. If a side-effect of [mapping] caused [key] to be present in the map,
 * [merge] is called with the key, the side-effect-computed value, and the function-computed value and the resulting value used.
 */
inline fun <K, V> MutableMap<K, V>.computeIfAbsentAndMerge(
    key: K,
    mapping: (K) -> V,
    merge: (K, V, V) -> V
): V =
    this[key] ?: mapping(key).let { computed ->
        this[key]?.let { present ->
            merge(key, present, computed).also {
                this[key] = it
            }
        } ?: computed
    }

/**
 * Reentrant version of [MutableMap.computeIfAbsent]. If this map contains [key], the corresponding entry is returned. Else, [mapping] is applied to the [key]. If a side-effect of [mapping] caused [key] to be present in the map,
 * the side-effect-computed value and function-computed value are required to be equal.
 */
inline fun <K, V> MutableMap<K, V>.computeIfAbsentAndMerge(
    key: K,
    mapping: (K) -> V
): V = computeIfAbsentAndMerge(key, mapping) { _, computed, present ->
    require(computed == present) { "the mapping function set $key: $present, but computed $key: $computed" }
    return computed
}