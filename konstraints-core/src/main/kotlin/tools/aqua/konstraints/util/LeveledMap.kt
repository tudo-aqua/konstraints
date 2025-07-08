/*
 * SPDX-License-Identifier: Apache-2.0
 *
 * Copyright 2023-2025 The Konstraints Authors
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

package tools.aqua.konstraints.util

class LeveledMap<K, V> : MutableMap<K, V> {
  private val map = mutableMapOf<K, V>()
  private val stack = Stack<MutableList<K>>()

  init {
    stack.push(mutableListOf())
  }

  fun push() {
    stack.push(mutableListOf())
  }

  fun pop() {
    stack.pop().forEach { key -> map.remove(key) }
  }

  override val keys = map.keys
  override val values = map.values
  override val entries = map.entries

  override fun put(key: K, value: V): V? {
    stack.peek().add(key)
    return map.put(key, value)
  }

  override fun remove(key: K): V? {
    throw UnsupportedOperationException(
        "Remove operation is not supported by LeveledMap, use push/pop to control map contents!")
  }

  override fun putAll(from: Map<out K, V>) {
    map.putAll(from)
    stack.peek().addAll(from.keys)
  }

  override fun clear() {
    map.clear()
    stack.clear()
    stack.push(mutableListOf())
  }

  override val size = map.size

  override fun isEmpty() = map.isEmpty()

  override fun containsKey(key: K) = map.containsKey(key)

  override fun containsValue(value: V) = map.containsValue(value)

  override fun get(key: K) = map[key]
}
