/*
 * SPDX-License-Identifier: Apache-2.0
 *
 * Copyright 2023-2024 The Konstraints Authors
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

/** Implements a stack/list hybrid that works well with all list operators like forEach */
class Stack<E>(private val stack: MutableList<E> = mutableListOf()) : List<E> by stack {

  /**
   * Construct stack from given list, where the first element in the list will be treated as bottom
   * element of the resulting stack
   */
  constructor(stack: List<E>) : this(stack.toMutableList())

  /**
   * Retrieve the top element of the stack
   *
   * @throws NoSuchElementException if the stack is empty
   */
  fun peek() = stack.last()

  /** Retrieve the top element of the stack or null if no such element exists */
  fun peekOrNull() = stack.lastOrNull()

  /**
   * Removes and returns the top element from the stack
   *
   * @throws NoSuchElementException if the stack is empty
   */
  fun pop() = stack.removeLast()

  /** Removes and returns the top element from the stack or null if no such element exists */
  fun popOrNull() = stack.removeLastOrNull()

  /** Pushes new element on top of the stack */
  fun push(element: E) {
    stack.add(element)
  }
}
