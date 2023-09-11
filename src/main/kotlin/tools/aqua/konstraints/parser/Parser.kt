package tools.aqua.konstraints.parser

import java.lang.Exception

object Parser {
    class ParseNode(var token: String, val parent: ParseNode?) {
        val childs: MutableList<ParseNode> = mutableListOf()
    }

    fun tokenize(string: String, delimiters: List<Char>): List<String> {
        val tokens = mutableListOf<String>()
        var token = ""

        string.forEach {
            if (delimiters.contains(it)) {
                if (token.isNotEmpty())
                    tokens.add(token)

                token = ""

                tokens.add(it.toString())
            } else {
                token += it
            }
        }

        if (token.isNotEmpty())
            tokens.add(token)

        return tokens
    }

    fun createParseTreeV2(statement: String): ParseNode {
        val tokens = tokenize(statement, listOf('(', ')', ' ')).filter { it != " " }

        val root = ParseNode("", null)
        var current = root

        tokens.forEach {
            if (it == "(") {
                val temp = ParseNode("", current)
                current.childs.add(temp)
                current = temp
            } else if (it == ")") {
                if (current.parent != null) {
                    current = current.parent!!
                } else {
                    throw Exception("Illegal Statement")
                }
            } else if (it != " ") {
                if (current.token.isEmpty()) {
                    current.token = it
                } else {
                    current.childs.add(ParseNode(it, current))
                }
            }
        }

        return root
    }
}