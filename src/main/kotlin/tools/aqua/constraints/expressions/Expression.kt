package tools.aqua.constraints.expressions

interface Expression<T : Sort> {

    /**
     * operator symbol of this expression
     */
    val symbol:String

    /**
     * type of the expression
     */
    val type:Sort

}