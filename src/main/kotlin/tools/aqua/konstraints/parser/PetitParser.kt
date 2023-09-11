package tools.aqua.konstraints.parser

import org.petitparser.parser.Parser
import org.petitparser.parser.combinators.ChoiceParser
import org.petitparser.parser.combinators.SequenceParser
import org.petitparser.parser.combinators.SettableParser.undefined
import org.petitparser.parser.primitive.CharacterParser.anyOf
import org.petitparser.parser.primitive.CharacterParser.of
import org.petitparser.parser.primitive.CharacterParser.range
import org.petitparser.parser.primitive.StringParser.of
import java.math.BigDecimal

operator fun Parser.plus(other: Parser): ChoiceParser = or(other)
operator fun Parser.times(other: Parser): SequenceParser = seq(other)

infix fun Parser.trim(both: Parser): Parser = trim(both)

object PetitParser {
    // Auxiliary Lexical Categories

    val whitespaceCat = anyOf(" \t\r\n", "space, tab, or newline expected")
    val printableCat = range('\u0020', '\u007E') + range('\u0080', '\u00FF')
    val digitCat = range('0', '9')
    val letterCat = range('A', 'Z') + range('a', 'z')

    // Tokens: Reserved Words: General

    val exclamationKW = of('!') trim whitespaceCat
    val underscoreKW = of('_') trim whitespaceCat
    val asKW = of("as") trim whitespaceCat
    val binaryKW = of("BINARY") trim whitespaceCat
    val decimalKW = of("DECIMAL") trim whitespaceCat
    val existsKW = of("exists") trim whitespaceCat
    val hexadecimalKW = of("HEXADECIMAL") trim whitespaceCat
    val forallKW = of("forall") trim whitespaceCat
    val letKW = of("let") trim whitespaceCat
    val matchKW = of("match") trim whitespaceCat
    val numeralKW = of("NUMERAL") trim whitespaceCat
    val parKW = of("par") trim whitespaceCat
    val stringKW = of("STRING") trim whitespaceCat

    // Tokens: Reserved Words: Command names

    val assertKW = of("assert") trim whitespaceCat
    val checkSatKW = of("check-sat") trim whitespaceCat
    val checkSatAssumingKW = of("check-sat-assuming") trim whitespaceCat
    val declareConstKW = of("declare-const") trim whitespaceCat
    val declareDatatypeKW = of("declare-datatype") trim whitespaceCat
    val declareDatatypesKW = of("declare-datatypes") trim whitespaceCat
    val declareFunKW = of("declare-fun") trim whitespaceCat
    val declareSortKW = of("declare-sort") trim whitespaceCat
    val defineFunKW = of("define-fun") trim whitespaceCat
    val defineFunRecKW = of("define-fun-rec") trim whitespaceCat
    val defineSortKW = of("define-sort") trim whitespaceCat
    val echoKW = of("echo") trim whitespaceCat
    val exitKW = of("exit") trim whitespaceCat
    val getAssertionsKW = of("get-assertions") trim whitespaceCat
    val getAssignmentKW = of("get-assignment") trim whitespaceCat
    val getInfoKW = of("get-info") trim whitespaceCat
    val getModelKW = of("get-model") trim whitespaceCat
    val getOptionKW = of("get-option") trim whitespaceCat
    val getProofKW = of("get-proof") trim whitespaceCat
    val getUnsatAssumptionsKW = of("get-unsat-assumptions") trim whitespaceCat
    val getUnsatCoreKW = of("get-unsat-core") trim whitespaceCat
    val getValueKW = of("get-value") trim whitespaceCat
    val popKW = of("pop") trim whitespaceCat
    val pushKW = of("push") trim whitespaceCat
    val resetKW = of("reset") trim whitespaceCat
    val resetAssertionsKW = of("reset-assertions") trim whitespaceCat
    val setInfoKW = of("set-info") trim whitespaceCat
    val setLogicKW = of("set-logic") trim whitespaceCat
    val setOptionKW = of("set-option") trim whitespaceCat

    // Tokens: Other tokens

    val lparen = of('(') trim whitespaceCat
    val rparen = of(')') trim whitespaceCat

    val numeralBase = (of('0') + (range('1', '9') * digitCat.plus()))
    val numeral = numeralBase.map(String::toInt)
    val decimal = (numeralBase * of('.') * of('0').star() * numeralBase).flatten().map<String, BigDecimal>(::BigDecimal)
    val hexadecimal = of("#x") * (digitCat + range('A', 'F') + range('a', 'f')).plus()
    val binary = of("#b") * range('0', '1').plus()
    val anythingButQuotes = whitespaceCat +
            range('\u0020', '"' - 1) +
            range('"' + 1, '\u007E') +
            range('\u0080', '\u00FF')
    val string =
        of("\"") * (anythingButQuotes.star() + ((anythingButQuotes.star() * of("\"\"") * anythingButQuotes.star()).star())) * of(
            "\""
        )

    val symbolSymbols = anyOf("+-/*=%?!.\$_~&^<>@")
    val simpleSymbol = (letterCat + symbolSymbols) * (letterCat + digitCat + anyOf("+-/*=%?!.\$_~&^<>@")).star()

    val anythingButPipeOrBackslash = whitespaceCat + range('\u0020', '\\' - 1) +
            range('\\' + 1, '|' - 1) +
            range('|' + 1, '\u007E') +
            range('\u0080', '\u00FF')
    val quotedSymbol = of('|') * anythingButPipeOrBackslash.star() * of('|')

    val symbol = (simpleSymbol + quotedSymbol)
    val keyword = of(':') * simpleSymbol

    // S-Expressions

    val specConstant = (numeralBase + decimal + hexadecimal + binary + string)
    val sExpression = undefined()
    val reserved = assertKW + checkSatKW + declareFunKW + declareConstKW
    init {
        sExpression.set(((specConstant + reserved + symbol + keyword) trim whitespaceCat).flatten() + ((lparen * sExpression.star() * rparen) trim whitespaceCat)) // TODO reserved
    }

    //Identifiers

    val index = numeralBase + symbol
    val identifier = symbol + (lparen * symbol * index.plus() * rparen)

    //Sorts

    val sort = undefined()
    init {
        sort.set(identifier + (lparen * identifier * sort.plus() * rparen))
    }

    //Attributes
    val attributeValue = specConstant + symbol + (lparen * sExpression.star() * rparen)
    val attribute = keyword + (keyword * attributeValue)

    //Terms

    val term = undefined()
    val qualIdentifier = identifier + (lparen * asKW * identifier * sort * rparen)
    val varBinding = lparen * symbol * term * rparen
    val sortedVar = lparen * symbol * sort * rparen
    val pattern = symbol + (lparen * symbol * symbol.plus() * rparen)
    val matchCase = lparen * pattern * term * rparen
    init {
        term.set(specConstant +
                qualIdentifier +
                (lparen * qualIdentifier * term.plus() * rparen) +
                (lparen * letKW * lparen * varBinding.plus() * rparen * term * rparen) +
                (lparen * forallKW * lparen * sortedVar.plus() * rparen * term * rparen) +
                (lparen * existsKW * lparen * sortedVar.plus() * rparen * term * rparen) +
                (lparen * matchKW * term * lparen * matchCase.plus() * rparen * rparen) +
                (lparen * exclamationKW * term * attribute.plus() * rparen)
        )
    }

    //Theories
    //TODO

    //Logices
    //TODO

    //Info flags
    //TODO

    //Command options
    //TODO

    //Commands
    val sortDec = lparen * symbol * numeralBase * rparen
    val selectorDec = lparen * symbol * sort * rparen
    val constructorDec = lparen * symbol * selectorDec.star() * rparen
    val datatypeDec = (lparen * constructorDec.plus() * rparen) +
            (lparen * parKW * lparen * symbol.plus() * rparen * lparen * constructorDec.plus() * rparen * rparen)
    val functionDec = lparen * symbol * lparen * sortedVar.star() * rparen * sort * rparen
    val functionDef = symbol * lparen * sortedVar.star() * rparen * sort * term
    val propLiteral = undefined() /*symbol + (lparen * notKW * symbol * rparen)*/

    val assertCMD = lparen * assertKW * term * rparen
    val checkSatCMD = lparen * checkSatKW * rparen
    val declareConstCMD = lparen * declareConstKW * symbol * sort * rparen
    val declareFunCMD = lparen * declareFunKW * symbol * lparen * sort.star() * rparen * sort * rparen

    val command = assertCMD + checkSatCMD + declareConstCMD + declareFunCMD
    val script = command.star()

    //TODO missing commands

    //Command responses
    //TODO
}