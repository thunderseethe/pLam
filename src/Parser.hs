{-# LANGUAGE FlexibleContexts, LambdaCase #-}
module Parser where

import           Prelude                 hiding ( abs )

import           Control.Monad.Combinators
import           Control.Monad.Except
import           Data.Bifunctor
import           Data.Functor
import           Data.Functor.Foldable
import qualified Data.Text                     as T
import           Data.Text                      ( Text )

import           Text.Megaparsec hiding ( empty )
import qualified Text.Megaparsec.Char as C
import qualified Text.Megaparsec.Char.Lexer    as L

import           Evaluator
import           Syntax

-------------------------------------------------------------------------------------
--lambdaCalcDef :: GenLanguageDef Text u Identity
--lambdaCalcDef = Token.LanguageDef
--    { Token.commentStart    = ""
--    , Token.commentEnd      = ""
--    , Token.commentLine     = "--"
--    , Token.nestedComments  = True
--    , Token.identStart      = letter
--    , Token.identLetter     = alphaNum <|> char '_'
--    , Token.opStart         = Token.opLetter lambdaCalcDef
--    , Token.opLetter        = oneOf ":!#$%&*+./<=>?@\\^|-~"
--    , Token.reservedOpNames = ["=", ".", "\\", "[", "]"]
--    , Token.reservedNames   = [ ":import"
--                              , ":review"
--                              , ":run"
--                              , ":print"
--                              , ":d"
--                              , ":cbv"
--                              ]
--    , Token.caseSensitive   = True
--    }

reservedOps :: [Text]
reservedOps = ["=", ".", "\\", "[", "]"]

reservedNames :: [Text]
reservedNames = [":import", ":review", ":run", ":print", ":d", ":cbv"]

type MegaParsec = Text.Megaparsec.Parsec () Text

spaceConsumer :: MegaParsec ()
spaceConsumer = L.space C.space1 (L.skipLineComment "--") (L.skipBlockComment "{-" "-}")

--lexer :: Token.GenTokenParser Text u Identity
--lexer = Token.makeTokenParser lambdaCalcDef

lexeme :: MegaParsec a -> MegaParsec a
lexeme = L.lexeme spaceConsumer

symbol' :: Text -> MegaParsec Text
symbol' = L.symbol spaceConsumer

--identifier :: ParsecT Text u Identity Text
--identifier = Token.identifier lexer

megaIdentLetter :: MegaParsec Char
megaIdentLetter = C.alphaNumChar <|> C.char '_'

megaIdentifier :: MegaParsec Text
megaIdentifier = lexeme $ do
    c <- C.letterChar
    cs <- many megaIdentLetter
    return $ T.pack (c:cs)

--reserved :: Text -> ParsecT Text u Identity ()
--reserved = Token.reserved lexer

megaReserved :: Text -> MegaParsec ()
megaReserved name = lexeme $ do
    _ <- symbol' name
    notFollowedBy megaIdentLetter

--reservedOp :: Text -> ParsecT Text u Identity ()
--reservedOp = Token.reservedOp lexer

megaReservedOp :: Text -> MegaParsec ()
megaReservedOp name = lexeme $ do
    _ <- symbol' name
    notFollowedBy megaOpLetter

--parens :: ParsecT Text u Identity a -> ParsecT Text u Identity a
--parens = Token.parens lexer

megaParens :: MegaParsec a -> MegaParsec a
megaParens = between (symbol' "(") (symbol' ")")

megaBraces :: MegaParsec a -> MegaParsec a
megaBraces = between (symbol' "[") (symbol' "]")

--comma :: ParsecT Text u Identity Text
--comma = Token.comma lexer

megaComma :: MegaParsec Text
megaComma = symbol' ","
-------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------
--symbol :: Parser Char
--symbol = oneOf ".`#~@$%^&*_+-=|;',/?[]<>(){} "

megaOpLetter :: MegaParsec Char
megaOpLetter = Text.Megaparsec.oneOf (".`#~@$%^&*_+-=|;',/?[]<>(){} " :: [Char])

--filename :: Parser Text
--filename = many1 $ letter <|> symbol <|> digit

megaFilename :: MegaParsec Text
megaFilename = T.pack <$> some (C.letterChar <|> megaOpLetter <|> C.digitChar)

createChurch :: Int -> DeBruijn
createChurch n = abs (abs (apo coalga n) (LambdaVar "x")) (LambdaVar "f")
  where
    -- successor
    f = Fix $ Var 1 (LambdaVar "f")
    -- zero
    x = Var 0 (LambdaVar "x")

    coalga :: Int -> Base DeBruijn (Either DeBruijn Int)
    coalga = \case
        0 -> x
        i -> App (Left f) (Right (i - 1))

-- HELP EXPRS --
true :: DeBruijn
true =
    let x = LambdaVar "x"
        y = LambdaVar "y"
    in  abs (abs (var 1 x) y) x

false :: DeBruijn
false =
    let x = LambdaVar "x"
        y = LambdaVar "y"
    in  abs (abs (var 0 y) y) x

pair :: DeBruijn
pair =
    let x = LambdaVar "x"
        y = LambdaVar "y"
        p = LambdaVar "p"
    in  abs (abs (abs (app (app (var 0 p) (var 2 x)) (var 1 y)) p) y) x

end :: DeBruijn
end = abs true (LambdaVar "e")

whichBit :: Int -> DeBruijn
whichBit b = if b == 0 then false else true

----------------

createBinary :: Int -> DeBruijn
createBinary 0 = app (app pair false) end
createBinary n = apo coalga n
  where
    coalga :: Int -> Base DeBruijn (Either DeBruijn Int)
    coalga = \case
        0 -> Left <$> unfix end
        i -> App (Left $ app pair (whichBit (mod i 2))) (Right $ quot i 2)


-- LIST --
empty :: DeBruijn
empty =
    let f = LambdaVar "f"
        l = LambdaVar "l"
    in  abs (abs (var 1 f) l) f

emptyExpr :: Expression
emptyExpr = toExpression Parser.empty

createList :: [Expression] -> Expression
createList []       = emptyExpr
createList (x : xs) = abstraction
    (LambdaVar "f")
    (abstraction
        (LambdaVar "l")
        (application (application (varOrEnv (LambdaVar "l")) x) (createList xs))
    )

createList' :: [DeBruijn] -> DeBruijn
createList' = cata alga
  where
    alga = \case
        Nil -> Parser.empty
        Cons x xs ->
            let f = LambdaVar "f"
                l = LambdaVar "l"
            in  abs (abs (app (app (var 0 l) x) xs) l) f
-------------------------------------------------------------------------------------

-------------------------------------------------------------------------------------
--parseList :: Parser Expression
--parseList = do
--    reservedOp "["
--    exprs <- parseExpression `sepBy` comma
--    reservedOp "]"
--    return $ createList exprs

megaParseList :: MegaParsec Expression
megaParseList = createList <$> megaBraces (megaParseExpression `sepBy` megaComma)

--parseNumeral :: Parser Expression
--parseNumeral = do
--    strNum <- many1 digit
--    spaces
--    let intNum = read strNum :: Int
--    maybeB <- optionMaybe (char 'b')
--    return $ toExpression
--        (if maybeB == Just 'b' then createBinary intNum else createChurch intNum
--        )

megaParseDecimal :: MegaParsec Expression
megaParseDecimal = toExpression . createChurch <$> lexeme L.decimal

megaParseBinary :: MegaParsec Expression
megaParseBinary = toExpression . createBinary <$> lexeme L.binary

--parseVariable :: Parser Expression
--parseVariable = varOrEnv . LambdaVar <$> identifier <* spaces

megaParseVariable :: MegaParsec Expression
megaParseVariable = fmap (varOrEnv . LambdaVar . T.unpack) megaIdentifier

--parseAbstraction :: Parser Expression
--parseAbstraction =
--    curryLambda
--        <$> (  reservedOp "\\"
--            *> endBy1 identifier spaces
--            <* reservedOp "."
--            <* spaces
--            )
--        <*> parseExpression
--    where curryLambda xs body = foldr (\x -> abstraction (LambdaVar x)) body xs

megaParseAbstraction :: MegaParsec Expression
megaParseAbstraction = do
    megaReservedOp "\\"
    arg <- some megaIdentifier
    megaReservedOp "."
    curryLambda arg <$> megaParseExpression
    where curryLambda xs body = foldr (\x -> abstraction (LambdaVar $ T.unpack x)) body xs

--parseApplication :: Parser Expression
--parseApplication = do
--    es <- sepBy1 parseSingleton spaces
--    return $ foldl1 application es

megaParseApplication :: MegaParsec Expression
megaParseApplication = do
    es <- some megaParseSingleton
    return $ foldl1 application es

--parseSingleton :: Parser Expression
--parseSingleton =
--    parseList
--        <|> parseNumeral
--        <|> parseVariable
--        <|> parseAbstraction
--        <|> parens parseApplication

megaParseSingleton :: MegaParsec Expression
megaParseSingleton =
    megaParseList
        <|> megaParseDecimal
        <|> megaParseBinary
        <|> megaParseVariable
        <|> megaParseAbstraction
        <|> megaParens megaParseApplication

--parseExpression :: Parser Expression
--parseExpression = do
--    spaces
--    expr <- parseApplication <|> parseSingleton
--    spaces
--    return expr

megaParseExpression :: MegaParsec Expression
megaParseExpression = megaParseApplication <|> megaParseSingleton
-------------------------------------------------------------------------------------

-------------------------------------------------------------------------------------
--parseDefine :: Parser Command
--parseDefine =
--    Define
--        <$> (identifier <* spaces <* reservedOp "=" <* spaces)
--        <*> parseExpression

megaParseDefine :: MegaParsec Command
megaParseDefine = do
    ident <- megaIdentifier <* megaReservedOp "="
    Define ident <$> megaParseExpression

-- Evaluate with options
--parseDetailed :: Parser EvaluateOption
--parseDetailed = do
--    reserved ":d"
--    return Detailed

megaParseDetailed :: MegaParsec EvaluateOption
megaParseDetailed = megaReservedOp ":d" $> Detailed

--parseCallByValue :: Parser EvaluateOption
--parseCallByValue = do
--    reserved ":cbv"
--    return CallByValue

megaParseCallByValue :: MegaParsec EvaluateOption
megaParseCallByValue = megaReserved ":cbv" *> return CallByValue

--parseEvaluate :: Parser Command
--parseEvaluate = do
--    det <- option None parseDetailed
--    spaces
--    cbv <- option None parseCallByValue
--    spaces
--    Evaluate det cbv <$> parseExpression

megaParseEvaluate :: MegaParsec Command
megaParseEvaluate = do
    det <- option None megaParseDetailed
    cbv <- option None megaParseCallByValue
    Evaluate det cbv <$> megaParseExpression
-----------------------------------

--parseFileCommand :: Text -> (Text -> Command) -> Parser Command
--parseFileCommand commandName cmd =
--    cmd <$> (reserved (':' : commandName) *> spaces *> filename)

--parseImport :: Parser Command
--parseImport = parseFileCommand "import" Import

megaParseImport :: MegaParsec Command
megaParseImport = Import <$> (megaReservedOp ":import" *> megaFilename)

--parseExport :: Parser Command
--parseExport = parseFileCommand "export" Export

megaParseExport :: MegaParsec Command
megaParseExport = Export <$> (megaReservedOp ":export" *> megaFilename)

--parseReview :: Parser Command
--parseReview = do
--    reserved ":review"
--    spaces
--    Review <$> identifier

megaParseReview :: MegaParsec Command
megaParseReview = do
    megaReserved ":review"
    Review <$> megaIdentifier

--parseComment :: Parser Command
--parseComment = Comment <$> (Text "--" *> comment)

--megaParseComment :: MegaParsec Command
--megaParseComment = Comment <$> (symbol' "--" *> megaComment)

--parseEmptyLine :: Parser Command
--parseEmptyLine = Comment <$> (Text "" *> comment)

--parseRun :: Parser Command
--parseRun = do
--    reserved ":run"
--    spaces
--    Run <$> filename

megaParseRun :: MegaParsec Command
megaParseRun = do
    megaReserved ":run"
    Run <$> megaFilename

--parsePrint :: Parser Command
--parsePrint = do
--    reserved ":print"
--    spaces
--    Print <$> comment

megaParsePrint :: MegaParsec Command
megaParsePrint = do
    megaReserved ":print"
    Print . T.pack <$> manyTill L.charLiteral C.newline

--parseLine :: Parser Command
--parseLine =
--    try parseDefine
--        <|> parseImport
--        <|> parseExport
--        <|> parseReview
--        <|> parseRun
--        <|> parsePrint
--        <|> parseComment
--        <|> parseEvaluate
--        <|> parseEmptyLine

megaParseLine :: MegaParsec Command
megaParseLine =
    megaParseDefine
        <|> megaParseImport
        <|> megaParseExport
        <|> megaParseReview
        <|> megaParseRun
        <|> megaParsePrint
        <|> megaParseEvaluate
        -- <|> megaParseEmptyLine

-------------------------------------------------------------------------------------

-------------------------------------------------------------------------------------
--readLine :: (MonadError Error m) => Text -> m Command
--readLine input =
--    let parseOutput = first SyntaxError $ parse parseLine "parser" input
--    in  either throwError return parseOutput

readLine :: (MonadError Error m) => Text -> m Command
readLine input =
    let parseOutput = first SyntaxError $ parse megaParseLine "parser" input
    in either throwError return parseOutput