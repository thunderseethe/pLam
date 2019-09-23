{-# LANGUAGE FlexibleContexts, LambdaCase #-}
module Parser where

import           Prelude                 hiding ( abs )

import           Control.Monad.Except
import           Text.Parsec             hiding ( State )
import           Data.Bifunctor
import           Data.Functor.Foldable
import           Data.Functor.Identity

import qualified Text.Parsec.Token             as Token
import           Text.Parsec.Language

import           Evaluator
import           Syntax

-------------------------------------------------------------------------------------
languageDef :: GenLanguageDef String u Identity
languageDef = emptyDef
    { Token.commentLine     = "--"
    , Token.identStart      = letter
    , Token.identLetter     = alphaNum <|> char '_'
    , Token.reservedNames   = [ ":import"
                              , ":review"
                              , ":run"
                              , ":print"
                              , ":d"
                              , ":cbv"
                              ]
    , Token.reservedOpNames = ["=", ".", "\\", "[", "]"]
    }

lexer :: Token.GenTokenParser String u Identity
lexer = Token.makeTokenParser languageDef

identifier :: ParsecT String u Identity String
identifier = Token.identifier lexer

reserved :: String -> ParsecT String u Identity ()
reserved = Token.reserved lexer

reservedOp :: String -> ParsecT String u Identity ()
reservedOp = Token.reservedOp lexer

parens :: ParsecT String u Identity a -> ParsecT String u Identity a
parens = Token.parens lexer

comma :: ParsecT String u Identity String
comma = Token.comma lexer
-------------------------------------------------------------------------------------

type Parser = Parsec String ()

-------------------------------------------------------------------------------------
symbol :: Parser Char
symbol = oneOf ".`#~@$%^&*_+-=|;',/?[]<>(){} "

comment :: Parser String
comment = many $ symbol <|> letter <|> digit

filename :: Parser String
filename = many1 $ letter <|> symbol <|> digit

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
emptyExpr = toExpression empty

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
        Nil -> empty
        Cons x xs ->
            let f = LambdaVar "f"
                l = LambdaVar "l"
            in  abs (abs (app (app (var 0 l) x) xs) l) f
-------------------------------------------------------------------------------------

-------------------------------------------------------------------------------------
parseList :: Parser Expression
parseList = do
    reservedOp "["
    exprs <- parseExpression `sepBy` comma
    reservedOp "]"
    return $ createList exprs

parseNumeral :: Parser Expression
parseNumeral = do
    strNum <- many1 digit
    spaces
    let intNum = read strNum :: Int
    maybeB <- optionMaybe (char 'b')
    return $ toExpression
        (if maybeB == Just 'b' then createBinary intNum else createChurch intNum
        )

parseVariable :: Parser Expression
parseVariable = varOrEnv . LambdaVar <$> identifier <* spaces

parseAbstraction :: Parser Expression
parseAbstraction =
    curryLambda
        <$> (  reservedOp "\\"
            *> endBy1 identifier spaces
            <* reservedOp "."
            <* spaces
            )
        <*> parseExpression
    where curryLambda xs body = foldr (\x -> abstraction (LambdaVar x)) body xs

parseApplication :: Parser Expression
parseApplication = do
    es <- sepBy1 parseSingleton spaces
    return $ foldl1 application es

parseSingleton :: Parser Expression
parseSingleton =
    parseList
        <|> parseNumeral
        <|> parseVariable
        <|> parseAbstraction
        <|> parens parseApplication

parseExpression :: Parser Expression
parseExpression = do
    spaces
    expr <- parseApplication <|> parseSingleton
    spaces
    return expr
-------------------------------------------------------------------------------------

-------------------------------------------------------------------------------------
parseDefine :: Parser Command
parseDefine =
    Define
        <$> (identifier <* spaces <* reservedOp "=" <* spaces)
        <*> parseExpression

-- Evaluate with options
parseDetailed :: Parser EvaluateOption
parseDetailed = do
    reserved ":d"
    return Detailed

parseCallByValue :: Parser EvaluateOption
parseCallByValue = do
    reserved ":cbv"
    return CallByValue

parseEvaluate :: Parser Command
parseEvaluate = do
    det <- option None parseDetailed
    spaces
    cbv <- option None parseCallByValue
    spaces
    Evaluate det cbv <$> parseExpression
-----------------------------------

parseFileCommand :: String -> (String -> Command) -> Parser Command
parseFileCommand commandName cmd =
    cmd <$> (reserved (':' : commandName) *> spaces *> filename)

parseImport :: Parser Command
parseImport = parseFileCommand "import" Import

parseExport :: Parser Command
parseExport = parseFileCommand "export" Export 

parseReview :: Parser Command
parseReview = do
    reserved ":review"
    spaces
    Review <$> identifier

parseComment :: Parser Command
parseComment = Comment <$> (string "--" *> comment)

parseEmptyLine :: Parser Command
parseEmptyLine = Comment <$> (string "" *> comment)

parseRun :: Parser Command
parseRun = do
    reserved ":run"
    spaces
    Run <$> filename

parsePrint :: Parser Command
parsePrint = do
    reserved ":print"
    spaces
    Print <$> comment

parseLine :: Parser Command
parseLine =
    try parseDefine
        <|> parseImport
        <|> parseExport
        <|> parseReview
        <|> parseRun
        <|> parsePrint
        <|> parseComment
        <|> parseEvaluate
        <|> parseEmptyLine

-------------------------------------------------------------------------------------

-------------------------------------------------------------------------------------
readLine :: (MonadError Error m) => String -> m Command
readLine input =
    let parseOutput = first SyntaxError $ parse parseLine "parser" input
    in  either throwError return parseOutput
