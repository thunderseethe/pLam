{-# LANGUAGE FlexibleContexts, LambdaCase #-}
module Parser where

import           Prelude                 hiding ( abs )

import           Control.Comonad.Trans.Cofree
import           Control.Monad.Combinators
import           Control.Monad.Except
import           Data.Bifunctor
import           Data.Functor.Foldable
import qualified Data.Text                     as T
import           Data.Text                      ( Text )
import           Data.Void

import           Text.Megaparsec         hiding ( empty )
import           Text.Megaparsec.Debug
import qualified Text.Megaparsec.Char          as C
import qualified Text.Megaparsec.Char.Lexer    as L

import           Evaluator
import           Syntax

-------------------------------------------------------------------------------------
reservedOps :: [Text]
reservedOps = ["=", ".", "\\", "[", "]"]

reservedNames :: [Text]
reservedNames = [":import", ":review", ":run", ":print", ":d", ":cbv"]

type MegaParsec = Text.Megaparsec.Parsec Void Text

spaceConsumer :: MegaParsec ()
spaceConsumer =
    L.space C.space1 (L.skipLineComment "--") (L.skipBlockComment "{-" "-}")

lexeme :: MegaParsec a -> MegaParsec a
lexeme = L.lexeme spaceConsumer

symbol' :: Text -> MegaParsec Text
symbol' = L.symbol spaceConsumer

identLetter :: MegaParsec Char
identLetter = C.alphaNumChar <|> C.char '_' <?> "IdentLetter"

identifier :: MegaParsec Text
identifier = lexeme $ do
    c  <- C.letterChar
    cs <- many identLetter
    return (T.pack (c : cs)) <?> "Identifier"

reserved :: Text -> MegaParsec ()
reserved name = lexeme $ do
    _ <- symbol' name
    notFollowedBy identLetter

reservedOp :: Text -> MegaParsec ()
reservedOp name = lexeme (symbol' name *> notFollowedBy opLetter)

parens :: MegaParsec a -> MegaParsec a
parens = between (symbol' "(") (symbol' ")")

braces :: MegaParsec a -> MegaParsec a
braces = between (symbol' "[") (symbol' "]")

comma :: MegaParsec Text
comma = symbol' ","
-------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------

opLetter :: MegaParsec Char
opLetter =
    Text.Megaparsec.oneOf (".`#~@$%^&*_+-=|;',/?[]<>(){} " :: [Char])

filename :: MegaParsec Text
filename = T.pack <$> some (C.letterChar <|> opLetter <|> C.digitChar)

createChurch :: Int -> Term
createChurch n = abs (abs (apo coalga n) (LambdaVar "x")) (LambdaVar "f")
  where
    -- successor
    f = var 1 (LambdaVar "f")

    coalga :: Int -> Base Term (Either Term Int)
    coalga = \case
        0 -> LambdaVar "x" :< Var 0
        i -> appLambdaVar :< App (Left f) (Right (i - 1))

-- HELP EXPRS --
true :: Term
true =
    let x = LambdaVar "x"
        y = LambdaVar "y"
    in  abs (abs (var 1 x) y) x

false :: Term
false =
    let x = LambdaVar "x"
        y = LambdaVar "y"
    in  abs (abs (var 0 y) y) x

pair :: Term
pair =
    let x = LambdaVar "x"
        y = LambdaVar "y"
        p = LambdaVar "p"
    in  abs (abs (abs (app (app (var 0 p) (var 2 x)) (var 1 y)) p) y) x

end :: Term
end = abs true (LambdaVar "e")

whichBit :: Int -> Term
whichBit b = if b == 0 then false else true

----------------

createBinary :: Int -> Term
createBinary 0 = app (app pair false) end
createBinary n = apo coalga n
  where
    coalga :: Int -> Base Term (Either Term Int)
    coalga = \case
        0 -> Left <$> project end
        i -> appLambdaVar
            :< App (Left $ app pair (whichBit (mod i 2))) (Right $ quot i 2)

-- LIST --
empty :: Term
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

createList' :: [Term] -> Term
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
parseList :: MegaParsec Expression
parseList =
    createList <$> braces (parseExpr `sepBy` comma) <?> "List"

parseDecimal :: MegaParsec Expression
parseDecimal =
    toExpression . createChurch <$> lexeme L.decimal <?> "Decimal"

parseBinary :: MegaParsec Expression
parseBinary = toExpression . createBinary <$> lexeme L.binary <?> "Binary"

parseVariable :: MegaParsec Expression
parseVariable = fmap (varOrEnv . LambdaVar) identifier <?> "Variable"

parseAbstraction :: MegaParsec Expression
parseAbstraction = do
    reservedOp "\\"
    args <- dbg "args" (some identifier)
    dbg "dot" $ reservedOp "."
    body <- dbg "body" parseExpr <?> "Abstraction"
    return $ curryLambda args body
    where 
        curryLambda :: [Text] -> Expression -> Expression
        curryLambda xs body = foldr (\arg acc -> abstraction (LambdaVar arg) acc) body xs

parseApplication :: MegaParsec Expression
parseApplication = do
    es <- some (dbg "appSingle" parseSingleton) <?> "Application"
    return $ foldl1 application es

parseSingleton :: MegaParsec Expression
parseSingleton =
    --parseList
    --    <|> parseDecimal
    --    <|> parseBinary
        {-<|>-} dbg "var" parseVariable
        <|> dbg "abs" parseAbstraction
        <|> dbg "parens" (parens parseExpr)
        <?> "Singleton"

parseExpr :: MegaParsec Expression
parseExpr = do
    left <- dbg "leftTerm" parseSingleton
    optBuildTerm <- dbg "rightTerm" $ optional parseExpr'
    return $ case optBuildTerm of
        Just buildTerm -> buildTerm left
        Nothing -> left

parseExpr' :: MegaParsec (Expression -> Expression)
parseExpr' = do
    term <- dbg "rightTerm" parseExpr
    optBuildTerm <- optional parseExpr'
    return $ case optBuildTerm of
        Just buildTerm -> \expr -> buildTerm (application expr term)
        Nothing -> (`application` term)

-------------------------------------------------------------------------------------

-------------------------------------------------------------------------------------
parseEvaluate :: MegaParsec Command
parseEvaluate =
    dbg "evaluate" (Evaluate None None <$> parseExpr <?> "Evaluate")
-----------------------------------

parseImport :: MegaParsec Command
parseImport =
    Import <$> (reservedOp ":import" *> filename) <?> "Import"

parseExport :: MegaParsec Command
parseExport =
    Export <$> (reservedOp ":export" *> filename) <?> "Export"

parseReview :: MegaParsec Command
parseReview = do
    reserved ":review"
    Review <$> identifier <?> "Review"

parseRun :: MegaParsec Command
parseRun = do
    reserved ":run"
    Run <$> filename <?> "Run"

parsePrint :: MegaParsec Command
parsePrint = do
    reserved ":print"
    Print . T.pack <$> manyTill L.charLiteral C.newline <?> "Print"

parseDefineOrEval :: MegaParsec Command
parseDefineOrEval = do
    ident <- identifier
    optExpr <- optional (reservedOp "=" *> parseExpr)
    return $ case optExpr of
        Just expr -> Define ident expr
        Nothing -> Evaluate None None $ (varOrEnv . LambdaVar) ident

parseLine :: MegaParsec Command
parseLine =
        parseImport
        <|> parseExport
        <|> parseReview
        <|> parseRun
        <|> parsePrint
        <|> parseDefineOrEval
        <|> parseEvaluate
        <?> "Line"

-------------------------------------------------------------------------------------

-------------------------------------------------------------------------------------
readLine :: (MonadError Error m) => Text -> m Command
readLine input =
    let parseOutput = first SyntaxError
            $ parse (dbg "parseLine" parseLine) "parser" input
    in  either throwError return parseOutput
