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
import qualified Text.Megaparsec.Char          as C
import qualified Text.Megaparsec.Char.Lexer    as L

import           Evaluator
import           Syntax

-------------------------------------------------------------------------------------
reservedOps :: [Text]
reservedOps = ["=", ".", "\\", "[", "]"]

reservedNames :: [Text]
reservedNames = [":import", ":review", ":run", ":print", ":d", ":cbv", "let"]

type MegaParsec = Text.Megaparsec.Parsec Void Text

spaceConsumer :: MegaParsec ()
spaceConsumer =
    L.space C.space1 (L.skipLineComment "--") (L.skipBlockComment "{-" "-}")

lexeme :: MegaParsec a -> MegaParsec a
lexeme = L.lexeme spaceConsumer

symbol' :: Text -> MegaParsec Text
symbol' = L.symbol' spaceConsumer

identLetter :: MegaParsec Char
identLetter = C.alphaNumChar <|> C.char '_' <?> "IdentLetter"

identifier :: MegaParsec Text
identifier = (lexeme . try) (p >>= check)
  where
    p = 
        T.pack <$> ((:) <$> C.letterChar <*> many identLetter) <?> "Identifier"
    check x =
       if x `elem` reservedNames
       then fail $ "keyword " ++ show x ++ "cannot be an identifier"
       else return x

reserved :: Text -> MegaParsec ()
reserved name = do
    _ <- symbol' name
    return ()

reservedOp :: Text -> MegaParsec ()
reservedOp name = do
    _ <- symbol' name
    return ()

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
    Text.Megaparsec.oneOf (".`#~@$%^&*_+-=|;',/?[]<>){} " :: [Char])

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
    args <- some identifier
    reservedOp "."
    body <- parseExpr <?> "Abstraction"
    return $ curryLambda args body
    where
        curryLambda :: [Text] -> Expression -> Expression
        curryLambda xs body = foldr (\arg acc -> abstraction (LambdaVar arg) acc) body xs

parseSingleton :: MegaParsec Expression
parseSingleton =
    parseList
        <|> parseDecimal
        <|> parseVariable
        <|> parseAbstraction
        <|> parens parseExpr
        <?> "Singleton"

parseExpr :: MegaParsec Expression
parseExpr = do
    left <- parseSingleton
    optBuildTerm <- optional parseExpr'
    return $ case optBuildTerm of
        Just buildTerm -> buildTerm left
        Nothing -> left

parseExpr' :: MegaParsec (Expression -> Expression)
parseExpr' = do
    term <- parseExpr
    optBuildTerm <- optional parseExpr'
    return $ case optBuildTerm of
        Just buildTerm -> \expr -> buildTerm (application expr term)
        Nothing -> (`application` term)

-------------------------------------------------------------------------------------

-------------------------------------------------------------------------------------
parseEvaluate :: MegaParsec Command
parseEvaluate =
    Evaluate None None <$> parseExpr <?> "Evaluate"

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

parseDefine :: MegaParsec Command
parseDefine = do
    reserved "let"
    ident <- identifier
    reservedOp "="
    Define ident <$> parseExpr

parseLine :: MegaParsec Command
parseLine =
        parseImport
        <|> parseExport
        <|> parseReview
        <|> parseRun
        <|> parsePrint
        <|> parseDefine
        <|> parseEvaluate
        <?> "Line"

-------------------------------------------------------------------------------------

-------------------------------------------------------------------------------------
readLine :: (MonadError Error m) => Text -> m Command
readLine input =
    let parseOutput = first SyntaxError
            $ parse parseLine "parser" input
    in  either throwError return parseOutput
