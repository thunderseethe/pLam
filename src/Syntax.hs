{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE UndecidableInstances #-}

module Syntax where

import Control.Monad.State
import Data.Functor.Classes
import Data.Functor.Foldable
import Data.List
import qualified Data.Text as Text
import Text.Parsec hiding (State)

-------------------------------------------------------------------------------------
data LambdaVar = LambdaVar
  { name :: Char
  , index :: Int
  } deriving (Ord, Eq)

showVarHelper :: Int -> String
showVarHelper 0 = ""
showVarHelper n = '\'' : showVarHelper (n - 1)

instance Show LambdaVar where
  show (LambdaVar c 0) = [c]
  show (LambdaVar c i) = c : showVarHelper i

-------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------
data Expression
  = Variable LambdaVar
  | Abstraction LambdaVar
                Expression
  | Application Expression
                Expression
  | EnvironmentVar String
  deriving (Ord, Eq)

uncurryShow :: Expression -> String
uncurryShow (Abstraction v1 (Abstraction v2 e)) =
  show v1 ++ show v2 ++ uncurryShow e
uncurryShow (Abstraction v e) = show v ++ "." ++ show e
uncurryShow (Variable v) = ". " ++ show v
uncurryShow (Application e1 e2) = ". " ++ show e1 ++ " " ++ show e2

instance Show Expression where
  show (Variable v) = show v
  show abs@(Abstraction v e) = "(λ" ++ uncurryShow abs ++ ")"
  show (Application t1 t2) = "(" ++ show t1 ++ " " ++ show t2 ++ ")"
  show (EnvironmentVar ev) = ev

-------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------
-- De Bruijn Indexed Term
data DeBruijnF a
  = Var Int
        LambdaVar
  | Abs a LambdaVar
  | App a
        a
  deriving (Ord, Eq, Functor)

var :: Int -> LambdaVar -> DeBruijn
var i lv = Fix $ Var i lv

abs :: DeBruijn -> LambdaVar -> DeBruijn
abs body lv = Fix $ Abs body lv

app :: DeBruijn -> DeBruijn -> DeBruijn
app e1 e2 = Fix $ App e1 e2

type DeBruijn = Fix DeBruijnF

debruijnify :: Expression -> DeBruijn
debruijnify = ana coalga . ([],)
  where
    coalga (gamma, expr) = case expr of
      Variable var ->
        let val = findDepth var gamma
        in Var val var
      Abstraction arg body -> Abs (arg:gamma, body) arg
      Application e1 e2 -> App (gamma, e1) (gamma, e2)

findDepth :: LambdaVar -> [LambdaVar] -> Int
findDepth var = go 0
  where
    go n = \case
      (v:vs) -> if v == var then n else go (n+1) vs
      [] -> n

instance Show1 DeBruijnF where
  liftShowsPrec _ _ d (Var i _) = showsPrec d i
  liftShowsPrec sp _ d (Abs body _) =
    showParen False $ showsUnaryWith sp "λ" d body
  liftShowsPrec sp _ d (App e1 e2) = (sp d e1) . (showChar ' ') . (sp d e2)

prettyPrint :: DeBruijn -> Text.Text
prettyPrint = cata alga
  where
    alga = \case
      Var i lv -> (Text.pack . show) lv
      Abs body lv -> Text.concat ["(λ", (Text.pack . show) lv, ". ", body, ")"]
      App e1 e2 -> Text.concat [e1, " ", e2]

-------------------------------------------------------------------------------------
data EvaluateOption = Detailed
                    | CallByValue
                    | None
                    deriving (Eq, Show)

data Command = Define String Expression
             | Evaluate EvaluateOption EvaluateOption Expression
             | Import String
             | Export String
             | Review String
             | Comment String
             | Run String
             | Print String
             deriving (Eq, Show)

-------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------
type Environment = [(String, Expression)]

type Program = State Environment

data Error
  = SyntaxError ParseError
  | UndeclaredVariable String
  | FatalError String

instance Show Error where
  show (SyntaxError se) = show se
  show (UndeclaredVariable uv) =
    " ERROR: undeclared variable " ++
    show uv ++
    "\n- type \":review all\" to see all environment variables you can use\n- type \"" ++
    uv ++ " = <lambda expression>\" to add this variables to environment"
  show (FatalError fe) = show fe

type Failable = Either Error
-------------------------------------------------------------------------------------
