{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}

module Syntax where

import Control.Monad.State
import Data.Functor.Classes
import Data.Functor.Foldable
import qualified Data.Text as Text
import Text.Parsec hiding (State)

-------------------------------------------------------------------------------------
data LambdaVar = LambdaVar
  { name :: Char
  , index :: Int
  } deriving (Ord, Eq)

showVarHelper :: Int -> String
showVarHelper 0 = ""
showVarHelper n = "'" ++ showVarHelper (n - 1)

instance Show LambdaVar where
  show (LambdaVar c 0) = [c]
  show (LambdaVar c i) = [c] ++ showVarHelper i

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
  | Abs a
  | App a
        a
  deriving (Ord, Eq, Functor)

var :: Int -> LambdaVar -> DeBruijn
var i lv = Fix $ Var i lv

abs :: DeBruijn -> DeBruijn
abs = Fix . Abs

app :: DeBruijn -> DeBruijn -> DeBruijn
app e1 e2 = Fix $ App e1 e2

type DeBruijn = Fix DeBruijnF

debruijnify :: Expression -> DeBruijn
debruijnify expr = ana debruijnCoalg ([], 0, expr)

debruijnCoalg ::
     ([(LambdaVar, Int)], Int, Expression)
  -> Base DeBruijn ([(LambdaVar, Int)], Int, Expression)
debruijnCoalg (gamma, n, expr) =
  case expr of
    Variable var ->
      let depth = findDepth n var gamma
          val =
            if depth < 0
              then depth
              else (n - depth)
      in Var val var
    EnvironmentVar name -> undefined
    Abstraction var body -> Abs ((var, n) : gamma, n + 1, body)
    Application e1 e2 -> App (gamma, n, e1) (gamma, n, e2)

findDepth :: Int -> LambdaVar -> [(LambdaVar, Int)] -> Int
findDepth freeVal var gamma =
  case gamma of
    (v, n):tail ->
      if var == v
        then n
        else findDepth (max freeVal n) var tail
    [] -> -(freeVal + 1)

instance Show1 DeBruijnF where
  liftShowsPrec _ _ d (Var i _) = showsPrec d i
  liftShowsPrec sp _ d (Abs body) =
    showParen False $ showsUnaryWith sp "λ" d body
  liftShowsPrec sp _ d (App e1 e2) = (sp d e1) . (showChar ' ') . (sp d e2)

prettyPrint :: DeBruijn -> Text.Text
prettyPrint = cata alga
  where
    alga e = case e of
      Var i _ -> (Text.pack . show) i
      Abs body -> Text.concat [Text.pack "(λ ", body, Text.pack ")"]
      App e1 e2 -> Text.concat [e1, Text.pack " ", e2]

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
