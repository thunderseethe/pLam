{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE UndecidableInstances #-}

module Syntax where

import Control.Comonad.Cofree
import Control.Monad.Trans.State.Strict
import Control.Monad.Except
import Data.Functor.Classes
import Data.Functor.Foldable
import qualified Data.Map as Map
import Data.Text
import Data.Void
import Text.Megaparsec

-------------------------------------------------------------------------------------
newtype LambdaVar = LambdaVar Text
  deriving (Ord, Eq, Show)

-------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------
-- Parsed input
data ExpressionF a 
  = VarOrEnv LambdaVar
  | Abstraction LambdaVar a
  | Application a a
  deriving (Ord, Eq, Functor)

type Expression = Fix ExpressionF

varOrEnv :: LambdaVar -> Expression
varOrEnv = Fix . VarOrEnv

abstraction :: LambdaVar -> Expression -> Expression
abstraction arg body = Fix $ Abstraction arg body

application :: Expression -> Expression -> Expression
application e1 e2 = Fix $ Application e1 e2

instance Eq1 ExpressionF where
  liftEq eq fa fb = case (fa, fb) of
    (VarOrEnv name1, VarOrEnv name2) -> name1 == name2
    (Abstraction lv1 body1, Abstraction lv2 body2) -> eq body1 body2 && lv1 == lv2
    (Application a1 a2, Application b1 b2) -> eq a1 b1 && eq a2 b2
    (_, _) -> False

instance Show1 ExpressionF where
  liftShowsPrec sp _ d = \case
    VarOrEnv nm -> showsPrec d nm
    Abstraction arg body -> 
      showParen False $ showsUnaryWith sp ("λ" ++ show arg ++ ".") d body
    Application e1 e2 -> sp d e1 . showChar ' ' . sp d e2

-------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------
-- De Bruijn Indexed Term
data DeBruijnF a
  = Var Int
  | Abs a
  | App a
        a
  deriving (Ord, Eq, Functor)

-- Deprecated
type DeBruijn = Fix DeBruijnF

-- Lambda Term where each Node is annotated with some data.
type AnnTerm = Cofree DeBruijnF

var :: Int -> LambdaVar -> Term
var i lv = lv :< Var i

abs :: Term -> LambdaVar -> Term
abs body lv = lv :< Abs body

app :: Term -> Term -> Term
app e1 e2 = appLambdaVar :< App e1 e2

-- An application has no lambda var associated with it
appLambdaVar :: LambdaVar
appLambdaVar = LambdaVar ""

instance Eq1 DeBruijnF where
  liftEq :: (a -> b -> Bool) -> DeBruijnF a -> DeBruijnF b -> Bool
  liftEq eq fa fb = case (fa, fb) of
    (Var i1, Var i2) -> i1 == i2
    (Abs body1, Abs body2) -> eq body1 body2
    (App a1 b1, App a2 b2) -> eq a1 a2 && eq b1 b2
    (_, _) -> False

instance Show1 DeBruijnF where
  liftShowsPrec _ _ d (Var i) = showsPrec d i
  liftShowsPrec sp _ d (Abs body) =
    showParen False $ showsUnaryWith sp "λ" d body
  liftShowsPrec sp _ d (App e1 e2) = sp d e1 . showChar ' ' . sp d e2

instance Foldable DeBruijnF where
  foldMap :: (Monoid m) => (a -> m) -> DeBruijnF a -> m
  foldMap f = \case
    Var _ -> mempty
    Abs body -> f body
    App e1 e2 -> f e1 <> f e2

  foldr :: (a -> b -> b) -> b -> DeBruijnF a -> b
  foldr accum seed = \case
    Var _ -> seed
    Abs body -> accum body seed
    App e1 e2 -> accum e1 (accum e2 seed)

instance Traversable DeBruijnF where
  traverse f = \case
    Var i -> pure (Var i)
    Abs body -> Abs <$> f body
    App e1 e2 -> App <$> f e1 <*> f e2

-------------------------------------------------------------------------------------
data EvaluateOption = Detailed
                    | CallByValue
                    | None
                    deriving (Eq, Show)

data Command = Define Text Expression
             | Evaluate EvaluateOption EvaluateOption Expression
             | Import Text
             | Export Text
             | Review Text
             | Comment Text
             | Run Text
             | Print Text
             deriving (Eq, Show)

-------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------
type Term = AnnTerm LambdaVar

type Environment = Map.Map Text Term

type ProgramT m = StateT Environment m

data Error
  = SyntaxError (ParseErrorBundle Text Void)
  | UndeclaredVariable Text
  | FatalError Text

instance Show Error where
  show (SyntaxError se) = errorBundlePretty se
  show (UndeclaredVariable uv) =
    " ERROR: undeclared variable " ++
    show uv ++
    "\n- type \":review all\" to see all environment variables you can use\n- type \"" ++
    show uv ++ " = <lambda expression>\" to add this variables to environment"
  show (FatalError fe) = show fe

type FailableT = ExceptT Error
-------------------------------------------------------------------------------------
