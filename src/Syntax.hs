{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE UndecidableInstances #-}

module Syntax where

import Control.Monad.Trans.State.Strict
import Control.Monad.Except
import Data.Functor.Classes
import Data.Functor.Foldable
import qualified Data.Map as Map
import Data.Text
import Text.Megaparsec

-------------------------------------------------------------------------------------
newtype LambdaVar = LambdaVar String
  deriving (Ord, Eq)

instance Show LambdaVar where
  show (LambdaVar c) = c

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
        LambdaVar
  | Abs a LambdaVar
  | App a
        a
  deriving (Ord, Eq, Functor)

type DeBruijn = Fix DeBruijnF

var :: Int -> LambdaVar -> DeBruijn
var i lv = Fix $ Var i lv

abs :: DeBruijn -> LambdaVar -> DeBruijn
abs body lv = Fix $ Abs body lv

app :: DeBruijn -> DeBruijn -> DeBruijn
app e1 e2 = Fix $ App e1 e2

instance Eq1 DeBruijnF where
  liftEq :: (a -> b -> Bool) -> DeBruijnF a -> DeBruijnF b -> Bool
  liftEq eq fa fb = case (fa, fb) of
    (Var i1 _, Var i2 _) -> i1 == i2
    (Abs body1 _, Abs body2 _) -> eq body1 body2
    (App a1 b1, App a2 b2) -> eq a1 a2 && eq b1 b2
    (_, _) -> False

instance Show1 DeBruijnF where
  liftShowsPrec _ _ d (Var i _) = showsPrec d i
  liftShowsPrec sp _ d (Abs body _) =
    showParen False $ showsUnaryWith sp "λ" d body
  liftShowsPrec sp _ d (App e1 e2) = sp d e1 . showChar ' ' . sp d e2

instance Foldable DeBruijnF where
  foldMap :: (Monoid m) => (a -> m) -> DeBruijnF a -> m
  foldMap f = \case
    Var _ _ -> mempty
    Abs body _ -> f body
    App e1 e2 -> f e1 <> f e2

  foldr :: (a -> b -> b) -> b -> DeBruijnF a -> b
  foldr accum seed = \case
    Var _ _ -> seed
    Abs body _ -> accum body seed
    App e1 e2 -> accum e1 (accum e2 seed)

instance Traversable DeBruijnF where
  traverse f = \case
    Var i lv -> pure (Var i lv)
    Abs body lv -> (`Abs` lv) <$> f body
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
type Environment = Map.Map String DeBruijn

type ProgramT m = StateT Environment m

data Error
  = SyntaxError (ParseErrorBundle Text ())
  | UndeclaredVariable String
  | FatalError String

instance Show Error where
  show (SyntaxError se) = show se
  show (UndeclaredVariable uv) =
    " ERROR: undeclared variable " ++
    show uv ++
    "\n- type \":review all\" to see all environment variables you can use\n- type \"" ++
    uv ++ " = <lambda expression>\" to add this variables to environment"
  show (FatalError fe) = fe

type FailableT = ExceptT Error
-------------------------------------------------------------------------------------
