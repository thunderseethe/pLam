{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
module Evaluator where

import Control.Monad.Except
import Control.Monad.State.Strict
import Control.Monad.Signatures
import Data.Char
import Debug.Trace
import System.Console.Haskeline

import HaskelineClass
import Syntax


-------------------------------------------------------------------------------------
type Eval = FailableT (ProgramT (HaskelineT IO))
runEvalToIO :: Environment -> Settings IO -> Eval a -> IO (Either Error a, Environment)
runEvalToIO initEnv settings eval = let
    stateT = runExceptT eval
    haskelineT = runStateT stateT initEnv
    in runHaskelineT settings haskelineT

evalVar :: (MonadState Environment m, MonadError Error m) => String -> m Expression
evalVar a = do
    e <- get
    maybe (throwError $ UndeclaredVariable a) return $ lookup a e

evalAbs
    :: (MonadState Environment m, MonadError Error m) => LambdaVar -> Expression -> m Expression
evalAbs x@(LambdaVar n i) y = do
    y' <- evalExp y
    return $ Abstraction x y'

evalApp
    :: (MonadState Environment m, MonadError Error m) => Expression -> Expression -> m Expression
evalApp f x = do
    f' <- evalExp f
    x' <- evalExp x
    return $ Application f' x'

evalExp :: (MonadState Environment m, MonadError Error m) => Expression -> m Expression
evalExp x@(Variable (LambdaVar n i)) = return x
evalExp (  Abstraction v e         ) = evalAbs v e
evalExp (  Application m n         ) = evalApp m n
evalExp (  EnvironmentVar ev       ) = evalVar ev
-------------------------------------------------------------------------------------

evalDefine
    :: (MonadState Environment m, MonadError Error m) => String -> Expression -> m Expression
evalDefine x y = do
    f <- evalExp y
    modify ((x, f) :)
    return f


