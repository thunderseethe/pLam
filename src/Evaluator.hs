{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, InstanceSigs, LambdaCase, MultiParamTypeClasses, TupleSections, UndecidableInstances #-}
module Evaluator where

import           Control.Monad.Except
import           Control.Monad.State.Strict
import           Data.Functor.Foldable
import           System.Console.Haskeline

import           HaskelineClass
import           Syntax
import           Schemes


-------------------------------------------------------------------------------------
type Eval = FailableT (ProgramT (HaskelineT IO))

runEvalToIO
    :: Environment -> Settings IO -> Eval a -> IO (Either Error a, Environment)
runEvalToIO initEnv settings eval =
    let stateT     = runExceptT eval
        haskelineT = runStateT stateT initEnv
    in  runHaskelineT settings haskelineT

evalDefine
    :: (MonadState Environment m, MonadError Error m)
    => String
    -> Expression
    -> m DeBruijn
evalDefine x y = do
    f <- evalExp y
    modify ((x, f) :)
    return f

toExpression :: DeBruijn -> Expression
toExpression = hoist naturalTransform
  where
    naturalTransform :: Base DeBruijn a -> Base Expression a
    naturalTransform = \case
        Var _ lv -> VarOrEnv lv
        Abs body lv -> Abstraction lv body
        App e1 e2 -> Application e1 e2

evalExp
    :: (MonadState Environment m, MonadError Error m)
    => Expression
    -> m DeBruijn
evalExp = earlyReturnM coalga . ([], )
  where
    coalga (gamma, expr) =
        let right = return . Right
            left  = return . Left
        in  case unfix expr of
                VarOrEnv n -> do
                    env <- get
                    case findDepth n gamma of
                        Right val -> right $ Var val n
                        Left nm -> case lookup (name nm) env of
                            Nothing   -> throwError (UndeclaredVariable $ name nm)
                            Just term -> left term

                Abstraction arg body -> right $ Abs (arg : gamma, body) arg
                Application e1  e2   -> right $ App (gamma, e1) (gamma, e2)

findDepth :: LambdaVar -> [LambdaVar] -> Either LambdaVar Int
findDepth variable = go 0
  where
    go n = \case
        (v : vs) -> if v == variable then Right n else go (n + 1) vs
        []       -> Left variable
