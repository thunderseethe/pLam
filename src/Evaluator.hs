{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, InstanceSigs, LambdaCase, MultiParamTypeClasses, TupleSections, UndecidableInstances #-}
module Evaluator where

import           Control.Comonad.Trans.Cofree
import           Control.Monad.Except
import           Control.Monad.State.Strict
import           Data.Functor.Foldable
import qualified Data.Map as Map
import           Data.Text (Text)
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
    => Text
    -> Expression
    -> m Term
evalDefine x y = do
    f <- evalExp y
    modify (Map.insert x f)
    return f

toExpression :: Term -> Expression
toExpression = hoist naturalTransform
  where
    naturalTransform :: Base Term a -> Base Expression a
    naturalTransform = \case
        lv :< Var _ -> VarOrEnv lv
        lv :< Abs body -> Abstraction lv body
        _ :< App e1 e2 -> Application e1 e2

evalExp
    :: (MonadState Environment m, MonadError Error m)
    => Expression
    -> m Term
evalExp = earlyReturnM coalga . ([], )
  where
    coalga (gamma, expr) =
        let right = return . Right
            left  = return . Left
        in  case unfix expr of
                VarOrEnv n -> do
                    env <- get
                    case findDepth n gamma of
                        Right val -> right $ n :< Var val
                        Left (LambdaVar name) -> case Map.lookup name env of
                            Nothing   -> throwError (UndeclaredVariable name)
                            Just term -> left term

                Abstraction arg body -> right $ arg :< Abs (arg : gamma, body)
                Application e1  e2   -> right $ appLambdaVar :< App (gamma, e1) (gamma, e2)

findDepth :: LambdaVar -> [LambdaVar] -> Either LambdaVar Int
findDepth variable = go 0
  where
    go n = \case
        (v : vs) -> if v == variable then Right n else go (n + 1) vs
        []       -> Left variable
