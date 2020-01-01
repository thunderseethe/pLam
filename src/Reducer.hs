{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Reducer where

import           Control.Comonad.Trans.Cofree
--import qualified Control.Comonad.Cofree as Cofree
import           Control.Monad.State

import           Data.Functor.Foldable   hiding ( fold )
import           Data.Set                hiding ( fold )
import           Prelude                 hiding ( filter
                                                , map
                                                , null
                                                , rem
                                                , abs
                                                )

import           Syntax
import           Schemes

--------------------------------------------------------------------------------
-- extracting all variales from a input expression
---- returns Set of lambda variables
vars :: Term -> Set Int
vars = cata $ \case
    _ :< Var i  -> singleton i
    _ :< Abs body  -> body
    _ :< App e1 e2 -> union e1 e2

--------------------------------------------------------------------------------
-- extracting free variales from a input expression
---- returns Set of lambda variables
freeVars :: Term -> Set Int
freeVars = cata $ \case
    _ :< Var i     -> if i < 0 then singleton i else empty
    _ :< Abs body  -> body
    _ :< App e1   e2 -> union e1 e2

--------------------------------------------------------------------------------
-- extracting bound variales from a input expression
---- returns Set of lambda variables
boundVars :: Term -> Set Int
boundVars = cata $ \case
    _ :< Var i     -> if i > 0 then singleton i else empty
    _ :< Abs body  -> body
    _ :< App e1   e2 -> union e1 e2

--------------------------------------------------------------------------------
-- returns a functions, which substitutes all free* occurences of x by n
---- if expression is a variable: sub if names match, else return same
---- if expression is an application: sub both applicants
---- if expression is an abstraction:
------ if vars are the same, leave unchanged
------ if x is NOT in free vars in the body, there is no x to be substituted
------ if x is in free vars in the body AND abstraction var is not in free vars of n, substitute in the body
------ else, we need a fresh var because abstraction variable y is in free vars of term to be substituted. fresh var is y'
subst :: Term -> Term -> Term
subst sub expr = cata alga expr (0, sub)
 where
  alga
    :: Base Term ((Int, Term) -> Term)
    -> ((Int, Term) -> Term)
  alga = \case
    lv :< Var i -> \(n, subTerm) -> if i == n then subTerm else var i lv
    lv :< Abs body -> \(n, subTerm) -> abs (body (n + 1, shift 1 0 subTerm)) lv
    _ :< App e1 e2 -> \s -> app (e1 s) (e2 s)


shift :: Int -> Int -> Term -> Term
shift d c = ana coalga . (,,) d c
 where
  coalga :: (Int, Int, Term) -> Base Term (Int, Int, Term)
  coalga (delta, cutoff, e) = case project e of
    lv :< Var i -> let n = if i >= cutoff then i + delta else i in lv :< Var n
    lv :< Abs body -> lv :< Abs (delta, cutoff + 1, body)
    lv :< App e1   e2 -> lv :< App (delta, cutoff, e1) (delta, cutoff, e2)

--------------------------------------------------------------------------------
-- ALPHA equivalence
--------------------------------------------------------------------------------
-- returns whether 2 lambda expressions are alpha equivalent
---- variables derive Eq
---- applications are alpha equivalent if their corresponding parts are
---- we substitute bounding var of one abstraction into body of another and compare bodies
alphaEquiv :: Term -> Term -> Bool
alphaEquiv = cata2 convolution
  where
    convolution :: DayB Term Term Bool -> Bool
    convolution (DayB f g fn) = case (f, g) of
      (_ :< Var i1, _ :< Var i2) -> i1 == i2
      (_ :< Abs body1, _ :< Abs body2) -> fn body1 body2
      (_ :< App a1 b1, _ :< App a2 b2) -> fn a1 a2 && fn b1 b2
      (_, _) -> False
      

--------------------------------------------------------------------------------
-- BETA reduction
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- determines whether given lambda expression contains at least one beta redex
hasBetaRedex :: Term -> Bool
hasBetaRedex = para alga
  where
    alga :: Base Term (Term, Bool) -> Bool
    alga = \case
      _ :< App (expr, left) (_, right) -> case project expr of
        _ :< Abs _ -> True
        _ -> left || right
      _ :< _ -> False

--------------------------------------------------------------------------------
-- performs one step beta reduction and count steps
---- application of abstraction to an expression beta reduces by definition substituting expression for bounding var in the body of abstraction
---- (other type) application reduces its applicants (first left one to beta nf)
---- reducing abstraction is reducing its body
---- variable doesnt reduce
betaReduction :: Term -> State Int Term
betaReduction term = state $ \k -> cata (alga k) term
  where
    alga :: Int -> Base Term (Term, Int) -> (Term, Int)
    alga k = \case
      lv :< Var i -> (var i lv, k)
      lv :< Abs (body, n) -> (abs body lv, n)
      _ :< App (expr, n) (arg, m) -> case project expr of
        _ :< Abs body -> (shift (-1) 0 $ subst (shift 1 0 arg) body, n + m + 1)
        _ -> (app expr arg, n + m)

--------------------------------------------------------------------------------
-- computes the beta normal form of a lambda term and count steps
---- do one step beta reduction if there are any redexes left
betaNF :: Term -> State Int Term
betaNF = go
 where
  go :: Term -> State Int Term
  go ex = if hasBetaRedex ex
    then betaReduction ex >>= go
    else return ex