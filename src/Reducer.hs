{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Reducer where

import           Control.Comonad.Cofree
import           Control.Monad.State

import           Data.Functor.Classes
import           Data.Functor.Foldable   hiding ( fold )
import qualified Data.List                     as List
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
vars :: DeBruijn -> Set Int
vars = cata alga
 where
  alga = \case
    Var i    _  -> singleton i
    Abs body _  -> body
    App e1   e2 -> union e1 e2

--------------------------------------------------------------------------------
-- extracting free variales from a input expression
---- returns Set of lambda variables
freeVars :: DeBruijn -> Set Int
freeVars = cata alga
 where
  alga = \case
    Var i    _  -> if i < 0 then singleton i else empty
    Abs body _  -> body
    App e1   e2 -> union e1 e2

--------------------------------------------------------------------------------
-- extracting bound variales from a input expression
---- returns Set of lambda variables
boundVars :: DeBruijn -> Set Int
boundVars = cata alga
 where
  alga = \case
    Var i    _  -> if i > 0 then singleton i else empty
    Abs body _  -> body
    App e1   e2 -> union e1 e2

--------------------------------------------------------------------------------
-- returns a functions, which substitutes all free* occurences of x by n
---- if expression is a variable: sub if names match, else return same
---- if expression is an application: sub both applicants
---- if expression is an abstraction:
------ if vars are the same, leave unchanged
------ if x is NOT in free vars in the body, there is no x to be substituted
------ if x is in free vars in the body AND abstraction var is not in free vars of n, substitute in the body
------ else, we need a fresh var because abstraction variable y is in free vars of term to be substituted. fresh var is y'
subst :: DeBruijn -> DeBruijn -> DeBruijn
subst sub expr = cata alga expr (0, sub)
 where
  alga
    :: Base DeBruijn ((Int, DeBruijn) -> DeBruijn)
    -> ((Int, DeBruijn) -> DeBruijn)
  alga = \case
    Var i    lv -> \(n, subTerm) -> if i == n then subTerm else var i lv
    Abs body lv -> \(n, subTerm) -> abs (body (n + 1, shift 1 0 subTerm)) lv
    App e1   e2 -> \s -> app (e1 s) (e2 s)


shift :: Int -> Int -> DeBruijn -> DeBruijn
shift d c = ana coalga . (,,) d c
 where
  coalga :: (Int, Int, DeBruijn) -> Base DeBruijn (Int, Int, DeBruijn)
  coalga (delta, cutoff, e) = case unfix e of
    Var i    lv -> let n = if i >= cutoff then i + delta else i in Var n lv
    Abs body lv -> Abs (delta, cutoff + 1, body) lv
    App e1   e2 -> App (delta, cutoff, e1) (delta, cutoff, e2)

--------------------------------------------------------------------------------
-- ALPHA equivalence
--------------------------------------------------------------------------------
-- returns whether 2 lambda expressions are alpha equivalent
---- variables derive Eq
---- applications are alpha equivalent if their corresponding parts are
---- we substitute bounding var of one abstraction into body of another and compare bodies
alphaEquiv :: DeBruijn -> DeBruijn -> Bool
alphaEquiv = cata2 convolution
  where
    convolution :: DayB DeBruijn DeBruijn Bool -> Bool
    convolution (DayB f g fn) =
      liftEq fn f g

--------------------------------------------------------------------------------
-- BETA reduction
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- finds all beta redexes of given lambda term
----- variable has no redexes
----- application of abstraction to expression is itself a redex. concatenate it with any inner redexes
----- redexes of (other type) application are just concatenated redexes of applicants
----- redexes of abstraction are redexes of its body
betaRedexes :: DeBruijn -> [DeBruijn]
betaRedexes = para alga
 where
  alga = \case
    App (Fix (Abs e1 lv), l1) (e2, l2) ->
      app (Syntax.abs e1 lv) e2 : l1 ++ l2
    App (_, l1 ) (_, l2) -> l1 ++ l2
    Abs (_, lst) _       -> lst
    Var _        _       -> []


--------------------------------------------------------------------------------
-- determines whether given lambda expression contains at least one beta redex
hasBetaRedex :: DeBruijn -> Bool
hasBetaRedex = not . List.null . betaRedexes

--------------------------------------------------------------------------------
-- performs one step beta reduction and count steps
---- application of abstraction to an expression beta reduces by definition substituting expression for bounding var in the body of abstraction
---- (other type) application reduces its applicants (first left one to beta nf)
---- reducing abstraction is reducing its body
---- variable doesnt reduce
betaReduction :: EvaluateOption -> DeBruijn -> State Int DeBruijn
betaReduction _ term = state $ \k -> histo (alga k) term
 where
  alga
    :: Int -> Base DeBruijn (Cofree (Base DeBruijn) (DeBruijn, Int)) -> (DeBruijn, Int)
  alga k = \case
    Var i                lv -> (var i lv, k)
    Abs ((body, n) :< _) lv -> (abs body lv, n)
    App (_ :< Abs ((body, n) :< _) _) ((arg, m) :< _) ->
      (shift (-1) 0 $ subst (shift 1 0 arg) body, n + m + 1)
    App ((e1, n) :< _) ((e2, m) :< _) -> (app e1 e2, n + m)


--------------------------------------------------------------------------------
-- computes the beta normal form of a lambda term and count steps
---- do one step beta reduction if there are any redexes left
betaNF :: EvaluateOption -> DeBruijn -> State Int DeBruijn
betaNF cbt = go
 where
  go :: DeBruijn -> State Int DeBruijn
  go ex = if hasBetaRedex ex
    then betaReduction cbt ex >>= go
    else return ex