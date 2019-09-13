{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Reducer where

import Control.Comonad.Cofree

import Data.Functor.Foldable hiding (fold)
import qualified Data.List as List
import Data.Set hiding (fold)
import Data.Tree
import Prelude hiding (filter, map, null, rem, abs)
import System.Console.Haskeline

import Syntax

--------------------------------------------------------------------------------
-- folding set operations on a lambda expression
-- used in vars and freeVars
---- insert and delete have same signature: (LambdaVar -> a -> a)
---- union has signature: (a -> a -> a)
---- singleton has signature: (LambdaVar -> a)
---- returns Set a
fold ::
     (LambdaVar -> a -> a)
  -> (a -> a -> a)
  -> (LambdaVar -> a)
  -> Expression
  -> a
fold _ _ h (Variable v) = h v
fold f g h (Abstraction v e) = f v (fold f g h e)
fold f g h (Application e1 e2) = g (fold f g h e1) (fold f g h e2)

--------------------------------------------------------------------------------
-- extracting all variales from a input expression
---- returns Set of lambda variables
vars :: Expression -> Set LambdaVar
vars = fold insert union singleton

dbVars :: DeBruijn -> Set Int
dbVars = cata alga
  where
    alga =
      \case
        Var i _ -> singleton i
        Abs body _ -> body
        App e1 e2 -> union e1 e2

--------------------------------------------------------------------------------
-- extracting free variales from a input expression
---- returns Set of lambda variables
freeVars :: Expression -> Set LambdaVar
freeVars = fold delete union singleton

dbFreeVars :: DeBruijn -> Set Int
dbFreeVars = cata alga
  where
    alga =
      \case
        Var i _ ->
          if i < 0
            then singleton i
            else empty
        Abs body _ -> body
        App e1 e2 -> union e1 e2

--------------------------------------------------------------------------------
-- extracting bound variales from a input expression
---- returns Set of lambda variables
boundVars :: Expression -> Set LambdaVar
boundVars ex = difference (vars ex) (freeVars ex)

dbBoundVars :: DeBruijn -> Set Int
dbBoundVars = cata alga
  where
    alga =
      \case
        Var i _ ->
          if i > 0
            then singleton i
            else empty
        Abs body _ -> body
        App e1 e2 -> union e1 e2

--------------------------------------------------------------------------------
-- returns a functions, which substitutes all free* occurences of x by n
---- if expression is a variable: sub if names match, else return same
---- if expression is an application: sub both applicants
---- if expression is an abstraction:
------ if vars are the same, leave unchanged
------ if x is NOT in free vars in the body, there is no x to be substituted
------ if x is in free vars in the body AND abstraction var is not in free vars of n, substitute in the body
------ else, we need a fresh var because abstraction variable y is in free vars of term to be substituted. fresh var is y'
sub :: LambdaVar -> Expression -> Expression -> Expression
sub x n (Variable y)
  | x == y = n
  | x /= y = Variable y
sub x n (Application p q) = Application (sub x n p) (sub x n q)
sub x n (Abstraction y@(LambdaVar name num) p)
  | x == y = Abstraction y p
  | not $ member x (freeVars p) = Abstraction y p
  | member x (freeVars p) && not (member y (freeVars n)) =
    Abstraction y (sub x n p)
  | member x (freeVars p) && member y (freeVars n) =
    let new = LambdaVar name (num + 1)
    in Abstraction new $ sub x n $ sub y (Variable new) p

subst :: DeBruijn -> DeBruijn -> DeBruijn
subst sub expr = cata alga expr (0, sub)
  where
    alga :: Base DeBruijn ((Int, DeBruijn) -> DeBruijn) -> ((Int, DeBruijn) -> DeBruijn)
    alga = \case
      Var i lv -> \(n, sub) -> if i == n then sub else var i lv
      Abs body lv -> \(n, sub) -> abs (body (n + 1, shift 1 0 sub)) lv
      App e1 e2 -> \s -> app (e1 s) (e2 s)


shift :: Int -> Int -> DeBruijn -> DeBruijn
shift d c = ana coalga . (,,) d c
  where
    coalga :: (Int, Int, DeBruijn) -> Base DeBruijn (Int, Int, DeBruijn)
    coalga (d, c, e) = case unfix e of
      Var i lv ->
        let n = if i >= c then i + d else i in Var n lv
      Abs body lv -> Abs (d, c+1, body) lv
      App e1 e2 -> App (d, c, e1) (d, c, e2)

--------------------------------------------------------------------------------
-- ALPHA equivalence
--------------------------------------------------------------------------------
-- returns whether 2 lambda expressions are alpha equivalent
---- variables derive Eq
---- applications are alpha equivalent if their corresponding parts are
---- we substitute bounding var of one abstraction into body of another and compare bodies
alphaEquiv :: Expression -> Expression -> Bool
alphaEquiv (Variable x) (Variable y) = x == y
alphaEquiv (Application a b) (Application x y) =
  alphaEquiv a x && alphaEquiv b y
alphaEquiv abs1@(Abstraction v1 (Variable w1)) abs2@(Abstraction v2 (Variable w2))
  | v1 == w1 && v2 /= w2 = False
  | v1 /= w1 && v2 == w2 = False
  | otherwise = True
alphaEquiv (Abstraction x f) (Abstraction y g) =
  alphaEquiv f $ sub y (Variable x) g
alphaEquiv _ _ = False

dbAlphaEquiv :: DeBruijn -> DeBruijn -> Bool
dbAlphaEquiv = go
  where
    go :: DeBruijn -> DeBruijn -> Bool
    go a b = case (unfix a, unfix b) of
      (Var i _, Var j _) -> i == j
      (Abs b1 _, Abs b2 _) -> go b1 b2
      (App e1 e2, App r1 r2) -> go e1 r1 && go e2 r2
      (_, _) -> False


--------------------------------------------------------------------------------
-- BETA reduction
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- finds all beta redexes of given lambda term
----- variable has no redexes
----- application of abstraction to expression is itself a redex. concatenate it with any inner redexes
----- redexes of (other type) application are just concatenated redexes of applicants
----- redexes of abstraction are redexes of its body
betaRedexes :: Expression -> [Expression]
betaRedexes (Variable _) = []
betaRedexes e@(Application (Abstraction _ e1) e2) =
  e : (betaRedexes e1 ++ betaRedexes e2)
betaRedexes (Application e1 e2) = betaRedexes e1 ++ betaRedexes e2
betaRedexes (Abstraction _ f) = betaRedexes f

dbBetaRedexes :: DeBruijn -> [DeBruijn]
dbBetaRedexes = para alga
  where
    alga = \case
      App (Fix (Abs e1 lv), l1) (e2, l2) -> (app (Syntax.abs e1 lv) e2) : l1 ++ l2
      App (_, l1) (_, l2) -> l1 ++ l2
      Abs (_, lst) _ -> lst
      Var _ _ -> []


--------------------------------------------------------------------------------
-- determines whether given lambda expression contains at least one beta redex
hasBetaRedex :: Expression -> Bool
hasBetaRedex = not . List.null . betaRedexes

dbHasBetaRedex :: DeBruijn -> Bool
dbHasBetaRedex = not . List.null . dbBetaRedexes

--------------------------------------------------------------------------------
-- performs one step beta reduction and count steps
---- application of abstraction to an expression beta reduces by definition substituting expression for bounding var in the body of abstraction
---- (other type) application reduces its applicants (first left one to beta nf)
---- reducing abstraction is reducing its body
---- variable doesnt reduce
dbBetaReduction :: DeBruijn -> (Int, DeBruijn)
dbBetaReduction = go 0 
  where 
    go n e = case unfix e of
      Var i lv -> (n, var i lv)
      Abs body lv ->
        let (n', body') = go n body
        in (n', Syntax.abs body' lv)
      App (Fix (Abs body _)) arg -> (n + 1, shift (-1) 0 $ subst (shift 1 0 arg) body)
      App e1 e2 -> if dbHasBetaRedex e1
                    then let (n', e1') = go n e1 in (n', app e1' e2)
                    else let (n', e2') = go n e2 in (n', app e1 e2')

beta :: DeBruijn -> (Int, DeBruijn)
beta = histo alga
  where
    alga :: Base DeBruijn (Cofree (Base DeBruijn) (Int, DeBruijn)) -> (Int, DeBruijn)
    alga = \case
      Var i lv -> (0, var i lv)
      Abs ((n, body) :< _) lv -> (n, abs body lv)
      App (_ :< Abs ((n, body) :< _) _) ((m, arg) :< _) -> (n + m + 1, shift (-1) 0 $ subst (shift 1 0 arg) body)
      App ((n, e1) :< _) ((m, e2) :< _) -> (n + m, app e1 e2)
 

betaReduction :: EvaluateOption -> Int -> Expression -> (Expression, Int)
betaReduction _ n (Variable v) = (Variable v, n)
betaReduction evop n (Abstraction v e) = let eb = betaReduction evop n e in
                                         (Abstraction v (fst eb), snd eb)
betaReduction evop n (Application (Abstraction v e) a)
  | (evop == CallByValue) && (hasBetaRedex a) = let ab = betaReduction CallByValue n a in
                                                (Application (Abstraction v e) (fst ab), snd ab)
  | otherwise = (sub v a e, n+1)
betaReduction evop n (Application e1 e2)
  | hasBetaRedex e1 = let e1b = betaReduction evop n e1 in
                      (Application (fst e1b) e2, snd e1b)
  | otherwise = let e2b = betaReduction evop n e2 in
                (Application e1 (fst e2b), snd e2b)

--------------------------------------------------------------------------------
-- computes the beta normal form of a lambda term and count steps
---- do one step beta reduction if there are any redexes left
betaNF :: EvaluateOption -> Int -> Expression -> (Expression, Int)
betaNF CallByValue n ex
  | hasBetaRedex ex = let exb = betaReduction CallByValue n ex in
                      betaNF CallByValue (snd exb) (fst exb)
  | otherwise = (ex, n)
betaNF _ n ex
  | hasBetaRedex ex = let exb = betaReduction None n ex in
                      betaNF None (snd exb) (fst exb)
  | otherwise = (ex, n)
