-- A collection of recursion schemes used througout this code but not included in recursion-schemes
{-# LANGUAGE AllowAmbiguousTypes, ExistentialQuantification, FlexibleContexts, TypeFamilies #-}
module Schemes where

import Data.Functor.Foldable

type Algebra f a = f a -> a
type Coalgebra f a = a -> f a

-- DayB type specialized to use Base without requiring pragma AllowAmbiguousTypes
data DayB f g a = forall b c. DayB (Base f b) (Base g c) (b -> c -> a)

lowerDay :: (Recursive g) => (DayB f g a -> a) -> Base f (g -> a) -> g -> a
lowerDay alga fta t = alga (DayB fta (project t) ($))

cata2 :: (Recursive f, Recursive g) => Algebra (DayB f g) a -> f -> g -> a
cata2 = cata . lowerDay

-- An unfold that allows for early return by returning Left
earlyReturnM
    :: (Monad m, Traversable (Base t), Corecursive t)
    => (a -> m (Either t (Base t a)))
    -> (a -> m t)
earlyReturnM f = go
    where go = (either return (fmap embed . traverse go) =<<) . f