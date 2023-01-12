{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_HADDOCK show-extensions #-}

-- |
-- Module      :  Logical.OrdConstraints
-- Copyright   :  (c) Oleksandr Zhabenko 2022-2023
-- License     :  MIT
-- Stability   :  Experimental
-- Maintainer  :  oleksandr.zhabenko@yahoo.com
--
-- Some simple logical encoding 'syntactical sugar' to represent point-wise or intervals-based logics.
-- If you would like to use data types not in the functions of the module  imported, but in your
-- own ones, please, consider using before the 'validOrdCs' function for them. If you use just
-- the functions defined here, you do not need to use it before because it is used internally.

module Logical.OrdConstraints where

import Control.Exception
import Data.Foldable (Foldable, any)
import GHC.Base hiding (O)
import GHC.List hiding (any)
import Text.Show 
import Text.Read
import GHC.Real (rem)
import Data.Maybe (fromMaybe)

-- | Data type to encode the simple logical contstraints for some 'Ord'ered data type value to be kept in some bounds (to lay in some intervals or points). 'O' constructor  encodes
-- point-wise logics, and 'C' encodes intervals logics.
data OrdConstraints a = O [a] | C [a] deriving (Eq, Ord, Show, Read)

-- | Primary intention: the @t@ here refers to 'Foldable' @t@.
type OrdCs t a = t (OrdConstraints a)

-- | The predicate to check whether the data is  encoded logically correct just enough to be used by the functions in the library (minimal necessary validation). Checks whether 
-- at least just one point or interval is set.
validOrdCs :: Ord a =>  OrdConstraints a -> Bool
validOrdCs (O (_:_)) = True
validOrdCs (C xs@(_:_:_)) = (length xs `rem` 2) == 0
validOrdCs _ = False

ordCs2Predicate1 :: Ord a => OrdConstraints a -> a -> Bool
ordCs2Predicate1 x@(O xs) y
 | validOrdCs x = any (== y) xs
 | otherwise = error "Logical.OrdConstraints.ordCs2Predicate1: Not valid logical constraint by constrution semantics."
ordCs2Predicate1 x@(C xs) y
 | validOrdCs x = any (\(t:u:_) -> y >= t && y <= u) . f $ xs
 | otherwise = error "Logical.OrdConstraints.ordCs2Predicate1: Not valid logical constraint by constrution semantics." 
    where f (x:y:xs) = [x,y]:f xs
          f [] = []

ordCs2HPred1 :: (Ord a, Foldable t1) => OrdCs t1 a -> a -> Bool
ordCs2HPred1 cs y = any (\c -> ordCs2Predicate1 c y) $ cs

-- | Just the head of the list is used. Therefore, is intended to be used mainly with the singleton list as the second argument.
ordCs2Predicate :: Ord a => OrdConstraints a -> [a] -> Bool
ordCs2Predicate x ys
 | null ys = False
 | otherwise = ordCs2Predicate1 x (head ys)
{-# INLINE ordCs2Predicate #-}

-- | Just the head of the list is used. Therefore, is intended to be used mainly with the singleton list as the second argument.
ordCs2HPred :: (Ord a, Foldable t1) => OrdCs t1 a -> [a] -> Bool
ordCs2HPred cs ys 
 | null ys = False
 | otherwise = any (\c -> ordCs2Predicate1 c (head ys)) $ cs

ordCs2PredicateG :: (Ord a, Foldable t) => OrdConstraints a -> (t a -> Maybe a) -> t a -> Bool
ordCs2PredicateG x@(O xs) p ys
 | validOrdCs x = any (\k -> (fromMaybe False . fmap (== k) . p $ ys)) xs
 | otherwise = error "Logical.OrdConstraints.ordCs2PredicateG: Not valid logical constraint by constrution semantics."
ordCs2PredicateG x@(C xs) p ys
 | validOrdCs x = any (\(t:u:_) -> fromMaybe False . fmap (\k -> k >= t && k <= u) . p $ ys) . f $ xs
 | otherwise = error "Logical.OrdConstraints.ordCs2PredicateG: Not valid logical constraint by constrution semantics."
    where f (x:y:xs) = [x,y]:f xs
          f [] = []

ordCs2HPredG :: (Ord a, Foldable t, Foldable t1) => OrdCs t1 a -> (t a -> Maybe a) -> t a -> Bool
ordCs2HPredG cs p ys = any (\c -> ordCs2PredicateG c p ys) $ cs


