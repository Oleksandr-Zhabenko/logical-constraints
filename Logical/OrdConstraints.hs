-- |
-- Module      :  Logical.OrdConstraints
-- Copyright   :  (c) Oleksandr Zhabenko 2022
-- License     :  MIT
-- Stability   :  Experimental
-- Maintainer  :  oleksandr.zhabenko@yahoo.com
--
-- Some simple logical encoding 'syntactical sugar' to represent point-wise or intervals-based logics.

module Logical.OrdConstraints where

import Data.Foldable
import Data.Maybe

-- | Data type to encode the simple logical contstraints for some 'Ord'ered data type value to be kept in some bounds (to lay in some intervals or points). 'O' constructor  encodes
-- point-wise logics, and 'C' encodes intervals logics.
data OrdConstraints a = O [a] | C [a] deriving (Eq, Ord, Show, Read)

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
 | otherwise = False
ordCs2Predicate1 x@(C xs) y
 | validOrdCs x = any (\(t:u:_) -> y >= t && y <= u) . f $ xs
 | otherwise = False
    where f (x:y:xs) = [x,y]:f xs
          f _ = []

ordCs2HPred1 :: (Ord a, Foldable t1) => OrdCs t1 a -> a -> Bool
ordCs2HPred1 cs y = any (\c -> ordCs2Predicate1 c y) $ cs

ordCs2Predicate :: Ord a => OrdConstraints a -> [a] -> Bool
ordCs2Predicate x@(O xs) ys
 | validOrdCs x = any (== head ys) xs
 | otherwise = False
ordCs2Predicate x@(C xs) ys
 | validOrdCs x = any (\(t:u:_) -> head ys >= t && head ys <= u) . f $ xs
 | otherwise = False
    where f (x:y:xs) = [x,y]:f xs
          f _ = []

ordCs2HPred :: (Ord a, Foldable t1) => OrdCs t1 a -> [a] -> Bool
ordCs2HPred cs ys = any (\c -> ordCs2Predicate c ys) $ cs

ordCs2PredicateG :: (Ord a, Foldable t) => OrdConstraints a -> (t a -> Maybe a) -> t a -> Bool
ordCs2PredicateG x@(O xs) p ys
 | validOrdCs x = any (\k -> (fromMaybe False . fmap (== k) . p $ ys)) xs
 | otherwise = False
ordCs2PredicateG x@(C xs) p ys
 | validOrdCs x = any (\(t:u:_) -> fromMaybe False . fmap (\k -> k >= t && k <= u) . p $ ys) . f $ xs
 | otherwise = False
    where f (x:y:xs) = [x,y]:f xs
          f _ = []

ordCs2HPredG :: (Ord a, Foldable t, Foldable t1) => OrdCs t1 a -> (t a -> Maybe a) -> t a -> Bool
ordCs2HPredG cs p ys = any (\c -> ordCs2PredicateG c p ys) $ cs


