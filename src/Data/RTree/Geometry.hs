
{-# OPTIONS -Wall -Werror #-}

{-# LANGUAGE 
DataKinds
, FlexibleContexts
, GADTs
, KindSignatures 
, MultiParamTypeClasses
, TemplateHaskell #-}

module Data.Concurrent.RTree.Geometry 
  ( Boundary
  , Spatial
  , bounds
  , overlap
  , size
  ) where

import Data.Semigroup (Semigroup, (<>))
import Data.Vector.Sized (Vector, all, map, product, zipWithSame)
import Prelude hiding (all, map, product)

data Interval i = (Num i, Ord i) => I (i,i)

instance Semigroup (Interval i) where
  (I (a1,a2)) <> (I (b1,b2)) = I (min a1 b1, max a2 b2) 

contains :: Interval i -> i -> Bool
contains (I (i1,i2)) test = (i1 <= test) && (test <= i2)

overlapInterval :: Interval i -> Interval i -> Bool
overlapInterval a (I (i1,i2)) = 
  contains a i1 || contains a i2

sizeInterval :: Interval i -> i
sizeInterval (I (i1,i2)) = i2 - i1

data Boundary i d = (Num i, Ord i) => B { intervals :: Vector (Interval i) d }

instance Semigroup (Interval i) => Semigroup (Boundary i d) where
  (B is1) <> (B is2) = B $ zipWithSame (<>) is1 is2

overlap :: Boundary i d -> Boundary i d -> Bool
overlap (B b1) (B b2) = all id $ zipWithSame overlapInterval b1 b2

size :: (Num i) => Boundary i d -> i
size = product . map sizeInterval . intervals

class Num i => Spatial i d a where
  bounds :: a -> Boundary i d 

