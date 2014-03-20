
{-# OPTIONS -Wall #-}

{-# LANGUAGE ConstraintKinds
, DataKinds
, FlexibleInstances
, GADTs
, ImpredicativeTypes
, KindSignatures
, LambdaCase
, MultiParamTypeClasses
, RankNTypes
, ScopedTypeVariables
, TypeOperators 
, TypeSynonymInstances #-}

module Data.Concurrent.RTree.Internal where

import Control.Applicative ((<$>))
import Control.Concurrent.STM (STM, TVar, readTVar)
import Data.Semigroup ((<>))
import Data.Type.Natural (Nat(S), (:<<=), (:+), Zero, One, Two, plusZR, plusSR)
import Data.Vector.Sized (Vector(Nil,(:-)), toList, head, sLength, map)
import qualified Prelude as P
import Prelude hiding (head, tail, foldl, map)
import Proof.Equational

import Data.Concurrent.RTree.Geometry (Boundary, Spatial, bounds, overlap, size)

type IRecord i dim a = (Boundary i dim, a)

type IVector i dim a n = Vector (IRecord i dim a) n

-- All nodes have no more than m elements and
-- have at least m' elements unless it is a root
type TreeInv root m m' n = True ~
  ((n :<<= m) :&& ((root :&& (One :<<= n)) :|| (m' :<<= n)))
-- Root node should have 2 elems if not a leaf
type InternalInv root n = True ~ 
  (Not root :|| (Two :<<= n))

-- Rtree root h d m m' i a
data RNode :: Bool -> Nat -> Nat -> Nat -> Nat -> * -> * -> * where
  Leaf :: (Spatial i dim a, TreeInv root max min n, n ~ S n') => 
    TVar (IVector i dim a (S n')) -> 
    RNode root Zero dim max min i a
  Internal :: (TreeInv root max min n, InternalInv root n, n ~ S n', Ord i, Num i) => 
    TVar (IVector i dim (RNode False h dim max min i a) (S n')) ->
    RNode root (S h) dim max min i a

data RTree dim max min i a = forall h. Root (TVar (RNode True h dim max min i a))

search :: Boundary i dim -> RTree dim max min i a -> STM [IRecord i dim a]
search b (Root root) = readTVar root >>= search' b

search' :: Boundary i dim -> 
  RNode root h dim max min i a -> 
  STM [IRecord i dim a]
search' b (Leaf irs) = filter (overlap b . fst) . toList <$> readTVar irs
search' b (Internal cps) = do
  cps' <- P.map snd . filter (overlap b . fst) . toList <$> readTVar cps
  concat <$> mapM (search' b) cps'

insert' :: RNode root h dim max min i a -> a -> STM ()
insert' (Leaf irs) x = undefined
insert' (Internal icps) x = undefined

minBubbleStep :: (Ord a) => a -> Vector a n -> Vector a (S n)
minBubbleStep x Nil       = x :- Nil
minBubbleStep x (y :- ys) = min x y :- max x y :- ys

minBubble :: (Ord a) => Vector a n -> Vector a n
minBubble v = crank minBubbleStep v where

crank' :: (forall m. a -> Vector a m -> Vector a (S m)) -> Vector a m -> Vector a n -> Vector a (n :+ m)
crank' f acc Nil = acc
crank' f acc (x :- xs) = 
  let newAcc = f x acc 
  in coerce (symmetry $ plusSR (sLength xs) (sLength acc)) $ crank' f newAcc xs

crank :: (forall m. a -> Vector a m -> Vector a (S m)) -> Vector a n -> Vector a n
crank _ Nil = Nil
crank f v = coerce (plusZR (sLength v)) $ crank' f Nil v

data Tag a b = Tag { gettag :: a, untag ::  b }

instance Eq a => Eq (Tag a b) where
  (Tag a1 _) == (Tag a2 _) = a1 == a2

instance Ord a => Ord (Tag a b) where
  compare (Tag a1 _) (Tag a2 _) = compare a1 a2

chooseSubNode :: (Spatial i dim a, Ord i, Num i) => 
  IVector i dim (RNode False h dim max min i a) (S n) ->
  a -> RNode False h dim max min i a
chooseSubNode icpts x = 
  let tag icpt = Tag (size (fst icpt <> bounds x) - size (fst icpt)) icpt
      bubbleIcpt = minBubble . map tag $ icpts
  in snd . head . map untag $ bubbleIcpt
