
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
import Control.Concurrent.STM (STM, TVar, readTVar, writeTVar)
import Data.Semigroup ((<>))
import Data.Type.Natural (Nat(S), SNat, (:<<=), (:+), Zero, One, Two, sNatToInt, plusZR, plusSR)
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
  ((n :<<= m) :&& (Not root :|| (m' :<<= n)))
-- Root node should have 2 elems if not a leaf
type InternalInv root n = True ~ 
  (Not root :|| (Two :<<= n))

-- Rtree root h d m m' i a
data RNode :: Bool -> Nat -> Nat -> Nat -> Nat -> * -> * -> * where
  Leaf :: (Spatial i dim a) => 
    TVar ((TreeInv root max min n, n ~ S n') => IVector i dim a (S n')) -> 
    RNode root Zero dim max min i a
  Internal :: (TreeInv root max min n, InternalInv root n, n ~ S n', Ord i, Num i) => 
    TVar (IVector i dim (RNode False h dim max min i a) (S n')) ->
    RNode root (S h) dim max min i a

maxRecords :: (SingRep max) => RNode root h dim max min i a -> SNat max
maxRecords _ = sing

minRecords :: (SingRep min) => RNode root h dim max min i a -> SNat min
minRecords _ = sing

data RTree dim max min i a = forall h. Root (TVar (RNode True h dim max min i a))

{- Search -}

search :: Boundary i dim -> RTree dim max min i a -> STM [IRecord i dim a]
search b (Root root) = readTVar root >>= search' b

search' :: Boundary i dim -> RNode root h dim max min i a -> STM [IRecord i dim a]
search' b (Leaf leaf) = do
  irs <- readTVar leaf 
  return . filter (overlap b . fst) . toList $ irs
search' b (Internal cps) = do
  cps' <- P.map snd . filter (overlap b . fst) . toList <$> readTVar cps
  concat <$> mapM (search' b) cps'

{- Insert -}

insert' :: (SingRep max) => RNode root h dim max min i a -> a -> 
  STM (Maybe (RNode root h dim max min i a, RNode root h dim max min i a))
insert' node@(Leaf leaf) x = do
  irs <- readTVar leaf
  if sNatToInt (sLength irs) < (sNatToInt (maxRecords node) :: Int)
  then 
    let ir = (bounds x, x)
    in writeTVar leaf (ir :- irs) >> return Nothing
  else undefined -- split
insert' node@(Internal icps) x = undefined

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

