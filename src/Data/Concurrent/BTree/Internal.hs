
{-# OPTIONS -Wall #-}

{-# LANGUAGE ConstraintKinds
, DataKinds
, FlexibleContexts
, FlexibleInstances
, GADTs
, ImpredicativeTypes
, KindSignatures
, LambdaCase
, MultiParamTypeClasses
, ScopedTypeVariables
, TypeOperators 
, TypeSynonymInstances #-}

module Data.Concurrent.BTree.Internal where

import Control.Applicative 
import Control.Concurrent.STM 
import Data.Type.Natural 
import Data.Vector.Sized (Vector(Nil))
import qualified Data.Vector.Sized as V
import Prelude hiding (head, tail, foldl, map)
--import Proof.Equational

data IsRoot = R Bool
data Height = H Nat
data Order = O Nat

type NodeInv order size = (Two :<= order, size :<= (Two :* order))

type LeafInv root size = True ~ (root :|| (One :<<= size))

type InternalInv root order size = True ~ 
  ((root :&& (Two :<<= size)) :|| (order :<<= size))

class Keyed k a where
  tokey :: a -> k

data BNode :: IsRoot -> Height -> Order -> Nat -> * -> * -> * where
  Leaf :: (Keyed k a, NodeInv m n, LeafInv r m) => 
    TVar (Vector a n) -> 
    BNode (R r) (H Zero) (O m) n k a
  Internal :: (Keyed k a, NodeInv m (S n), InternalInv r m (S n)) =>
    TVar (Vector (forall n'. BNode (R False) (H h) (O m) n' k a) (S n), Vector k n) ->
    BNode (R r) (H (S h)) (O m) (S n) k a

empty :: (Two :<= order, Keyed k a) => STM (BNode (R True) (H Zero) (O order) Z k a)
empty = Leaf <$> newTVar Nil

singleton :: (Two :<= order, Keyed k a, {-infer...-} S Z :<= (Two :* order)) => 
  a -> STM (BNode (R True) (H Zero) (O order) (S Z) k a)
singleton x = Leaf <$> newTVar (V.singleton x)

searchLeaf :: (Eq k, Keyed k a) => k -> Vector a n -> [a]
searchLeaf key vec = filter (\x -> key == tokey x) . V.toList $ vec

search :: (Eq k, Keyed k a) => k -> BNode (R r) (H h) (O m) n k a -> STM [a]
search key (Leaf leaf) = searchLeaf key <$> readTVar leaf
search key (Internal node) = undefined node key

