
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

module Data.BTree.Internal (empty, singleton, search, insert) where

import Control.Applicative ()
import Data.Type.Natural 
import Data.Vector.Sized (Vector(Nil,(:-)))
import qualified Data.Vector.Sized as V
import Prelude hiding (head, tail, foldl, map)
import Proof.Equational
import Unsafe.Coerce

type MaxSize order = Two :+ order

type NodeInv order size = True ~ (size :<<= MaxSize order)

type LeafInv root size = True ~ (root :|| (One :<<= size))

type InternalInv root order size = True ~ ((root :&& (Two :<<= size)) :|| (MaxSize order :<<= (Two :* size)))

class Ord k => Keyed k a where
  toKey :: a -> k

data BNode :: Bool -> Nat -> Nat -> Nat -> * -> * -> * where
  Leaf :: (Keyed k a, NodeInv o n, LeafInv r n) => 
    Vector (k,a) n -> 
    BNode r Zero o n k a
  Internal :: (Keyed k a, NodeInv o (S n), InternalInv r o (S n)) =>
    (Vector (forall n'. BNode False h o n' k a) (S n), Vector k n) ->
    BNode r (S h) o (S n) k a

data BTree order key a = forall h n. BRoot (BNode True h order n key a)

empty :: (Keyed k a) => BNode True Zero o Z k a
empty = Leaf Nil

singleton :: (Keyed k a) => a -> BNode True Zero o (S Z) k a
singleton x = Leaf $ V.singleton (toKey x, x)

choosePointer :: (Keyed k a) => k ->
  Vector (forall n. BNode False h o n k a) (S n1) -> 
  Vector k n1 -> 
  BNode False h o n2 k a
choosePointer _ (a :- _) Nil = a
choosePointer key (a :- as) (b :- bs) = if key < b then a else choosePointer key as bs

search' :: (Keyed k a) => k -> BNode r h o n k a -> [(k,a)]
search' key (Leaf xs) = filter (\pair -> key == fst pair) . V.toList $ xs
search' key (Internal (cpts,keys)) = search' key $ choosePointer key cpts keys

search :: (Keyed k a) => k -> BTree m k a -> [a]
search key (BRoot node) = fmap snd $ search' key node

data InsertResult root height order n k a
  = Here (BNode root height order (S n) k a)
  | Below (BNode root height order n k a)
  | forall n1 n2. ((S n) ~ (n1 :+ n2)) => Split (BNode False height order n1 k a, BNode False height order n2 k a)

insertLeaf :: (Keyed k a) => (k,a) -> Vector (k,a) n -> Vector (k,a) (S n)
insertLeaf x Nil = x :- Nil
insertLeaf (key,x) (y :- ys) = if key < fst y then (key,x) :- y :- ys else y :- (insertLeaf (key,x) ys)

insert' :: (SingI o, Keyed k a) => a -> BNode r h o n k a -> InsertResult r h o n k a
insert' x (Leaf xs :: BNode r h o n k a) = 
  let maxSize = (sing :: SNat (MaxSize o))
      xxs :: Vector (k,a) (S n)
      xxs = insertLeaf (toKey x, x) xs
  in
    if sNatToInt (V.sLength xs) < sNatToInt maxSize 
    then Here $ Leaf xxs
    else undefined x
insert' x (Internal (cpts,keys)) = undefined x cpts keys

insert :: (SingI o, Keyed k a) => a -> BTree o k a -> BTree o k a
insert x (BRoot node) = 
  case insert' x node of
    Here node' -> BRoot node'
    Below node' -> BRoot node'
    Split (node1, node2) -> undefined node1 node2
