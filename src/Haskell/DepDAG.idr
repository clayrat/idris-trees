module Haskell.DepDAG

import Functor 

import Data.Fin
import Data.Vect

%default total

-- https://www.twanvl.nl/blog/haskell/dependently-typed-dags

-- Lifted 

interface Eq1 (f : t -> Type) where
  eq1 : f n -> f n -> Bool

interface Pred1 (f : Nat -> Type) where
  pred1 : f (S n) -> Maybe (f n)

Pred1 Fin where
  pred1 FZ = Nothing
  pred1 (FS i) = Just i

interface Succ1 (f : Nat -> Type) where
  succ1 : f n -> f (S n)

Succ1 Fin where
  succ1 = FS

(Functor f, Succ1 g) => Succ1 (CompF f g) where
  succ1 (MkCompF x) = MkCompF (map succ1 x)

-- Monad1  

infixr 3 >>>=

interface Monad1 (m : (t -> Type) -> t -> Type) where
  pure1 : f a -> m f a
  (>>>=) : m f a -> ({b : t} -> f b -> m g b) -> m g a  


-- Box

data Box : (f : Nat -> Type) -> (n : Nat) -> Type where
  BoxZ : f n -> Box f n
  BoxS : Box f (S n) -> Box f n

Monad1 Box where
    pure1 = BoxZ
    (>>>=) {a} (BoxZ x) y = y {b=a} x 
    (>>>=) (BoxS x) y = BoxS (x >>>= y)

boxLift : Succ1 g => Box f n -> g n -> Box (ProdF f g) n
boxLift (BoxZ x) y = BoxZ (MkProdF x y)
boxLift (BoxS x) y = BoxS (boxLift x (succ1 y))

unprod : Box (ProdF x y) n -> Box y n
unprod (BoxZ (MkProdF _ y)) = BoxZ y
unprod (BoxS b) = BoxS $ unprod b

-- VectF

data VectF : (f : Nat -> Type) -> Nat -> Type where
  Nil  : VectF f Z
  (::) : f n -> VectF f n -> VectF f (S n) 

Eq1 f => Eq (VectF f n) where
  [] == [] = True
  (x :: xs) == (y :: ys) = eq1 x y && xs == ys

Eq1 f => Eq1 (VectF f) where
  eq1 = (==)  

findVec : (Eq1 f, Pred1 f) => f n -> VectF f n -> Maybe (Fin n)  
findVec x (y :: ys) = case pred1 x of
    Just x' => if eq1 x' y then Just FZ else map FS (findVec x' ys)
    Nothing => Nothing
findVec _ _ = Nothing

-- DAG Node

data Node : Type -> Nat -> Type where
  MkNode : a -> List (Fin n) -> Node a n

Eq a => Eq (Node a n) where
  (MkNode x xs) == (MkNode y ys) = x == y && xs == ys
  
Eq a => Eq1 (Node a) where
  eq1 = (==)  
  
Pred1 (Node a) where
  pred1 (MkNode x is) = map (MkNode x) (traverse pred1 is)
  
Succ1 (Node a) where
  succ1 (MkNode x cs) = MkNode x (map FS cs)

-- DAG

DAG : Type -> Nat -> Type 
DAG a = VectF (Node a) 

consNode : Eq a => Node a n -> DAG a n -> Box (ProdF Fin (DAG a)) n
consNode n dag = case findVec n dag of
  Just i  => BoxZ (MkProdF i dag)
  Nothing => BoxS $ BoxZ (MkProdF FZ (n :: dag))

-- Tree

data Tree a = TNode a (List (Tree a))

-- Convert a DAG to a tree, using the given node index as root
toTree : Fin n -> DAG a n -> Tree a
toTree  FZ    (MkNode x is :: t) = TNode x (map (\z => toTree z t) is)
toTree (FS i) (_           :: t) = toTree i t

toTree0 : DAG a (S n) -> Tree a
toTree0 = toTree FZ

mutual   
  fromTree : Eq a => Tree a -> DAG a n -> Box (ProdF Fin (DAG a)) n
  fromTree (TNode x cs) dag0 = 
    fromForest cs dag0
      >>>= \(MkProdF (MkCompF cs1) dag1) =>
            consNode (MkNode x cs1) dag1
  
  fromForest : Eq a => List (Tree a) -> DAG a n -> Box (ProdF (CompF List Fin) (DAG a)) n
  fromForest [] dag = pure1 $ MkProdF (MkCompF []) dag
  fromForest (x :: xs) dag0 =
    fromForest xs dag0
      >>>= \(MkProdF xs1 dag1) =>
             boxLift (fromTree x dag1) xs1
      >>>= \(MkProdF (MkProdF x2 dag2) (MkCompF xs2)) =>
             pure1 $ MkProdF (MkCompF (x2 :: xs2)) dag2

fromTree0 : Eq a => Tree a -> Box (DAG a) Z
fromTree0 x = unprod (fromTree x [])

-- test

Example : DAG String 5
Example = [MkNode "a" [0,1,1,3], MkNode "b" [1,1], MkNode "c" [0,1], MkNode "d" [], MkNode "e" []]  

test : fromTree0 $ toTree0 Example = BoxS $ BoxS $ BoxS $ BoxS $ BoxS $ BoxZ Example
test = Refl
