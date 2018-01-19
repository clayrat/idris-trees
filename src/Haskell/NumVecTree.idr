module Haskell.NumVecTree

import Functor
import Data.Fin
import Data.Vect

%default total

-- after https://github.com/conal/numbers-vectors-trees

Digits : Nat -> Nat -> Type
Digits n b = Vect n (Fin b)

littleEndianToZ : Digits n b -> Integer
littleEndianToZ {b} = foldr (\x, s => finToInteger x + ib * s) 0
  where 
  ib = toIntegerNat b

bigEndianToZ : Digits n b -> Integer
bigEndianToZ {b} = foldl (\s, x => finToInteger x + ib * s) 0
  where 
  ib = toIntegerNat b

data TrieU : Type -> Type where
  U : TrieU ()
  F : (n : Nat) -> TrieU (Fin n)
  E : TrieU a -> TrieU b -> TrieU (Either a b)
  P : TrieU a -> TrieU b -> TrieU (a, b)
  V : TrieU a -> (n : Nat) -> TrieU (Vect n a)

Trie : TrieU _ -> Type -> Type
Trie  U      = Id
Trie (F n)   = Vect n
Trie (E a b) = ProdF (Trie a) (Trie b)
Trie (P a b) = CompF (Trie a) (Trie b)
Trie (V a n) = CompRF (Trie a) n

trie : (u : TrieU x) -> (x -> y) -> Trie u y
trie  U          f = MkId (f ())
trie (F m)       f with (sizeAccessible m)
  trie (F Z)     f | _ = []
  trie (F (S k)) f | Access acc = f FZ :: trie (F k) (f . FS) | acc k lteRefl
trie (E n m)     f = MkProdF (trie n (f . Left)) (trie m (f . Right))
trie (P n m)     f = MkCompF (trie n (trie m . curry f))
trie (V n m)     f with (sizeAccessible m)
 trie (V n Z)     f | _ = CRFZ (f [])
 trie (V n (S k)) f | Access acc = CRFS (MkCompF $ trie n (\a => trie (V n k) (f . (a ::)) | acc k lteRefl)) 

untrie : (u : TrieU x) -> Trie u y -> (x -> y)
untrie  U        (MkId a)       ()       = a
untrie (F (S _)) (x :: _)       FZ       = x
untrie (F (S k)) (_ :: xs)     (FS s)    = untrie (F k) xs s
untrie (E n m)   (MkProdF a b) (Left x)  = untrie n a x 
untrie (E n m)   (MkProdF a b) (Right y) = untrie m b y
untrie (P n m)   (MkCompF c)   (x, y)    = untrie m (untrie n c x) y
untrie (V n m)   c x with (sizeAccessible m)
  untrie (V n Z) (CRFZ a) x | _ = a
  untrie (V n (S k)) (CRFS (MkCompF b)) (x::xs) | Access acc = untrie (V n k) (untrie n b x) xs | acc k lteRefl

-- TODO actually memoize  
memo : .{u : TrieU a} -> (a -> b) -> (a -> b)
memo {u} = untrie u . trie u

-- examples

Digits' : Nat -> Nat -> Type
Digits' n b = Trie (F n) (Fin b)

TrieTree : TrieU a -> Nat -> Type -> Type 
TrieTree t = CompRF (Trie t)

VecTree : Nat -> Nat -> Type -> Type 
VecTree b = TrieTree (F b)

test : VecTree 2 3 Int
test = CRFS $ MkCompF [ CRFS $ MkCompF [ CRFS $ MkCompF [ CRFZ 1
                                                        , CRFZ 2
                                                        ]
                                       , CRFS $ MkCompF [ CRFZ 3
                                                        , CRFZ 4
                                                        ]
                                       ]
                      , CRFS $ MkCompF [ CRFS $ MkCompF [ CRFZ 5
                                                        , CRFZ 6
                                                        ]
                                       , CRFS $ MkCompF [ CRFZ 7
                                                        , CRFZ 8
                                                        ]
                                       ]
                      ]