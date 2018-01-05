module Haskell.NumVecTree

import Functor
import Data.Fin
import Data.Vect

%default total

-- after https://github.com/conal/numbers-vectors-trees

Digits : Nat -> Nat -> Type
Digits n b = Vect n (Fin b)

--Digits' : Nat -> Nat -> Type
--Digits' n b = Trie (Fin b)

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
  E : TrieU a -> TrieU b -> TrieU (Either a b)
  P : TrieU a -> TrieU b -> TrieU (a, b)
  V : TrieU a -> (n : Nat) -> TrieU (Vect n a)

Trie : TrieU _ -> Type -> Type
Trie  U      = Id
Trie (E a b) = ProdF (Trie a) (Trie b)
Trie (P a b) = CompF (Trie a) (Trie b)
Trie (V a n) = CompRF (Trie a) n

trie : (u : TrieU x) -> (x -> y) -> Trie u y
trie  U          f = MkId (f ())
trie (E n m)     f = MkProdF (trie n (f . Left)) (trie m (f . Right))
trie (P n m)     f = MkCompF (trie n (trie m . curry f))
trie (V n m)     f with (sizeAccessible m)
 trie (V n Z)     f | acc = CRFZ (f [])
 trie (V n (S k)) f | Access acc = CRFS (MkCompF $ trie n (\a => trie (V n k) (f . (a ::)) | acc k lteRefl)) 

untrie : (u : TrieU x) -> Trie u y -> (x -> y)
untrie  U      (MkId a)      ()        = a
untrie (E n m) (MkProdF a b) (Left x)  = untrie n a x 
untrie (E n m) (MkProdF a b) (Right y) = untrie m b y
untrie (P n m) (MkCompF c)   (x, y)    = untrie m (untrie n c x) y
untrie (V n m) c x with (sizeAccessible m)
  untrie (V n Z) (CRFZ a) x | acc = a
  untrie (V n (S k)) (CRFS (MkCompF b)) (x::xs) | Access acc = untrie (V n k) (untrie n b x) xs | acc k lteRefl

memo : .{u : TrieU a} -> (a -> b) -> (a -> b)
memo {u} = untrie u . trie u

--interface HasTrie (a : Type) where
--  u : TrieU
--  trie : (a -> b) -> Trie u b
--  untrie : Trie u b -> (a -> b)
  
-- trie . untrie = id
-- untrie . trie = id



{-
HasTrie () where
  u = U
  trie f = MkId (f ())
  untrie (MkId a) = \() => a

(HasTrie a, HasTrie b) => HasTrie (a,b) where
  u @{ta} @{tb} = P (u @{ta}) (u @{tb})
  trie f = MkCompF (trie (trie . curry f))
  untrie (MkCompF t) = uncurry (untrie . untrie t)

(HasTrie a, HasTrie b) => HasTrie (Either a b) where
  u @{ta} @{tb} = E (u @{ta}) (u @{tb})
  trie f = MkProdF (trie (f . Left)) (trie (f . Right))
  untrie (MkProdF s t) = either (untrie s) (untrie t)  

HasTrie a => HasTrie (Vect n a) where
  u {n} @{at} = V (u @{at}) n
  trie {n=Z} f = CRFZ (f [])
  trie {n=S k} f = ?wat --CRFS (trie $ \a => trie (f . (Vect.(::) a)))
  untrie = ?wat2
  
    ZeroC v `untrie` ZVec      = v
    SuccC t `untrie` (a :< as) = (t `untrie` a) `untrie` as
  

  
  trieN ∷ HasTrie a ⇒ Nat n → (Vec n a → b) → (Trie a :^ n) b
  trieN Zero     f = ZeroC (f ZVec)
  trieN (Succ _) f = SuccC (trie (λ a → trie (f ∘ (a :<))))
  -}