module Coq.BipTrie

import Data.Bip

%default total

-- after https://softwarefoundations.cis.upenn.edu/current/vfa-current/Trie.html

-- TODO port stdlib PositiveMap / FMaps

data Trie : Type -> Type where
  Leaf : Trie a
  Node : Trie a -> a -> Trie a -> Trie a

TrieTable : Type -> Type
TrieTable a = (a, Trie a)

empty : (default : a) -> TrieTable a
empty default = (default, Leaf)

look : (default : a) -> (i : Bip) -> (m : Trie a) -> a
look default  _     Leaf        = default
look _        U    (Node _ x _) = x
look default (O i) (Node l _ _) = look default i l
look default (I i) (Node _ _ r) = look default i r

lookup : (i : Bip) -> (t : TrieTable a) -> a
lookup i t = look (fst t) i (snd t)

ins : (default : a) -> (i : Bip) -> (x : a) -> (m : Trie a) -> Trie a
ins _        U    x  Leaf        = Node Leaf x Leaf
ins default (O i) x  Leaf        = Node (ins default i x Leaf) default Leaf
ins default (I i) x  Leaf        = Node Leaf default (ins default i x Leaf)
ins _        U    x (Node l _ r) = Node l x r
ins default (O i) x (Node l y r) = Node (ins default i x l) y r
ins default (I i) x (Node l y r) = Node l y (ins default i x r)

insert : (i : Bip) -> (x : a) -> (t : TrieTable a) -> TrieTable a
insert i x t = (fst t, ins (fst t) i x (snd t))

-- PROOFS

-- lookLeaf is Refl

lookInsSame : (x : a) -> (k : Bip) -> (v : a) -> (t : Trie a) -> look x k (ins x k v t) = v
lookInsSame _  U    _  Leaf        = Refl
lookInsSame _  U    _ (Node _ _ _) = Refl
lookInsSame x (O k) v  Leaf        = lookInsSame x k v Leaf
lookInsSame x (O k) v (Node l _ _) = lookInsSame x k v l
lookInsSame x (I k) v  Leaf        = lookInsSame x k v Leaf
lookInsSame x (I k) v (Node _ _ r) = lookInsSame x k v r

lookInsOther : (x : a) -> (j, k : Bip) -> (v : a) -> (t : Trie a) -> Not (j = k) -> look x j (ins x k v t) = look x j t
lookInsOther _  U     U    _  _           njk = absurd $ njk Refl
lookInsOther _  U    (O _) _  Leaf        _   = Refl
lookInsOther _  U    (O _) _ (Node _ _ _) _   = Refl
lookInsOther _  U    (I _) _  Leaf        _   = Refl
lookInsOther _  U    (I _) _ (Node _ _ _) _   = Refl
lookInsOther _ (O _)  U    _  Leaf        _   = Refl
lookInsOther _ (O _)  U    _ (Node _ _ _) _   = Refl
lookInsOther x (O a) (O b) v  Leaf        njk = lookInsOther x a b v Leaf (njk  . cong)
lookInsOther x (O a) (O b) v (Node l _ _) njk = lookInsOther x a b v l (njk  . cong)
lookInsOther _ (O _) (I _) _  Leaf        _   = Refl
lookInsOther _ (O _) (I _) _ (Node _ _ _) _   = Refl
lookInsOther _ (I _)  U    _  Leaf        _   = Refl
lookInsOther _ (I _)  U    _ (Node _ _ _) _   = Refl
lookInsOther _ (I _) (O _) _  Leaf        _   = Refl
lookInsOther _ (I _) (O _) _ (Node _ _ _) _   = Refl
lookInsOther x (I a) (I b) v  Leaf        njk = lookInsOther x a b v Leaf (njk  . cong)
lookInsOther x (I a) (I b) v (Node _ _ r) njk = lookInsOther x a b v r (njk  . cong)

-- TODO relation with TotalMap

-- TESTS

threeTen : TrieTable Bool 
threeTen = insert 3 True $ insert 10 True $ empty False

test310 : map (\i => lookup i BipTrie.threeTen) [3,1,4,1,5] = [True,False,False,False,False]
test310 = Refl

collisions : List Bip -> Nat
collisions input = loop input 0 (empty False)
  where
  loop : List Bip -> Nat -> TrieTable Bool -> Nat
  loop []        c _     = c
  loop (x :: xs) c table = if lookup x table 
                             then loop xs (S c) table
                             else loop xs c (insert x True table)

collisionsPi : collisions [3,1,4,1,5,9,2,6] = 1
collisionsPi = Refl