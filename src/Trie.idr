module Trie

import Data.SortedMap

%access public export

record Trie a where
  constructor MkTrie
  endHere : Bool
  getTrie : SortedMap a (Trie a)

empty : Ord a => Trie a
empty = MkTrie False empty

follow : Ord a => c -> (Trie a -> c) -> List a -> Trie a -> c
follow ifMiss onEnd = foldr f onEnd 
  where
  f : a -> (Trie a -> c) -> Trie a -> c
  f x g = fromMaybe ifMiss . map g . lookup x . getTrie 
   
member : Ord a => List a -> Trie a -> Bool
member = follow False endHere
 
complete : Ord a => List a -> Trie a -> Trie a
complete = follow empty id

overMap : Ord b => (SortedMap a (Trie a) -> SortedMap b (Trie b)) -> Trie a -> Trie b
overMap f (MkTrie e m) = MkTrie e (f m)

insert : Ord a => List a -> Trie a -> Trie a
insert = foldr f (\(MkTrie _ m) => MkTrie True m)
  where
  f : a -> (Trie a -> Trie a) -> Trie a -> Trie a
  f x g = overMap (\sm => insert x (g $ fromMaybe (MkTrie False empty) $ lookup x sm) sm)
