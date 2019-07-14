module TrieMap

import These
import Data.SortedMap

%access public export
%default total

record TrieMap a b where
  constructor MkTrieMap
  node : These b (SortedMap a (TrieMap a b))
  
Functor (TrieMap a) where 
  map f (MkTrieMap node) = MkTrieMap $ assert_total $ bimap f (map (map f)) node

--

mapSingleton : Ord a => a -> b -> SortedMap a b
mapSingleton a b = insert a b empty

--

empty : Ord a => TrieMap a b 
empty = MkTrieMap $ That empty

singleton : Ord a => List a -> b -> TrieMap a b
singleton []      v = MkTrieMap $ This v
singleton (k::ks) v = MkTrieMap $ That $ mapSingleton k (singleton ks v)

insertWith : Ord a => List a -> (Maybe b -> b) -> TrieMap a b -> TrieMap a b
insertWith []      f (MkTrieMap nd) = 
  MkTrieMap $ these (This . f . Just) (Both (f Nothing)) (Both . f . Just) nd
insertWith (k::ks) f (MkTrieMap nd) = 
  MkTrieMap $ these (\x => Both x (mapSingleton k end)) (That . rec) (\x => Both x . rec) nd
  where
  end : TrieMap a b
  end = singleton ks (f Nothing)
  rec : SortedMap a (TrieMap a b) -> SortedMap a (TrieMap a b)
  rec sm = maybe (insert k end sm) (\tm => insert k (insertWith ks f tm) sm) (lookup k sm) 

insert : Ord a => List a -> b -> TrieMap a b -> TrieMap a b
insert ks v = insertWith ks (const v)

foldWithKeysM : (Ord a, Monad m, Monoid c) => (List a -> m c) -> (List a -> b -> m c) -> TrieMap a b -> m c
foldWithKeysM {a} {m} {c} fk fv = go [] 
  where 
  go : List a -> TrieMap a b -> m c
  go as (MkTrieMap nd) = 
    bifold <$> bitraverse 
                (fv as) 
                (\sm => foldlM 
                          (\x, (k, vs) => do let as' = as ++ [k]
                                             y <- assert_total $ go as' vs
                                             z <- fk as'
                                             pure $ x <+> y <+> z)
                          neutral 
                          (toList sm)) 
                nd 
