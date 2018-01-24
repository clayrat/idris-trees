module Agda.Pivotal.Slime

import Data.So

%default total

data Tree : Type -> Type where
  Leaf : Tree a
  Node : Tree a -> a -> Tree a -> Tree a

data STRange : Type -> Type where
  Empty : STRange a
  Intrv : a -> a -> STRange a

m : Bool -> Maybe a -> Maybe a
m b mx = if b then mx else Nothing

valid : Ord x => Tree x -> Maybe $ STRange x
valid Leaf = Just Empty
valid (Node l p r) with (valid l) 
  valid (Node l p r) | vl with (valid l) 
    valid (Node l p r) | Just  Empty      | Just  Empty      = Just $ Intrv p p
    valid (Node l p r) | Just  Empty      | Just (Intrv c d) = m (p <= c) (Just $ Intrv p d) 
    valid (Node l p r) | Just (Intrv a b) | Just  Empty      = m (b <= p) (Just $ Intrv a p) 
    valid (Node l p r) | Just (Intrv a b) | Just (Intrv c d) = m (b <= p) $ m (p <= c) (Just $ Intrv a d) 
    valid (Node l p r) | _                | _                = Nothing

lOK : Ord a => STRange a -> a -> Bool
lOK  Empty      _ = True
lOK (Intrv _ u) p = u<=p

rOK : Ord a => a -> STRange a -> Bool
rOK _  Empty      = True
rOK p (Intrv l _) = p <= l

rOut : STRange a -> a -> STRange a -> STRange a
rOut  Empty      p  Empty      = Intrv p p
rOut  Empty      p (Intrv _ u) = Intrv p u
rOut (Intrv l _) p  Empty      = Intrv l p
rOut (Intrv l _) _ (Intrv _ u) = Intrv l u

data BST : (t : Type) -> STRange t -> Type where
  BLeaf : BST t Empty
  BNode : Ord t => BST t l -> (x : t) -> BST t r -> So (lOK l p) -> So (rOK p r) -> BST t (rOut l p r)   -- green slime!

oRange : Ord a => STRange a -> a -> STRange a
oRange Empty y = Intrv y y
oRange (Intrv l u) y = if y<=l then Intrv y u else if u<=y then Intrv l y else Intrv l u

insert : Ord t => (y : t) -> BST t r -> BST t (oRange r y)
insert y BLeaf = BNode BLeaf y BLeaf Oh Oh
insert y (BNode lt p rt s1 s2) = if y <= p then ?wat else ?wat2   -- rOut ~ oRange ?