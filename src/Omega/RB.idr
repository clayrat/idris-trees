module Omega.RB

%default total

data Color = Red | Black

data SubTree : Color -> Nat -> Type where
  Leaf : SubTree Black Z
  RNode : SubTree Black n -> Int -> SubTree Black n -> SubTree Red n
  BNode : SubTree cL n -> Int -> SubTree cR n -> SubTree Black (S n)

data RBTree = MkRBTree (SubTree Black n)  

-- a Ctxt records where we've venn as we descend down into a tree as we search
-- for a value

data Dir = LeftD | RightD

data Ctxt : Color -> Nat -> Type where
  Nil : Ctxt Black n    
  RCons : Int -> Dir -> SubTree Black n -> Ctxt Red n -> Ctxt Black n 
  BCons : Int -> Dir -> SubTree c1 n -> Ctxt Black (S n) -> Ctxt c n 

-- Turn a Red tree into a Black tree. Always possible, since Black nodes don't
-- restrict the color of their subtrees  

blacken : SubTree Red n -> SubTree Black (S n)
blacken (RNode l e r) = (BNode l e r)

-- fill a context with a subtree to regain the original RBTree, works if the
-- colors and black depth match up 

fill : Ctxt c n -> SubTree c n -> RBTree 
fill Nil t = MkRBTree t 
fill (RCons e LeftD  uncle c) tree = fill c (RNode uncle e tree) 
fill (RCons e RightD uncle c) tree = fill c (RNode tree  e uncle) 
fill (BCons e LeftD  uncle c) tree = fill c (BNode uncle e tree) 
fill (BCons e RightD uncle c) tree = fill c (BNode tree  e uncle) 

recolor : Dir -> Int -> SubTree Black n -> Dir -> Int -> SubTree Black (S n) -> SubTree Red n -> SubTree Red (S n) 
recolor LeftD  pE sib RightD gE uncle t = RNode (BNode sib pE t) gE  uncle 
recolor RightD pE sib RightD gE uncle t = RNode (BNode t pE sib) gE  uncle 
recolor LeftD  pE sib LeftD  gE uncle t = RNode  uncle           gE (BNode sib pE t) 
recolor RightD pE sib LeftD  gE uncle t = RNode  uncle           gE (BNode t pE sib) 

rotate : Dir -> Int -> SubTree Black n -> Dir -> Int -> SubTree Black n -> SubTree Red n -> SubTree Black (S n) 
rotate RightD pE sib RightD gE uncle (RNode x e y) = BNode (RNode x e y)        pE (RNode sib gE uncle) 
rotate LeftD  pE sib RightD gE uncle (RNode x e y) = BNode (RNode sib pE x)     e  (RNode y gE uncle) 
rotate LeftD  pE sib LeftD  gE uncle (RNode x e y) = BNode (RNode uncle gE sib) pE (RNode x e y) 
rotate RightD pE sib LeftD  gE uncle (RNode x e y) = BNode (RNode uncle gE x)   e  (RNode y pE sib) 

-- Repair a tree if its out of balance. The Ctxt holds crucial information about
-- colors of parent and grand­parent nodes. 
repair : SubTree Red n -> Ctxt c n -> RBTree 
repair t Nil = MkRBTree (blacken t) 
repair t (BCons e LeftD sib c) = fill c (BNode sib e t) 
repair t (BCons e RightD sib c) = fill c (BNode t e sib) 
-- these are the tricky cases 
repair t (RCons e dir sib (BCons {c1=Red} e' dir' uncle ctxt)) = 
  repair (recolor dir e sib dir' e' (blacken uncle) t) ctxt 
repair t (RCons e dir sib (BCons {c1=Black} e' dir' uncle ctxt)) = 
  fill ctxt (rotate dir e sib dir' e' uncle t)
repair _ (RCons _ _ _ (RCons _ _ _ _)) impossible
  
insert : Int -> RBTree -> RBTree 
insert e (MkRBTree t) = go t Nil
  where
  -- as we walk down the tree, keep track of everywhere we've been in the Ctxt
  -- input
  go : SubTree c n -> Ctxt c n -> RBTree 
  go (RNode l e' r) ctxt = 
    if e < e' 
      then go l (RCons e' RightD r ctxt) 
      else go r (RCons e' LeftD l ctxt) 
  go (BNode l e' r) ctxt =
    if e < e'
      then go l (BCons e' RightD r ctxt) 
      else go r (BCons e' LeftD l ctxt) 
  -- once we get to the bottom we "insert" the node as a Red node. since this
  -- may break invariant, we may need do some patch work 
  go Leaf ctxt = repair (RNode Leaf e Leaf) ctxt 
    
