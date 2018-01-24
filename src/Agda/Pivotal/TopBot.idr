module Agda.Pivotal.TopBot

import Data.So

%default total

data TopBot : Type -> Type where
  Top : TopBot t
  Bot : TopBot t
  Box : (x : t) -> TopBot t

le : Ord t => TopBot t -> TopBot t -> Bool
le _ Top = True
le (Box x) (Box y) = x <= y
le Bot _ = True
le _ _ = False

data BST : (o : Ord t) -> (l, u : TopBot t) -> Type where
  BLeaf : BST o l u
  BNode : (x : t) -> BST o l (Box x) -> BST o (Box x) u -> So (le l (Box x)) -> So (le (Box x) u) -> BST o l u

insert : (o : Ord t) => (y : t) -> BST o l u -> So (le l (Box y)) -> So (le (Box y) u) -> BST o l u
insert @{o} y BLeaf s1 s2 = BNode y BLeaf BLeaf s1 s2
insert @{o} y (BNode p lt rt s1 s2) s11 s22 with ((<=) @{o} y p) proof yp
  | True = BNode p (insert @{o} y lt s11 (rewrite sym yp in Oh)) rt s1 s2
  | False = BNode p lt (insert @{o} y rt ?wat s22) s1 s2    -- Conor can't be bothered to prove `y <= p = False -> So (p <= y)`