module Coq.Binom

import Ord

import Data.List.Quantifiers

%default total

-- after https://softwarefoundations.cis.upenn.edu/current/vfa-current/Binom.html

data Tree : Type where
  Leaf : Tree
  Node : Nat -> Tree -> Tree -> Tree

PriQueue : Type
PriQueue = List Tree

empty : PriQueue
empty = []

smash : (t, u : Tree) -> Tree
smash (Node x t1 Leaf) (Node y u1 Leaf) = 
  if x > y 
    then Node x (Node y u1 t1) Leaf 
    else Node y (Node x t1 u1) Leaf
smash  _                _               = Leaf  -- arbitrary bogus tree

carry : (q : PriQueue) -> (t : Tree) -> PriQueue
carry q              Leaf        = q
carry []          t@(Node _ _ _) = [t]
carry (Leaf :: q) t@(Node _ _ _) = t :: q
carry (u    :: q) t@(Node _ _ _) = Leaf :: carry q (smash t u)

insert : (x : Nat) -> (q : PriQueue) -> PriQueue
insert x q = carry q (Node x Leaf Leaf)

--testQ : foldl (\x,q => insert q x) Binom.empty (the (List Nat) [3,1,4,1,5,9,2,3,5])
--      = [ Node 5 Leaf Leaf
--        , Leaf
--        , Leaf
--        , Node 9 (Node 4 (Node 3 (Node 1 Leaf Leaf) (Node 1 Leaf Leaf)) (Node 3 (Node 2 Leaf Leaf) (Node 5 Leaf Leaf))) Leaf
--        ]
--testQ = Refl

join : (p, q : PriQueue) -> (c : Tree) -> PriQueue
join []          q           c              = carry q c
join p            []         c              = carry p c
join (Leaf :: p) (Leaf :: q) c              = c    :: join p q Leaf
join (Leaf :: p) (q1   :: q)    Leaf        = q1   :: join p q Leaf
join (Leaf :: p) (q1   :: q) c@(Node _ _ _) = Leaf :: join p q (smash c q1)
join (p1   :: p) (Leaf :: q)    Leaf        = p1   :: join p q Leaf
join (p1   :: p) (Leaf :: q) c@(Node _ _ _) = Leaf :: join p q (smash c p1)
join (p1   :: p) (q1   :: q) c              = c    :: join p q (smash p1 q1)

merge : (p, q : PriQueue) -> PriQueue
merge p q = join p q Leaf

unzip : (t : Tree) -> (cont : PriQueue -> PriQueue) -> PriQueue 
unzip  Leaf          cont = cont []
unzip (Node x t1 t2) cont = unzip t2 (\q => Node x t1 Leaf :: cont q)

findMax1 : (current : Nat) -> (q : PriQueue) -> Nat
findMax1 current []                = current
findMax1 current (Leaf       :: q) = findMax1 current q
findMax1 current (Node x _ _ :: q) = findMax1 (if x > current then x else current) q

findMax : (q: PriQueue) -> Maybe Nat
findMax []                = Nothing
findMax (Leaf       :: q) = findMax q
findMax (Node x _ _ :: q) = Just (findMax1 x q)

heapDeleteMax : (t : Tree) -> PriQueue
heapDeleteMax (Node x t1 Leaf) = unzip t1 id
heapDeleteMax  _               = [] -- bogus value for ill-formed or empty trees

deleteMaxAux : (m : Nat) -> (p : PriQueue) -> (PriQueue, PriQueue)
deleteMaxAux m (Leaf           :: p) = 
  let (j, k) = deleteMaxAux m p in 
  (Leaf :: j, k)
deleteMaxAux m (Node x t1 Leaf :: p) =
  if m > x
    then 
      let (j,k) = deleteMaxAux m p in 
      (Node x t1 Leaf :: j, k)
    else (Leaf :: p, heapDeleteMax (Node x t1 Leaf))
deleteMaxAux _  _                    = ([], []) -- Bogus value

deleteMax : (q : PriQueue) -> Maybe (Nat, PriQueue)
deleteMax q = 
  case findMax q of
    Nothing => Nothing
    Just m => let (p1, q1) = deleteMaxAux m q in 
              Just (m, merge p1 q1)

-- predicates

-- t is a complete binary tree of depth n, with every key <= m
pow2heap1 : (n : Nat) -> (m : Nat) -> (t : Tree) -> Type
pow2heap1 Z     _  Leaf        = ()
pow2heap1 Z     _ (Node _ _ _) = Void
pow2heap1 (S _) _  Leaf        = Void
pow2heap1 (S n) m (Node k l r) = (LTE k m, pow2heap1 n k l, pow2heap1 n m r)

-- t is a power-of-2 heap of depth n 
pow2heap : (n : Nat) -> (t : Tree) -> Type
pow2heap n (Node m t1 Leaf) = pow2heap1 n m t1
pow2heap _  _               = Void

-- l is the ith tail of a binomial heap
priq1 : (i : Nat) -> (l : PriQueue) -> Type
priq1 i (t :: l) = (Either (t = Leaf) (pow2heap i t), priq1 (S i) l)
priq1 _ []       = ()

-- q is a binomial heap
priq : (q : PriQueue) -> Type
priq q = priq1 Z q

-- correctness

emptyPriq : priq Binom.empty
emptyPriq = ()

smashValid : (n : Nat) -> (t, u : Tree) -> pow2heap n t -> pow2heap n u -> pow2heap (S n) (smash t u)
smashValid  Z    (Node _ _ (Node _ _ _))  _                      prft _    = absurd prft
smashValid  Z     _                      (Node _ _ (Node _ _ _)) _    prfu = absurd prfu
smashValid  Z    (Node x Leaf Leaf)      (Node y Leaf Leaf)      ()   () with (compare x y) proof xy
  smashValid Z (Node x Leaf Leaf) (Node y Leaf Leaf) () () | LT = 
    (lteSuccLeft $ cmpLt x y (sym xy), (), ())
  smashValid Z (Node x Leaf Leaf) (Node y Leaf Leaf) () () | EQ = 
    (rewrite cmpEq x y (sym xy) in lteRefl, (), ())
  smashValid Z (Node x Leaf Leaf) (Node y Leaf Leaf) () () | GT = 
    (lteSuccLeft $ cmpLt y x (rewrite cmpOp y x in rewrite sym xy in Refl), (), ())
smashValid (S _) (Node _ Leaf Leaf)       _                      prft _    = absurd prft
smashValid (S _)  _                      (Node _ Leaf Leaf)      _    prfu = absurd prfu
smashValid (S _) (Node x (Node _ _ _) Leaf) (Node y (Node _ _ _) Leaf) prft prfu with (compare x y) proof xy
  smashValid (S _) (Node x (Node _ _ _) Leaf) (Node y (Node _ _ _) Leaf) prft prfu | LT = 
    (lteSuccLeft $ cmpLt x y (sym xy), prft, prfu)
  smashValid (S _) (Node x (Node _ _ _) Leaf) (Node y (Node _ _ _) Leaf) prft prfu | EQ = 
    (rewrite cmpEq x y (sym xy) in lteRefl, prft, prfu)
  smashValid (S _) (Node x (Node _ _ _) Leaf) (Node y (Node _ _ _) Leaf) prft prfu | GT = 
    (lteSuccLeft $ cmpLt y x (rewrite cmpOp y x in rewrite sym xy in Refl), prfu, prft)
smashValid  _     Leaf                    _                      prft _    = absurd prft 
smashValid  _     _                       Leaf                   _    prfu = absurd prfu

carryValid : (n : Nat) -> (q : PriQueue) -> priq1 n q -> (t : Tree) -> Either (t=Leaf) (pow2heap n t) -> priq1 n (carry q t)
carryValid _ _                       pq1                 _           (Left  pt) = rewrite pt in pq1
carryValid _ _                       _                   Leaf        (Right pt) = absurd pt
carryValid _ []                      ()                 (Node _ _ _) (Right pt) = (Right pt, ())
carryValid _ (    _           ::  _) (Left  pht, pq1)   (Node _ _ _) (Right pt) = rewrite pht in (Right pt, pq1)
carryValid _ (    Leaf        ::  _) (Right pht,  _)    (Node _ _ _) (Right _ ) = absurd pht
carryValid n (ht@(Node _ _ _) :: tt) (Right pht, pq1) t@(Node _ _ _) (Right pt) = 
  (Left Refl, carryValid (S n) tt pq1 (smash t ht) (Right $ smashValid n t ht pt pht))

-- TODO

insertPriq : (x : Nat) -> (q : PriQueue) -> priq q -> priq (insert x q)

-- This proof is rather long, but each step is reasonably straightforward. There's just one induction to do, right at the beginning.

joinValid : (p, q : PriQueue) -> (c : Tree) -> (n : Nat) -> priq1 n p -> priq1 n q -> Either (c=Leaf) (pow2heap n c) -> priq1 n (join p q c)

deleteMaxJustPriq : (p, q : PriQueue) -> (k : Nat) -> priq p -> deleteMax p = Just (k, q) -> priq q

-- TODO move out?
data Permutation : List a -> List a -> Type where
  PermNil : Permutation [] []
  PermSkip : Permutation l l1 -> Permutation (x :: l) (x :: l1)
  PermSwap : (x, y : a) -> (l : List a) -> Permutation (y :: x :: l) (x :: y :: l)
  PermTrans : Permutation l l1 -> Permutation l1 l2 -> Permutation l l2

-- the keys in t are the same as the elements of l (with repetition)
data TreeElems : Tree -> List Nat -> Type where
  TreeElemsLeaf : TreeElems Leaf []
  TreeElemsNode : TreeElems tl bl -> TreeElems tr br -> Permutation b (v :: bl ++ br) -> TreeElems (Node v tl tr) b

data PriQueueElems : PriQueue -> List Nat -> Type where
  PriQueueElemsNil : PriQueueElems [] []
  -- TODO cons

-- extensionality theorem for the tree_elems relation
treeElemsExt : (t : Tree) -> (e1, e2 : List Nat) -> Permutation e1 e2 -> TreeElems t e1 -> TreeElems t e2

treePerm : (t : Tree) -> (e1, e2 : List Nat) -> TreeElems t e1 -> TreeElems t e2 -> Permutation e1 e2

-- To prove priqueue_elems_ext, you should almost be able to cut-and-paste the proof of tree_elems_ext, with just a few edits.
priqueueElemsExt : (q : PriQueue) -> (e1, e2 : List Nat) -> Permutation e1 e2 -> PriQueueElems q e1 -> PriQueueElems q e2

priqueuePerm : (q : PriQueue) -> (e1, e2 : List Nat) -> PriQueueElems q e1 -> PriQueueElems q e2 -> Permutation e1 e2

treeCanRelate : (t : Tree) -> (al : List Nat ** TreeElems t al)

canRelate : (q : PriQueue) -> (al : List Nat ** PriQueueElems q al)

emptyRelate : PriQueueElems Binom.empty []

-- Warning: This proof is rather long.
smashElems : (n : Nat) -> (t, u : Tree) -> (bt, bu : List Nat) -> pow2heap n t -> pow2heap n u -> TreeElems t bt -> TreeElems u bu -> TreeElems (smash t u) (bt ++ bu)

-- Some of these proofs are quite long, but they're not especially tricky. 

carryElems : (n : Nat) -> (q : PriQueue) -> priq1 n q -> (t : Tree) -> Either (t=Leaf) (pow2heap n t) -> (eq, et : List Nat) -> PriQueueElems q eq -> TreeElems t et ->  PriQueueElems (carry q t) (eq++et)

insertRelate : (p : PriQueue) -> (al : List Nat) -> (k : Nat) -> priq p -> PriQueueElems p al -> PriQueueElems (insert k p) (k::al)

joinElems : (p, q : PriQueue) -> (c : Tree) -> (n : Nat) -> priq1 n p -> priq1 n q -> Either (c=Leaf) (pow2heap n c) -> (pe, qe, ce : List Nat) -> PriQueueElems p pe -> PriQueueElems q qe -> TreeElems c ce -> PriQueueElems (join p q c) (ce++pe++qe)

mergeRelate : (p, q : PriQueue) -> (pl, ql, al : List Nat) -> priq p -> priq q -> PriQueueElems p pl -> PriQueueElems q ql -> PriQueueElems (merge p q) al -> Permutation al (pl++ql)

deleteMaxNothingRelate : (p : PriQueue) -> priq p -> (PriQueueElems p [] -> deleteMax p = Nothing, deleteMax p = Nothing -> PriQueueElems p []) 

deleteMaxJustRelate : (p, q : PriQueue) -> (k : Nat) -> (pl, ql : List Nat) -> priq p -> PriQueueElems p pl -> deleteMax p = Just (k, q) -> PriQueueElems q ql -> (Permutation pl (k::ql), All (GTE k) ql)