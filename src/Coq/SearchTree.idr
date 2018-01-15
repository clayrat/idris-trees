module Coq.SearchTree

import Ord 

%default total

-- after https://softwarefoundations.cis.upenn.edu/current/vfa-current/SearchTree.html

data Tree : Type -> Type where
  E : Tree v
  T : Tree v -> Nat -> v -> Tree v -> Tree v    

emptyTree : Tree v 
emptyTree = E

lookup : (x : Nat) -> (default : v) -> (t : Tree v) -> v 
lookup _ default  E              = default
lookup x default (T tl k val tr) =
  if x < k 
    then lookup x default tl 
    else if k < x then lookup x default tr      
                  else val

insert : (x : Nat) -> (val : v) -> (t : Tree v) -> Tree v
insert x val  E               = T E x val E
insert x val (T tl y val1 tr) =
  if x < y 
    then T (insert x val tl) y val1 tr
    else if y < x then T tl y val1 (insert x val tr)
                  else T tl x val tr

elements' : (t : Tree v) -> (base : List (Nat, v)) -> List (Nat, v)
elements'  E              base = base
elements' (T tl k val tr) base = elements' tl ((k,val) :: elements' tr base)

elements : (t : Tree v) -> List (Nat, v)
elements t = elements' t []

-- TODO totalMap equivalence / elements

data SearchTreeProp : Nat -> Tree v -> Nat -> Type where
  ST_E : LTE lo hi -> SearchTreeProp lo E hi
  ST_T : SearchTreeProp lo l k -> SearchTreeProp (S k) r hi -> SearchTreeProp lo (T l k v r) hi

data SearchTree : Tree v -> Type where
  ST_intro : SearchTreeProp 0 t hi -> SearchTree t

SearchTreePropLTE : SearchTreeProp lo t hi -> LTE lo hi  
SearchTreePropLTE (ST_E e) = e
SearchTreePropLTE (ST_T x y) = lteTransitive (lteSuccRight $ SearchTreePropLTE x) (SearchTreePropLTE y)

emptyTreeSearchTree : SearchTree {v} $ emptyTree {v}
emptyTreeSearchTree = ST_intro $ ST_E {hi=Z} LTEZero

insertSTPIn : SearchTreeProp lo t hi -> LTE lo k -> LTE (S k) hi -> SearchTreeProp lo (insert k v t) hi
insertSTPIn     (ST_E x)          ltelo ltehi = ST_T (ST_E ltelo) (ST_E ltehi)
insertSTPIn {k} (ST_T {k=k1} x y) ltelo ltehi with (compare k k1) proof cmp
  insertSTPIn {k} (ST_T {k=k1} x y) ltelo _     | LT =
    ST_T (insertSTPIn {k} x ltelo $ cmpLt k k1 $ sym cmp) y
  insertSTPIn {k} (ST_T {k=k1} x y) _     _     | EQ = 
    rewrite cmpOp k1 k in
    rewrite sym cmp in
    rewrite cmpEq k k1 (sym cmp) in
    ST_T x y
  insertSTPIn {k} (ST_T {k=k1} x y) _     ltehi | GT = 
    rewrite cmpOp k1 k in
    rewrite sym cmp in
    ST_T x (insertSTPIn {k} y (cmpLt k1 k $ rewrite cmpOp k1 k in
                                            rewrite sym cmp in
                                            Refl) ltehi)

insertSTPOut : SearchTreeProp lo t hi -> LTE hi k -> SearchTreeProp lo (insert k v t) (S hi + k)
insertSTPOut {hi} {k} (ST_E x)          lte = 
  ST_T (ST_E $ lteTransitive x lte) (ST_E $ LTESucc $ rewrite plusCommutative hi k in 
                                                      lteAddRight k) 
insertSTPOut      {k} (ST_T {k=k1} x y) lte = 
  rewrite cmpOp k k1 in 
  rewrite ltCmp k1 k (lteTransitive (SearchTreePropLTE y) lte) in  
  ST_T x (insertSTPOut {k} y lte)

insertSearchTree : SearchTree t -> SearchTree (insert k v t)
insertSearchTree {k} (ST_intro {hi} prf) = case cmpTotal k hi of 
  Left  khi => ST_intro $ insertSTPIn prf LTEZero khi
  Right hik => ST_intro $ insertSTPOut prf hik