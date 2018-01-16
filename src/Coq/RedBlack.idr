module RedBlack 

import Ord

import Data.Biz
import Data.Biz.Ord

%default total

data Color = Red | Black

data Tree : Type -> Type where
  E : Tree v
  T : Color -> Tree v -> Int -> v -> Tree v -> Tree v    
  
emptyTree : Tree v 
emptyTree = E

lookup : (x : Int) -> (default : v) -> (t : Tree v) -> v 
lookup _ default  E              = default
lookup x default (T _ tl k val tr) =
  if x < k 
    then lookup x default tl 
    else if k < x then lookup x default tr      
                  else val

balance : Color -> Tree v -> Int -> v -> Tree v -> Tree v
balance Red    t1                             k vk  t2                             = T Red t1 k vk t2
balance Black (T Red (T Red a x vx b) y vy c) k vk  t2                             = T Red (T Black a x vx b)  y vy (T Black c k vk t2)
balance Black (T Red a x vx (T Red b y vy c)) k vk  t2                             = T Red (T Black a x vx b)  y vy (T Black c k vk t2)
balance Black  t1                             k vk (T Red (T Red b y vy c) z vz d) = T Red (T Black t1 k vk b) y vy (T Black c z vz d)
balance Black  t1                             k vk (T Red b y vy (T Red c z vz d)) = T Red (T Black t1 k vk b) y vy (T Black c z vz d)
balance Black  t1                             k vk  t2                             = T Black t1 k vk t2

makeBlack : Tree v -> Tree v 
makeBlack  E             = E
makeBlack (T _ a x vx b) = T Black a x vx b

ins : Int -> v -> Tree v -> Tree v
ins x vx  E             = T Red E x vx E
ins x vx (T c a y vy b) = 
  if x < y then balance c (ins x vx a) y vy b
           else if y < x then balance c a y vy (ins x vx b)
                         else T c a x vx b

insert : Int -> v -> Tree v -> Tree v
insert x vx s = makeBlack $ ins x vx s

Uninhabited (T c l k v r = E) where
  uninhabited Refl impossible
 
-- TODO automate via elab reflection

-- insNotE : (x : Int) -> (vx : v) -> (s : Tree v) -> Not (ins x vx s = E)
-- insNotE x vx E = absurd
-- insNotE x vx (T y z w s t) = ?wat1

int2z : Int -> Biz
int2z = fromInteger . cast

data SearchTreeProp : Biz -> Tree v -> Biz -> Type where
  ST_E : lo `Le` hi -> SearchTreeProp lo E hi
  ST_T : SearchTreeProp lo l (int2z k) -> SearchTreeProp (int2z k + 1) r hi -> SearchTreeProp lo (T c l k v r) hi

data SearchTree : Tree v -> Type where
  ST_intro : SearchTreeProp lo t hi -> SearchTree t  

-- TODO automate via elab reflection

-- balanceSearchTree : (c : Color) -> (s1 : Tree v) -> (k : Int) -> (kv : v) -> (s2 : Tree v) -> (lo, hi : Biz) 
--                  -> SearchTreeProp lo s1 (int2z k) -> SearchTreeProp (int2z k + 1) s2 hi -> SearchTreeProp lo (balance c s1 k kv s2) hi  
-- balanceSearchTree c s1 k kv s2 lo hi prf1 prf2 = ?wat2
--
-- insSearchTree : (x : Int) -> (vx : v) -> (s : Tree v) -> (lo, hi : Biz) 
--              -> lo `Le` int2z x -> int2z x `Lt` hi -> SearchTreeProp lo s hi -> SearchTreeProp lo (ins x vx s) hi
-- insSearchTree x vx s lo hi lolex xlthi prf = ?wat3
             
emptyTreeSearchTree : SearchTree {v} $ emptyTree {v}
emptyTreeSearchTree = ST_intro $ ST_E {lo=0} {hi=0} uninhabited

SearchTreePropLTE : SearchTreeProp lo t hi -> lo `Le` hi  
SearchTreePropLTE           (ST_E e)           = e
SearchTreePropLTE {lo} {hi} (ST_T {k} stl str) = 
  leTrans lo (int2z k + 1) hi 
    (leSuccR lo (int2z k) $ SearchTreePropLTE stl)
    (SearchTreePropLTE str)

expandRangeSearchTreeProp : (s : Tree v) -> (lo, hi : Biz) -> SearchTreeProp lo s hi 
                         -> (lo1, hi1 : Biz) -> lo1 `Le` lo -> hi `Le` hi1 -> SearchTreeProp lo1 s hi1
expandRangeSearchTreeProp E lo hi (ST_E lohi) lo1 hi1 l1le h1le = 
  ST_E $ leTrans lo1 lo hi1 l1le $ leTrans lo hi hi1 lohi h1le
expandRangeSearchTreeProp (T _ l k _ r) lo hi (ST_T stl str) lo1 hi1 l1le h1le = 
  ST_T 
    (expandRangeSearchTreeProp l  lo           (int2z k) stl  lo1          (int2z k)  l1le                  (leRefl $ int2z k))
    (expandRangeSearchTreeProp r (int2z k + 1)  hi       str (int2z k + 1)  hi1      (leRefl $ int2z k + 1)  h1le             )
   
-- TODO relies on `insSearchTree` above 

-- insertSearchTree : (x : Int) -> (vx : v) -> (s : Tree v) -> SearchTree s -> SearchTree (insert x vx s)                         
-- insertSearchTree x vx s st = ?wat4

-- TODO TotalMap relations

data IsRedblack : Tree v -> Color -> Nat -> Type where
  IsRB_leaf : IsRedblack E c Z
  IsRB_r : IsRedblack tl Red   n -> IsRedblack tr Red   n -> IsRedblack (T Red   tl k kv tr) Black  n
  IsRB_b : IsRedblack tl Black n -> IsRedblack tr Black n -> IsRedblack (T Black tl k kv tr) c     (S n)

isRedblackToblack : (s : Tree v) -> (n : Nat) -> IsRedblack s Red n -> IsRedblack s Black n  
isRedblackToblack  E                 Z     IsRB_leaf         = IsRB_leaf
isRedblackToblack (T Black _ _ _ _) (S _) (IsRB_b irbl irbr) = IsRB_b irbl irbr

-- the tree is a red-black tree, except that it's nonempty and it is permitted to have two red nodes in a row at the very root (only)

data NearlyRedblack : Tree v -> Nat -> Type where
  NRB_r : IsRedblack tl Black n -> IsRedblack tr Black n -> NearlyRedblack (T Red tl k kv tr) n
  NRB_b : IsRedblack tl Black n -> IsRedblack tr Black n -> NearlyRedblack (T Black tl k kv tr) (S n)

-- TODO automate via elab reflection
  
-- insIsRedblack : (x : Int) -> (vx : v) -> (s : Tree v) -> (n : Nat) 
--              -> (IsRedblack s Black n -> NearlyRedblack (ins x vx s) n, IsRedblack s Red n -> IsRedblack (ins x vx s) Black n)  
-- insIsRedblack x vx s n = ?wat5
-- 
-- insertIsRedblack : (x : Int) -> (vx : v) -> (s : Tree v) -> (n : Nat) -> IsRedblack s Red n -> (n1 : Nat ** IsRedblack (insert x vx s) Red n1)  
-- insertIsRedblack x vx s n prf = ?wat6