module Pivotal

import Data.So

%default total

-- bad 1
{-
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
-}    

data TopBot : Type -> Type where
  Top : TopBot t
  Bot : TopBot t
  Box : (x : t) -> TopBot t

-- bad2
{-
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
-}

-- sorta works
{-
Rel : Type -> Type
Rel X = (X, X) -> Type

OWOTO : Rel t -> Rel t
OWOTO L (x,y) = Either (L (x,y)) (L (y,x))

LEaux : Nat -> Nat -> Type
LEaux  Z     _    = ()
LEaux (S _)  Z    = Void
LEaux (S x) (S y) = LEaux x y

LE : Rel Nat
LE (x, y) = LEaux x y

owotoN : (x, y : Nat) -> OWOTO LE (x,y)
owotoN  Z     _    = Left ()
owotoN (S _)  Z    = Right ()
owotoN (S x) (S y) = owotoN x y

BRel : Rel t -> Rel (TopBot t)
BRel _ (_    , Top  ) = ()
BRel L (Box x, Box y) = L (x, y)
BRel _ (Bot  , _    ) = ()
BRel _ (_    , _    ) = Void

-- O : Type -> Type
-- O _ = Void
-- 
-- I : Type -> Type
-- I _ = ()

infixr 5 /\.
infixr 4 *.
infixr 3 +.
infixr 2 ->.

-- (+.) : {t : Type} -> (t -> Type) -> (t -> Type) -> (t -> Type)
-- (+.) S T i = Either (S i) (T i)

(*.) : {t : Type} -> (t -> Type) -> (t -> Type) -> (t -> Type)
(*.) S T i = (S i, T i)

(->.) : {t : Type} -> (t -> Type) -> (t -> Type) -> (t -> Type)
(->.) S T i = S i -> T i

Bd : {I : Type} -> (I -> Type) -> Type
Bd {I} F = {i : I} -> F i

(/\.) : Rel (TopBot t) -> Rel (TopBot t) -> Rel (TopBot t)
(/\.) {t} S T lu = (p : t ** (S (fst lu, Box p), T (Box p, snd lu)))

It : Rel t -> Rel (TopBot t)
It L = BRel L /\. BRel L

owoto : {r : Rel t} -> (x, y : t) -> OWOTO r (x,y)

-- bad2

-- data BST : (lu : (TopBot t, TopBot t)) -> Type where
--   BLeaf : BST lu    
--   BNode : ((BRel l *. BST) /\. (BRel l *. BST)) lu -> BST lu
--   
--   -- lp doesn't want to fit  
-- insert : Bd (It l ->. BST ->. BST)
-- insert (y**yb)  BLeaf                         = BNode (y ** ((fst yb, BLeaf), (snd yb, BLeaf)))
-- insert {l} (y**yb) (BNode (p**((pl,lt),(pr,rt)))) with (owoto {r=l} y p)
--   insert {l} (y**yb) (BNode {l} (p**((pl,lt),(pr,rt)))) | Left  lp = BNode (p ** ( (pl, insert {l} (y**(fst yb, really_believe_me lp)) lt)
--                                                                                  , (pr,                                                rt)))
--   insert {l} (y**yb) (BNode {l} (p**((pl,lt),(pr,rt)))) | Right rp = BNode (p ** ((pl,lt), (pr, insert {l} (y ** (really_believe_me rp, snd yb)) rt)))
-- 
-- rotR : Bd (BST ->. BST)
-- rotR (BNode (p**((pl,BNode (m ** ((ml,lt),(mr,mt)))),(pr,rt)))) = BNode (m ** ?wat)
-- rotR t = t

data BST : (lu : (TopBot t, TopBot t)) -> Type where
  BLeaf : BRel l lu -> BST lu    
  BNode : (BST /\. BST) lu -> BST lu

-- should work but crashes checker

--insert : Bd (It l ->. BST ->. BST)
--insert (y**yb) (BLeaf o)  = BNode (y ** (BLeaf (fst yb), BLeaf (snd yb)))
--insert (y**yb) (BNode (p**(a,b))) = ?wat2

rotR : Bd (BST ->. BST)
rotR (BNode (p**(BNode (m**(lt,mt)),rt))) = BNode (m ** (lt, BNode (p ** (mt, rt))))
rotR t = t

data OList : (lu : (TopBot t, TopBot t)) -> Type where
  Nil : BRel l lu -> OList lu    
  Cons : (BRel l /\. OList) lu -> OList lu
-}


data JJ : Type where
  R : JJ               -- recursive substructure
  P : JJ               -- parameter
  U : JJ               -- 1
  Pl : JJ -> JJ -> JJ
  Ti : JJ -> JJ -> JJ

Interp : JJ -> Type -> Type -> Type
Interp R A _ = A
Interp P _ B = B
Interp U _ _ = ()
Interp (Pl S T) A B = Either (Interp S A B) (Interp T A B)
Interp (Ti S T) A B = (Interp S A B, Interp T A B)

data MuJJ : (f : JJ) -> (p : Type) -> Type where
  MkMuJJ : Interp f (MuJJ f p) p -> MuJJ f p 

traverse : Applicative h => (a -> h b) -> MuJJ f a -> h (MuJJ f b)
traverse {h} ahb t = go R t 
  where
  go : (g : JJ) -> Interp g (MuJJ f a) a -> h (Interp g (MuJJ f b) b)
  go R (MkMuJJ t) = pure MkMuJJ <*> go f t
  go P x = ahb x
  go U () = pure ()
  go (Pl S _) (Left s) = pure Left <*> go S s
  go (Pl _ T) (Right t) = pure Right <*> go T t
  go (Ti S T) (s,t) = pure MkPair <*> go S s <*> go T t

[idFun] Functor (\x => x) where
  map = id

using implementation idFun
  [idApp] Applicative (\x => x) where
    pure = id
    (<*>) = id
