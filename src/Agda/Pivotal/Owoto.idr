module Agda.Pivotal.Owoto

%default total

data TopBot : Type -> Type where
  Top : TopBot t
  Bot : TopBot t
  Box : (x : t) -> TopBot t

Rel : Type -> Type
Rel t = (t, t) -> Type

OWOTO : Rel t -> Rel t
OWOTO l (x,y) = Either (l (x,y)) (l (y,x))

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
BRel l (Box x, Box y) = l (x, y)
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

(+.) : {x : Type} -> (x -> Type) -> (x -> Type) -> (x -> Type)
(+.) s t i = Either (s i) (t i)

(*.) : {x : Type} -> (x -> Type) -> (x -> Type) -> (x -> Type)
(*.) s t i = (s i, t i)

(->.) : {x : Type} -> (x -> Type) -> (x -> Type) -> (x -> Type)
(->.) s t i = s i -> t i

Bd : {x : Type} -> (x -> Type) -> Type
Bd {x} f = {i : x} -> f i

(/\.) : Rel (TopBot x) -> Rel (TopBot x) -> Rel (TopBot x)
(/\.) {x} s t lu = (p : x ** (s (fst lu, Box p), t (Box p, snd lu)))

It : Rel t -> Rel (TopBot t)
It l = BRel l /\. BRel l

owoto : {r : Rel t} -> (x, y : t) -> OWOTO r (x,y)

-- bad2

-- data BST : (lu : (TopBot t, TopBot t)) -> Type where
--   BLeaf : BST lu    
--   BNode : ((BRel l *. BST) /\. (BRel l *. BST)) lu -> BST lu
--   
--   -- lp doesn't want to fit, probably because of indexed stuff  
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