module Mazzoli

%default total

-- https://mazzo.li/posts/AgdaSort.html

Rel : Type -> Type
Rel X = X -> X -> Type

interface DecRel (o : Rel t) where
  decRel : (a, b : t) -> Dec (o a b)

interface TotalOrd (o : Rel t) where
  Asym : {x, y    : t} -> o x y -> o y x -> x = y
  Trns : {x, y, z : t} -> o x y -> o y z -> o x z
  Totl : {x, y    : t} -> Either (o x y) (o y x)
  Rflx : {x, y    : t} -> x = y -> o x y
  
-- insertion sort

data TopBot : Type where
  Top : TopBot
  Bot : TopBot
  Box : t -> TopBot    

data BoundOrd : Rel TopBot where
  BotO : BoundOrd Bot x
  TopO : BoundOrd x Top
  Lift : TotalOrd o => o x y -> BoundOrd (Box x) (Box y)

data OList : (l, u : TopBot) -> Type -> Type where
  Nil : BoundOrd l u -> OList l u t 
  Cons : (x : t) -> (xs : OList (Box x) u t) -> BoundOrd l (Box x) -> OList l u t

toList : OList l u t -> List t
toList (Nil _) = []
toList (Cons x xs _) = x :: toList xs

insert : (TotalOrd {t} o, DecRel {t} o) => (x : t) -> OList l u t -> BoundOrd l (Box x) -> BoundOrd (Box x) u -> OList l u t
insert                 x (Nil _)         lx xu = Cons x (Nil xu) lx
insert @{to} @{dr} {t} x (Cons y ys ly) lx xu with (decRel @{dr} {t} x y)
  | Yes xoy = Cons x (Cons y ys (Lift @{to} xoy)) lx
  | No xny  = Cons y (insert @{to} @{dr} x ys (either (Lift @{to}) (\xoy => absurd $ xny xoy) (Totl @{to} {x=y} {y=x})) xu) ly

isort1 : (TotalOrd {t} o, DecRel {t} o) => List t -> OList Bot Top t
isort1 @{to} @{dr} = foldr (\x, xs => insert @{to} @{dr} x xs BotO TopO) (Nil BotO) 

isort : (TotalOrd {t} o, DecRel {t} o) => List t -> List t
isort @{to} @{dr} xs = toList (isort1 @{to} @{dr} xs)

-- tree sort

data Tree : (l, u : TopBot) -> Type -> Type where
  Leaf : BoundOrd l u -> Tree l u t
  Node : (x : t) -> Tree l (Box x) t -> Tree (Box x) u t -> Tree l u t

newLeaf : (TotalOrd {t} o, DecRel {t} o) => (x : t) -> Tree l u t -> BoundOrd l (Box x) -> BoundOrd (Box x) u -> Tree l u t
newLeaf                 x (Leaf _)         lx xu = Node x (Leaf lx) (Leaf xu)
newLeaf @{to} @{dr} {t} x (Node y ly yu) lx xu with (decRel @{dr} {t} x y)
 | Yes xoy = Node y (newLeaf @{to} @{dr} x ly lx (Lift @{to} xoy)) yu
 | No xny = Node y ly (newLeaf @{to} @{dr} x yu (either (\xoy => absurd $ xny xoy) (Lift @{to}) (Totl @{to} {x} {y})) xu)

fromList : (TotalOrd {t} o, DecRel {t} o) => List t -> Tree Bot Top t
fromList @{to} @{dr} = foldr (\x, xs => newLeaf @{to} @{dr} x xs BotO TopO) (Leaf BotO) 

concatIns : (x : t) -> OList l (Box x) t -> OList (Box x) u t -> OList l u t
concatIns x (Nil lu)       xs = Cons x xs lu
concatIns x (Cons y ys ly) xs = Cons y (concatIns x ys xs) ly

flatten : Tree l u t -> OList l u t
flatten (Leaf lu)     = Nil lu
flatten (Node x lx xu) = concatIns x (flatten lx) (flatten xu)

treeSort1 : (TotalOrd {t} o, DecRel {t} o) => List t -> OList Bot Top t
treeSort1 @{to} @{dr} xs = flatten (foldr (\x, xs => newLeaf @{to} @{dr} x xs BotO TopO) (Leaf BotO) xs)

treeSort : (TotalOrd {t} o, DecRel {t} o) => List t -> List t
treeSort @{to} @{dr} xs = toList (treeSort1 @{to} @{dr} xs)

-- for nats

DecRel LTE where
  decRel  Z     _    = Yes LTEZero
  decRel (S k)  Z    = No uninhabited
  decRel (S k) (S j) with (decRel {o=LTE} k j)
    | Yes xly = Yes (LTESucc xly)
    | No  xny = No (xny . fromLteSucc)

TotalOrd LTE where
  Asym LTEZero LTEZero = Refl
  Asym (LTESucc lxy) (LTESucc lyx) = cong $ Asym lxy lyx

  Trns LTEZero _ = LTEZero
  Trns (LTESucc lxy) (LTESucc lyz) = LTESucc (Trns lxy lyz)

  Totl {x=Z}           = Left LTEZero
  Totl {x=S k} {y=Z  } = Right LTEZero
  Totl {x=S k} {y=S j} with (Totl {o=LTE} {x=k} {y=j})
    | Left  xly = Left  (LTESucc xly)
    | Right ylx = Right (LTESucc ylx)

  Rflx Refl = lteRefl

willBeSorted : List Nat 
willBeSorted = treeSort {o=LTE} [12, 3, 7, 4, 40, 5, 0]
