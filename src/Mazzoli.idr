module Mazzoli

%default total

-- https://mazzo.li/posts/AgdaSort.html

Rel : Type -> Type
Rel X = X -> X -> Type

interface TotalOrd (t : Type) (o : Rel t) | o where
  Asym : {x, y    : t} -> o x y -> o y x -> x = y
  Trns : {x, y, z : t} -> o x y -> o y z -> o x z
  Totl : {x, y    : t} -> Either (o x y) (o y x)
  Rflx : {x, y    : t} -> x = y -> o x y

decOrd : (TotalOrd t o, DecEq t) => (a, b : t) -> Dec (o a b)
decOrd @{to} a b =
  case Totl @{to} {x=a} {y=b} of
    Left l => Yes l
    Right r => case decEq a b of
                 Yes eq => Yes $ Rflx @{to} eq
                 No neq => No $ \oab => neq $ Asym @{to} oab r

-- insertion sort

data TopBot : Type where
  Top : TopBot
  Bot : TopBot
  Box : t -> TopBot

data BoundOrd : Rel TopBot where
  BotO : BoundOrd Bot x
  TopO : BoundOrd x Top
  Lift : TotalOrd t o => o x y -> BoundOrd (Box x) (Box y)

data OList : (l, u : TopBot) -> Type -> Type where
  Nil  : BoundOrd l u -> OList l u t
  Cons : (x : t) -> (xs : OList (Box x) u t) -> BoundOrd l (Box x) -> OList l u t

toList : OList l u t -> List t
toList (Nil _) = []
toList (Cons x xs _) = x :: toList xs

insert : (TotalOrd t o, DecEq t) => (x : t) -> OList l u t -> BoundOrd l (Box x) -> BoundOrd (Box x) u -> OList l u t
insert       x (Nil _)        lx xu = Cons x (Nil xu) lx
insert @{to} x (Cons y ys ly) lx xu with (decOrd @{to} x y)
  | Yes xoy = Cons x (Cons y ys (Lift xoy)) lx
  | No xny  = Cons y (insert  @{to} x ys (either Lift (\xoy => absurd $ xny xoy) (Totl {x=y} {y=x})) xu) ly

isort1 : (TotalOrd t o, DecEq t) => List t -> OList Bot Top t
isort1 @{to} = foldr (\x, xs => insert @{to} x xs BotO TopO) (Nil BotO)

isort : (TotalOrd t o, DecEq t) => List t -> List t
isort @{to} xs = toList (isort1 @{to} xs)

-- tree sort

data Tree : (l, u : TopBot) -> Type -> Type where
  Leaf : BoundOrd l u -> Tree l u t
  Node : (x : t) -> Tree l (Box x) t -> Tree (Box x) u t -> Tree l u t

newLeaf : (TotalOrd t o, DecEq t) => (x : t) -> Tree l u t -> BoundOrd l (Box x) -> BoundOrd (Box x) u -> Tree l u t
newLeaf       x (Leaf _)       lx xu = Node x (Leaf lx) (Leaf xu)
newLeaf @{to} x (Node y ly yu) lx xu with (decOrd @{to} x y)
 | Yes xoy = Node y (newLeaf @{to} x ly lx (Lift xoy)) yu
 | No xny = Node y ly (newLeaf @{to} x yu (either (\xoy => absurd $ xny xoy) Lift Totl) xu)

fromList : (TotalOrd t o, DecEq t) => List t -> Tree Bot Top t
fromList @{to} = foldr (\x, xs => newLeaf @{to} x xs BotO TopO) (Leaf BotO)

concatIns : (x : t) -> OList l (Box x) t -> OList (Box x) u t -> OList l u t
concatIns x (Nil lu)       xs = Cons x xs lu
concatIns x (Cons y ys ly) xs = Cons y (concatIns x ys xs) ly

flatten : Tree l u t -> OList l u t
flatten (Leaf lu)      = Nil lu
flatten (Node x lx xu) = concatIns x (flatten lx) (flatten xu)

treeSort1 : (TotalOrd t o, DecEq t) => List t -> OList Bot Top t
treeSort1 @{to} xs = flatten (foldr (\x, xs => newLeaf @{to} x xs BotO TopO) (Leaf BotO) xs)

treeSort : (TotalOrd t o, DecEq t) => List t -> List t
treeSort @{to} xs = toList (treeSort1 @{to} xs)

TotalOrd Nat LTE where
  Asym  LTEZero       LTEZero      = Refl
  Asym (LTESucc lxy) (LTESucc lyx) = cong $ Asym {o=LTE} lxy lyx

  Trns  LTEZero       _            = LTEZero
  Trns (LTESucc lxy) (LTESucc lyz) = LTESucc (Trns {o=LTE} lxy lyz)

  Totl {x=Z}           = Left LTEZero
  Totl {x=S k} {y=Z  } = Right LTEZero
  Totl {x=S k} {y=S j} with (Totl {o=LTE} {x=k} {y=j})
    | Left  xly = Left  (LTESucc xly)
    | Right ylx = Right (LTESucc ylx)

  Rflx Refl = lteRefl

willBeSorted : List Nat
willBeSorted = treeSort {o=LTE} [12, 3, 7, 4, 40, 5, 0]
