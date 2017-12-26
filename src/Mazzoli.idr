module Mazzoli

%default total

-- https://mazzo.li/posts/AgdaSort.html

Rel : Type -> Type
Rel X = X -> X -> Type

Decide : Rel t -> Type
Decide {t} R = (a, b : t) -> Dec (R a b)

interface TotalOrd (o : Rel t) where
  Asym : {x, y : t} -> o x y -> o y x -> x = y
  Trns : {x, y, z : t} -> o x y -> o y z -> o x z
  Totl : {x, y : t} -> Either (o x y) (o y x)
  Rflx : {x, y : t} -> x = y -> o x y
  
-- insertion sort

data TopBot : Type where
  Top : TopBot
  Bot : TopBot
  Box : t -> TopBot    

data BoundOrd : Rel TopBot where
  BotOrd : BoundOrd Bot x
  TopOrd : BoundOrd x Top
  Lift : TotalOrd o => o x y -> BoundOrd (Box x) (Box y)

data OList : (l, u : TopBot) -> Type -> Type where
  Nil : BoundOrd l u -> OList l u t 
  Cons : (x : t) -> (xs : OList (Box x) u t) -> BoundOrd l (Box x) -> OList l u t

toList : OList l u t -> List t
toList (Nil _) = []
toList (Cons x xs _) = x :: toList xs

insert : TotalOrd o => Decide {t} o -> (x : t) -> OList l u t -> BoundOrd l (Box x) -> BoundOrd (Box x) u -> OList l u t
insert       _ x (Nil _)         lox xou = Cons x (Nil xou) lox
insert @{to} d x (Cons y ys loy) lox xou with (d {a=x} {b=y})
  | Yes xoy = Cons x (Cons y ys (Lift @{to} xoy)) lox
  | No xny  = Cons y (insert @{to} d x ys (either (Lift @{to}) (\xoy => absurd $ xny xoy) (Totl @{to} {x=y} {y=x})) xou) loy

isort1 : TotalOrd o => Decide {t} o -> List t -> OList Bot Top t
isort1 @{to} d = foldr (\x, xs => insert @{to} d x xs BotOrd TopOrd) (Nil BotOrd) 

isort : TotalOrd o => Decide {t} o -> List t -> List t
isort @{to} d xs = toList (isort1 @{to} d xs)

-- tree sort

data Tree : (l, u : TopBot) -> Type -> Type where
  Leaf : BoundOrd l u -> Tree l u t
  Node : (x : t) -> Tree l (Box x) t -> Tree (Box x) u t -> Tree l u t

newLeaf : TotalOrd o => Decide {t} o -> (x : t) -> Tree l u t -> BoundOrd l (Box x) -> BoundOrd (Box x) u -> Tree l u t
newLeaf       _ x (Leaf _)         lox xou = Node x (Leaf lox) (Leaf xou)
newLeaf @{to} d x (Node y loy you) lox xou with (d {a=x} {b=y})
 | Yes xoy = Node y (newLeaf @{to} d x loy lox (Lift @{to} xoy)) you
 | No xny = Node y loy (newLeaf @{to} d x you (either (\xoy => absurd $ xny xoy) (Lift @{to}) (Totl @{to} {x} {y})) xou)

fromList : TotalOrd o => Decide {t} o -> List t -> Tree Bot Top t
fromList @{to} d = foldr (\x, xs => newLeaf @{to} d x xs BotOrd TopOrd) (Leaf BotOrd) 

concatIns : (x : t) -> OList l (Box x) t -> OList (Box x) u t -> OList l u t
concatIns x (Nil lou)      xs = Cons x xs lou
concatIns x (Cons y ys loy)xs = Cons y (concatIns x ys xs) loy

flatten : Tree l u t -> OList l u t
flatten (Leaf lou)     = Nil lou
flatten (Node x lx xu) = concatIns x (flatten lx) (flatten xu)

treeSort1 : TotalOrd o => Decide {t} o -> List t -> OList Bot Top t
treeSort1 @{to} d xs = flatten (foldr (\x, xs => newLeaf @{to} d x xs BotOrd TopOrd) (Leaf BotOrd) xs)

treeSort : TotalOrd o => Decide {t} o -> List t -> List t
treeSort @{to} d xs = toList (treeSort1 @{to} d xs)

-- for nats

decideLTE : Decide {t=Nat} LTE 
decideLTE Z      _    = Yes LTEZero
decideLTE (S k)  Z    = No uninhabited
decideLTE (S k) (S j) with (decideLTE k j)
  | Yes xly = Yes (LTESucc xly)
  | No  xny = No (xny . fromLteSucc)

TotalOrd (LTE) where
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
willBeSorted = treeSort decideLTE [12, 3, 7, 4, 40, 5, 0]