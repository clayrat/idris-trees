module Agda.Pivotal.IOU

%default total

-- TODO move into common

data TopBot : Type -> Type where
    Top : TopBot t
    Bot : TopBot t
    Box : (x : t) -> TopBot t
  
Rel : Type -> Type
Rel t = (t, t) -> Type

BRel : Rel t -> Rel (TopBot t)
BRel _ (_    , Top  ) = ()
BRel l (Box x, Box y) = l (x, y)
BRel _ (Bot  , _    ) = ()
BRel _ (_    , _    ) = Void

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

interface DecRel (t : Type) (l : Rel t) | l where
    decRel : (x, y : t) -> Either (l (x,y)) (l (y,x))

---    

data IOU : Type -> Type where
  R : i -> IOU i
  O : IOU i
  I : IOU i
  Pl : IOU i -> IOU i -> IOU i
  Pv : IOU i -> IOU i -> IOU i

IntIOlte : IOU i -> (i -> Rel (TopBot p)) -> Rel p -> Rel (TopBot p)
IntIOlte (R i)    r _ = r i
IntIOlte  O       _ _ = \_ => Void
IntIOlte  I       _ l = BRel l
IntIOlte (Pl s t) r l = IntIOlte s r l +. IntIOlte t r l
IntIOlte (Pv s t) r l = IntIOlte s r l /\. IntIOlte t r l

data MuIOlte : (f : i -> IOU i) -> (l : Rel p) -> (j : i) -> (lu : (TopBot t, TopBot t)) -> Type where
  MkMuIOlte : IntIOlte (f j) (MuIOlte f l) l lu -> MuIOlte f l j lu

IOList : () -> IOU ()
IOList () = I `Pl` (I `Pv` R ())

IOTree : () -> IOU ()
IOTree () = I `Pl` (R () `Pv` R ())

IOInterval : () -> IOU ()
IOInterval () = I `Pv` I

MuList : Rel t -> Rel (TopBot t)
MuList l = MuIOlte IOList l ()

MuTree : Rel t -> Rel (TopBot t)
MuTree l = MuIOlte IOTree l ()

MuInterval : Rel t -> Rel (TopBot t)
MuInterval l = MuIOlte IOInterval l ()

IOVec : Nat -> IOU Nat
IOVec Z = I
IOVec (S n) = I `Pv` R n

IOEven : Nat -> IOU Nat
IOEven  Z        = I
IOEven (S  Z)    = O
IOEven (S (S n)) = I `Pv` (I `Pv` R n)

IOTree23 : Nat -> IOU Nat
IOTree23 Z = I
IOTree23 (S h) = R h `Pv` (R h `Pl` (R h `Pv` R h))

Mu23 : Rel t -> Nat -> Rel (TopBot t)
Mu23 l = MuIOlte IOTree23 l

ins23 :  DecRel t l => (h : Nat) -> MuInterval l lu -> Mu23 l h lu -> Either (Mu23 l h lu) (p ** (Mu23 l h (fst lu, Box p), Mu23 l h (Box p, snd lu)))
ins23        Z    (MkMuIOlte (y ** (l, r))) _ = Right (y ** (MkMuIOlte l, MkMuIOlte r))
ins23 @{dr} (S k) (MkMuIOlte (y ** (l, r))) (MkMuIOlte (p ** (lt, rest))) with (decRel @{dr} y p)
  ins23 (S k) (MkMuIOlte (y ** (l, r))) (MkMuIOlte (p ** (lt, rest))) | Left le  = ?wat
  ins23 (S k) (MkMuIOlte (y ** (l, r))) (MkMuIOlte (p ** (lt, rest))) | Right ge = ?wat2
