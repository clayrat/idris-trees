module Agda.Pivotal.JJ

import Data.So

%default total

data TopBot : Type -> Type where
  Top : TopBot t
  Bot : TopBot t
  Box : (x : t) -> TopBot t

Rel : Type -> Type
Rel X = (X, X) -> Type

BRel : Rel t -> Rel (TopBot t)
BRel _ (_    , Top  ) = ()
BRel L (Box x, Box y) = L (x, y)
BRel _ (Bot  , _    ) = ()
BRel _ (_    , _    ) = Void

infixr 5 /\.
infixr 4 *.
infixr 3 +.
infixr 2 ->.

(+.) : {t : Type} -> (t -> Type) -> (t -> Type) -> (t -> Type)
(+.) S T i = Either (S i) (T i)

(*.) : {t : Type} -> (t -> Type) -> (t -> Type) -> (t -> Type)
(*.) S T i = (S i, T i)

(->.) : {t : Type} -> (t -> Type) -> (t -> Type) -> (t -> Type)
(->.) S T i = S i -> T i

Bd : {I : Type} -> (I -> Type) -> Type
Bd {I} F = {i : I} -> F i

(/\.) : Rel (TopBot t) -> Rel (TopBot t) -> Rel (TopBot t)
(/\.) {t} S T lu = (p : t ** (S (fst lu, Box p), T (Box p, snd lu)))

data JJ : Type where
  R : JJ               -- recursive substructure
  P : JJ               -- parameter
  U : JJ               -- 1
  Pl : JJ -> JJ -> JJ
  Ti : JJ -> JJ -> JJ

IntJJ : JJ -> Type -> Type -> Type
IntJJ  R       A _ = A
IntJJ  P       _ B = B
IntJJ  U       _ _ = ()
IntJJ (Pl S T) A B = Either (IntJJ S A B) (IntJJ T A B)
IntJJ (Ti S T) A B = (IntJJ S A B, IntJJ T A B)

data MuJJ : (f : JJ) -> (p : Type) -> Type where
  MkMuJJ : IntJJ f (MuJJ f p) p -> MuJJ f p 

traverse : Applicative h => (a -> h b) -> MuJJ f a -> h (MuJJ f b)
traverse {h} ahb t = go R t 
  where
  go : (g : JJ) -> IntJJ g (MuJJ f a) a -> h (IntJJ g (MuJJ f b) b)
  go  R       (MkMuJJ t) = pure MkMuJJ <*> go f t
  go  P       x          = ahb x
  go  U       ()         = pure ()
  go (Pl S _) (Left s)   = pure Left <*> go S s
  go (Pl _ T) (Right t)  = pure Right <*> go T t
  go (Ti S T) (s,t)      = pure MkPair <*> go S s <*> go T t

[idFun] Functor (\x => x) where
  map = id

using implementation idFun
  [idApp] Applicative (\x => x) where
    pure = id
    (<*>) = id

map : (a -> b) -> MuJJ f a -> MuJJ f b
map = traverse @{idApp}

[cnstFun] Functor (\_ => x) where
  map _ = id

using implementation cnstFun
  [monApp] Monoid x => Applicative (\_ => x) where
    pure = \_ => neutral
    (<*>) = (<+>)

crush : Monoid x => (p -> x) -> MuJJ f p -> x
crush {x} = JJ.traverse {b=x} @{monApp}

[compSemi] Semigroup (x -> x) where
  (<+>) = (.)

using implementation compSemi
  [compMon] Monoid (x -> x) where
    neutral = id

foldr : (a -> b -> b) -> b -> MuJJ f a -> b
foldr f b t = crush @{compMon} f t b

data SO : Type where
  Ro : SO               -- recursive substructure
  Uo : SO               -- 1
  Plo : SO -> SO -> SO
  Pvo : SO -> SO -> SO

IntSO : SO -> JJ
IntSO  Ro = R
IntSO  Uo = U
IntSO (Plo S T) = (IntSO S) `Pl` (IntSO T)
IntSO (Pvo S T) = (IntSO S) `Ti` (P `Ti` (IntSO T))

MuSO : SO -> Type -> Type
MuSO f p = MuJJ (IntSO f) p

SOList : SO
SOList = Uo `Plo` (Uo `Pvo` Ro)

SOTree : SO
SOTree = Uo `Plo` (Ro `Pvo` Ro)

SOInterval : SO
SOInterval = Uo `Pvo` Uo

tree : MuSO f p -> MuSO SOTree p
tree {f} (MkMuJJ t) = go f t 
  where
  go : (g : SO) -> (IntJJ (IntSO g)) (MuSO f p) p -> MuSO SOTree p
  go  Ro       f         = tree f
  go  Uo       ()        = MkMuJJ $ Left ()
  go (Plo S _) (Left s)  = go S s
  go (Plo _ T) (Right t) = go T t
  go (Pvo S T) (s, p, t) = MkMuJJ $ Right (go S s, p, go T t)

IntSOlte : SO -> Rel (TopBot p) -> Rel p -> Rel (TopBot p)
IntSOlte  Ro       r _ = r
IntSOlte  Uo       _ l = BRel l
IntSOlte (Plo S T) r l = IntSOlte S r l +. IntSOlte T r l
IntSOlte (Pvo S T) r l = IntSOlte S r l /\. IntSOlte T r l

data MuSOlte : (f : SO) -> (l : Rel p) -> (lu : (TopBot t, TopBot t)) -> Type where
  MkMuSOlte : IntSOlte f (MuSOlte f l) l lu -> MuSOlte f l lu

MuTree : Rel t -> Rel (TopBot t)
MuTree l = MuSOlte SOTree l

MuInterval : Rel t -> Rel (TopBot t)
MuInterval l = MuSOlte SOInterval l

tree1 : {lt : Rel pt} -> MuSOlte ft lt lu1 -> MuTree lt lu1
tree1 {lu1} {ft} {lt} {pt} (MkMuSOlte t) = go {lu=lu1} ft t 
  where
  go : {lu : (TopBot pt, TopBot pt)} -> (g : SO) -> (IntSOlte g) (MuSOlte ft lt) lt lu -> MuTree lt lu
  go  Ro        f        = tree1 f
  go  Uo        x        = MkMuSOlte $ Left x
  go (Plo S _) (Left l)  = go S l
  go (Plo _ T) (Right r) = go T r
  go {lu} (Pvo S T) (p ** (l,r)) = MkMuSOlte $ Right (p ** ( go {lu = (fst lu, Box p)} S l
                                                           , go {lu = (Box p, snd lu)} T r))