module Agda.Pivotal.JJ

import Data.So

%default total

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

data JJ : Type where
  R : JJ               -- recursive substructure
  P : JJ               -- parameter
  U : JJ               -- 1
  Pl : JJ -> JJ -> JJ
  Ti : JJ -> JJ -> JJ

IntJJ : JJ -> Type -> Type -> Type
IntJJ  R       a _ = a
IntJJ  P       _ b = b
IntJJ  U       _ _ = ()
IntJJ (Pl s t) a b = Either (IntJJ s a b) (IntJJ t a b)
IntJJ (Ti s t) a b = (IntJJ s a b, IntJJ t a b)

data MuJJ : (f : JJ) -> (p : Type) -> Type where
  MkMuJJ : IntJJ f (MuJJ f p) p -> MuJJ f p 

traverse : Applicative h => (a -> h b) -> MuJJ f a -> h (MuJJ f b)
traverse {h} ahb t = go R t 
  where
  go : (g : JJ) -> IntJJ g (MuJJ f a) a -> h (IntJJ g (MuJJ f b) b)
  go  R         (MkMuJJ t) = pure MkMuJJ <*> go f t
  go  P         x          = ahb x
  go  U         ()         = pure ()
  go (Pl st _ ) (Left s)   = pure Left <*> go st s
  go (Pl _  tt) (Right t)  = pure Right <*> go tt t
  go (Ti st tt) (s,t)      = pure MkPair <*> go st s <*> go tt t

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
crush {x} = traverse {b=x} @{monApp}

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
  go  Ro         f         = tree f
  go  Uo         ()        = MkMuJJ $ Left ()
  go (Plo st  _) (Left s)  = go st s
  go (Plo _  tt) (Right t) = go tt t
  go (Pvo st tt) (s, p, t) = MkMuJJ $ Right (go st s, p, go tt t)

-- TODO figure out how to use indexed stuff from idris-tparsec
-- we get problems later in insert
IntSOlte : SO -> Rel (TopBot x) -> Rel x -> Rel (TopBot x)
IntSOlte  Ro       r _ i = r i
IntSOlte  Uo       _ l i = BRel l i
-- IntSOlte (Plo s t) r l = IntSOlte s r l +. IntSOlte t r l
-- IntSOlte (Pvo s t) r l = IntSOlte s r l /\. IntSOlte t r l
IntSOlte (Plo s t) r l i = Either (IntSOlte s r l i) (IntSOlte t r l i)
IntSOlte {x} (Pvo s t) r l i = (p : x ** (IntSOlte s r l (fst i, Box p), IntSOlte t r l (Box p, snd i)))

data MuSOlte : (f : SO) -> (l : Rel p) -> (lu : (TopBot t, TopBot t)) -> Type where
  MkMuSOlte : IntSOlte f (MuSOlte f l) l lu -> MuSOlte f l lu

MuTree : Rel t -> Rel (TopBot t)
MuTree = MuSOlte SOTree

MuInterval : Rel t -> Rel (TopBot t)
MuInterval = MuSOlte SOInterval

treeLte : {lt : Rel pt} -> MuSOlte ft lt lu1 -> MuTree lt lu1
treeLte {lu1} {ft} {lt} {pt} (MkMuSOlte t) = go {lu=lu1} ft t 
  where
  go : {lu : (TopBot pt, TopBot pt)} -> (g : SO) -> (IntSOlte g) (MuSOlte ft lt) lt lu -> MuTree lt lu
  go       Ro        f           = treeLte f
  go       Uo        x           = MkMuSOlte $ Left x
  go      (Plo s _) (Left l)     = go s l
  go      (Plo _ t) (Right r)    = go t r
  go {lu} (Pvo s t) (p ** (l,r)) = MkMuSOlte $ Right (p ** ( go {lu = (fst lu, Box p)} s l
                                                           , go {lu = (Box p, snd lu)} t r))

interface DecRel (t : Type) (l : Rel t) | l where
  decRel : (x, y : t) -> Either (l (x,y)) (l (y,x))

insert : DecRel t l => MuInterval l i -> MuTree l i -> MuTree l i
insert           (MkMuSOlte (y ** (yl,yr))) (MkMuSOlte (Left _)) = MkMuSOlte $ Right (y ** (MkMuSOlte $ Left yl, MkMuSOlte $ Left yr))
insert @{dr} {i} (MkMuSOlte (y ** (yl,yr))) (MkMuSOlte (Right (p ** (pl,pr)))) with (decRel @{dr} y p)
  insert {i} (MkMuSOlte (y ** (yl,yr))) (MkMuSOlte (Right (p ** (lt,rt)))) | Left  le = 
    MkMuSOlte $ Right (p ** (insert {i=(fst i, Box p)} (MkMuSOlte (y ** (yl, le))) lt, rt))
  insert {i} (MkMuSOlte (y ** (yl,yr))) (MkMuSOlte (Right (p ** (lt,rt)))) | Right ge = 
    MkMuSOlte $ Right (p ** (lt, insert {i=(Box p, snd i)} (MkMuSOlte (y ** (ge, yr))) rt))

makeTree : DecRel t l => MuJJ f t -> MuTree l (Bot, Top)
makeTree = foldr (\p => insert (MkMuSOlte (p ** ((), ())))) (MkMuSOlte $ Left ())

MuList : Rel t -> Rel (TopBot t)
MuList = MuSOlte SOList

-- seems Idris doesn't have a problem with termination here, and splitting recursion actually gets us into trouble with implicit passing
merge : DecRel t l => MuList l i -> MuList l i -> MuList l i
merge (MkMuSOlte (Left _)) ys = ys
merge xs (MkMuSOlte (Left _)) = xs
merge @{dr} (MkMuSOlte (Right (x ** (lx, xs)))) (MkMuSOlte (Right (y ** (ly, ys)))) with (decRel @{dr} x y)
  merge (MkMuSOlte (Right (x ** (lx, xs)))) (MkMuSOlte (Right (y ** (ly, ys)))) | Left le = 
    MkMuSOlte $ Right (x ** (lx, merge xs (MkMuSOlte (Right (y ** (le, ys))))))
  merge (MkMuSOlte (Right (x ** (lx, xs)))) (MkMuSOlte (Right (y ** (ly, ys)))) | Right ge = 
    MkMuSOlte $ Right (y ** (ly, merge (MkMuSOlte (Right (x ** (ge, xs)))) ys))

DecRel t l => Semigroup (MuList l lu) where
  (<+>) = merge

interface BRelProv (l : Rel t) (lu : (TopBot t, TopBot t)) where
  provide : BRel l lu 

[olMon] (DecRel t l, BRelProv l lu) => Monoid (MuList l lu) where
  neutral {l} {lu} = MkMuSOlte $ Left $ provide {l} {lu}

BRelProv l (Bot, Top) where
  provide = ()

mergeJJ : DecRel p l => MuJJ f p -> MuList l (Bot, Top)  
mergeJJ = crush @{olMon} (\p => MkMuSOlte $ Right (p ** ((), MkMuSOlte $ Left ())))

QLTree : JJ
QLTree = (U `Pl` P) `Pl` (R `Ti` R)

twistIn : p -> MuJJ QLTree p -> MuJJ QLTree p
twistIn p (MkMuJJ (Left (Left ()))) = MkMuJJ $ Left $ Right p
twistIn p (MkMuJJ (Left (Right q))) = MkMuJJ $ Right (MkMuJJ $ Left $ Right p, MkMuJJ $ Left $ Right q)
twistIn p (MkMuJJ (Right (l, r))) = MkMuJJ $ Right (twistIn p r, l)

mergeSort : DecRel p l => MuJJ f p -> MuList l (Bot, Top)  
mergeSort = mergeJJ . foldr twistIn (MkMuJJ (Left (Left ())))

{-
-- NAIVE 

-- concat : MuList l (x,y) -> MuList l (y,z) -> MuList l (x,z)
-- concat (MkMuSOlte (Left   t))              ys = ?wat
-- concat (MkMuSOlte (Right (x ** (xl, xs)))) ys = MkMuSOlte (Right (x ** (xl, concat xs ys)))

sandwich : (MuList l /\. MuList l) i -> MuList l i
sandwich (p ** (MkMuSOlte (Left t), ys)) = MkMuSOlte (Right (p ** (t,ys)))
sandwich (p ** (MkMuSOlte (Right (x ** (xl, xs))), ys)) = MkMuSOlte (Right (x ** (xl, assert_total $ sandwich (p ** (xs, ys)))))

flatten : MuTree l i -> MuList l i
flatten (MkMuSOlte $ Left x) = MkMuSOlte $ Left x
flatten (MkMuSOlte $ Right (p ** (l, r))) = sandwich (p ** (flatten l, flatten r))

flattenSOlte : MuSOlte f l i -> MuList l i
flattenSOlte = flatten . treeLte
-}

{-
-- COMPLICATED 

flapp : {l : Rel p} -> (g : SO) -> (((IntSOlte g) (MuSOlte ft l) l) /\. MuList l) lu -> MuList l lu
flapp {ft}  Ro       (p ** (MkMuSOlte x,ys))     = assert_total $ flapp ft (p ** (x, ys))
flapp       Uo       (p ** (t, ys))              = MkMuSOlte (Right (p ** (t, ys)))
flapp      (Plo s _) (p ** (Left l, ys))         = flapp s (p ** (l, ys))
flapp      (Plo _ t) (p ** (Right r, ys))        = flapp t (p ** (r, ys))
flapp      (Pvo s t) (p ** ((p1 ** (l, r)), ys)) = flapp s (p1 ** (l, flapp t (p ** (r, ys))))

flatten : MuSOlte f l i -> MuList l i
flatten {f} (MkMuSOlte t) = go f t
  where
  go : (g : SO) -> (IntSOlte g) (MuSOlte ft l) l lu -> MuList l lu
  go  Ro        t            = flatten t
  go  Uo        t            = MkMuSOlte (Left t)
  go (Plo s _) (Left l)      = go s l
  go (Plo _ t) (Right r)     = go t r
  go (Pvo s t) (p ** (l, r)) = flapp s (p ** (l, go t r))
-}  

RepL : Rel p -> Rel (TopBot p)
RepL {p} l (n, u) = {m : TopBot p} -> BRel l (m,n) -> MuList l (m, u)

concat : MuList ll (l, n) -> RepL ll (n, u) -> MuList ll (l, u)
concat (MkMuSOlte (Left l)) ys = ys l
concat (MkMuSOlte (Right (x ** (l, xs)))) ys =  MkMuSOlte (Right (x ** (l, concat xs ys)))

flapp : MuSOlte f ll (l,n) -> RepL ll (n,u) -> MuList ll (l, u)
flapp t ys = go Ro t ys
  where
  go : (g : SO) -> (IntSOlte g) (MuSOlte ft ll) ll (l,n) -> RepL ll (n,u) -> MuList ll (l,u)
  go  Ro       (MkMuSOlte t) ys = go ft t ys
  go  Uo        z            ys = ys z
  go (Plo s _) (Left l)      ys = go s l ys
  go (Plo _ t) (Right r)     ys = go t r ys
  go (Pvo s t) (p ** (l, r)) ys = go s l (\z => MkMuSOlte $ Right (p ** (z, go t r ys)))

flatten : MuSOlte f ll (l, u) -> MuList ll (l, u)
flatten t = flapp t (MkMuSOlte . Left)