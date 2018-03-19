module Agda.Pivotal.IOU

import Agda.Pivotal.JJ

%default total

data IOU : Type -> Type where
  R : i -> IOU i
  O : IOU i
  I : IOU i
  Pl : IOU i -> IOU i -> IOU i
  Pv : IOU i -> IOU i -> IOU i

IntIOL : IOU i -> (i -> Rel (TopBot p)) -> Rel p -> Rel (TopBot p)
IntIOL (R i)    r _ = r i
IntIOL  O       _ _ = \_ => Void
IntIOL  I       _ l = BRel l
IntIOL (Pl s t) r l = IntIOL s r l +. IntIOL t r l
IntIOL (Pv s t) r l = IntIOL s r l /\. IntIOL t r l

data MuIOL : (f : i -> IOU i) -> (l : Rel p) -> (j : i) -> (lu : (TopBot t, TopBot t)) -> Type where
  MkMuIOL : IntIOL (f j) (MuIOL f l) l lu -> MuIOL f l j lu

IOList : () -> IOU ()
IOList () = I `Pl` (I `Pv` R ())

IOTree : () -> IOU ()
IOTree () = I `Pl` (R () `Pv` R ())

IOInterval : () -> IOU ()
IOInterval () = I `Pv` I

MuIOList : Rel t -> Rel (TopBot t)
MuIOList l = MuIOL IOList l ()

MuIOTree : Rel t -> Rel (TopBot t)
MuIOTree l = MuIOL IOTree l ()

MuIOInterval : Rel t -> Rel (TopBot t)
MuIOInterval l = MuIOL IOInterval l ()

IOVec : Nat -> IOU Nat
IOVec Z = I
IOVec (S n) = I `Pv` R n

IOEven : Nat -> IOU Nat
IOEven  Z        = I
IOEven (S  Z)    = O
IOEven (S (S n)) = I `Pv` (I `Pv` R n)

treeIO : {rt : Rel t} -> {j : i} -> MuIOL f rt j lu1 -> MuIOTree rt lu1
treeIO {f} {rt} {i} {j} {t} (MkMuIOL tr) = go {lu=lu1} (f j) tr 
  where     
  go : {lu : (TopBot t, TopBot t)} -> (g : IOU i) -> IntIOL g (MuIOL f rt) rt lu -> MuIOTree rt lu
  go (R _)     br           = treeIO br                    
  go  O        br           = absurd br
  go  I        br           = MkMuIOL $ Left br
  go (Pl s _) (Left l)      = go s l
  go (Pl _ t) (Right r)     = go t r
  go (Pv s t) (p ** (l, r)) = MkMuIOL $ Right (p ** (go s l, go t r))

RepLIO : Rel p -> Rel (TopBot p)
RepLIO {p} l (n,u) = {m : TopBot p} -> BRel l (m,n) -> MuIOList l (m,u)  

flattenIO : {rt : Rel t} -> {j : i} -> MuIOL f rt j (l,u) -> MuIOList rt (l,u)
flattenIO {f} (MkMuIOL tr) = go (f j) tr (MkMuIOL . Left)
  where
  go : (g : IOU i) -> IntIOL g (MuIOL f rt) rt (l,n) -> RepLIO rt (n,u) -> MuIOList rt (l,u)
  go (R i)     (MkMuIOL t) ys = go (f i) t ys             
  go  O         br           _  = absurd br
  go  I         br           ys = ys br
  go (Pl s _)  (Left l)      ys = go s l ys                 
  go (Pl _ t)  (Right r)     ys = go t r ys                 
  go (Pv s t)  (p ** (l, r)) ys = go s l (\z => MkMuIOL $ Right (p ** (z, go t r ys)))

-- 2-3 trees

IOTree23 : Nat -> IOU Nat
IOTree23 Z = I
IOTree23 (S h) = R h `Pv` (R h `Pl` (R h `Pv` R h))

Mu23 : Rel t -> Nat -> Rel (TopBot t)
Mu23 l = MuIOL IOTree23 l

ins23 : DecRel t l => (h : Nat) -> MuIOInterval l lu -> Mu23 l h lu -> Either (Mu23 l h lu) (p ** (Mu23 l h (fst lu, Box p), Mu23 l h (Box p, snd lu)))
ins23        Z    (MkMuIOL (y ** (l, r))) _ = Right (y ** (MkMuIOL l, MkMuIOL r))
ins23 @{dr} (S k) (MkMuIOL (y ** (l, r))) (MkMuIOL (p ** (lt, rest))) with (decRel @{dr} y p)
  ins23 (S k) (MkMuIOL (y ** (l, r))) (MkMuIOL (p ** (lt, rest))) | Left le with (ins23 k (MkMuIOL (y ** (l, le))) lt)
    ins23 (S k) (MkMuIOL (y ** (l, r))) (MkMuIOL (p ** (lt, rest)))                  | Left le | Left lt1                 = 
      Left $ MkMuIOL (p ** (lt1, rest))
    ins23 (S k) (MkMuIOL (y ** (l, r))) (MkMuIOL (p ** (lt, Left rt)))               | Left le | Right (r0 ** (llt, lrt)) = 
      Left $ MkMuIOL (r0 ** (llt, Right (p ** (lrt, rt))))
    ins23 (S k) (MkMuIOL (y ** (l, r))) (MkMuIOL (p ** (lt, Right (q ** (mt, rt))))) | Left le | Right (r0 ** (llt, lrt)) = 
      Right (p ** (MkMuIOL (r0 ** (llt, Left lrt)), MkMuIOL (q ** (mt, Left rt))))
  ins23 (S k) (MkMuIOL (y ** (l, r))) (MkMuIOL (p ** (lt, Left rt))) | Right ge with (ins23 k (MkMuIOL (y ** (ge, r))) rt)
    ins23 (S k) (MkMuIOL (y ** (l, r))) (MkMuIOL (p ** (lt, Left rt))) | Right ge | rt0 = Left $ MkMuIOL (p ** (lt, rt0))
  ins23 @{dr} (S k) (MkMuIOL (y ** (l, r))) (MkMuIOL (p ** (lt, Right (q ** (mt, rt))))) | Right ge with (decRel @{dr} y q)
    ins23 (S k) (MkMuIOL (y ** (l, r))) (MkMuIOL (p ** (lt, Right (q ** (mt, rt))))) | Right ge | Left le1 with (ins23 k (MkMuIOL (y ** (ge, le1))) mt)
      ins23 (S k) (MkMuIOL (y ** (l, r))) (MkMuIOL (p ** (lt, Right (q ** (mt, rt))))) | Right ge | Left le1 | Left mt1 = 
        Left $ MkMuIOL (p ** (lt, Right (q ** (mt1, rt))))
      ins23 (S k) (MkMuIOL (y ** (l, r))) (MkMuIOL (p ** (lt, Right (q ** (mt, rt))))) | Right ge | Left le1 | Right (r1 ** (mlt, mrt)) = 
        Right (r1 ** (MkMuIOL (p ** (lt, Left mlt)), MkMuIOL (q ** (mrt, Left rt))))
    ins23 (S k) (MkMuIOL (y ** (l, r))) (MkMuIOL (p ** (lt, Right (q ** (mt, rt))))) | Right ge | Right ge1 with (ins23 k (MkMuIOL (y ** (ge1, r))) rt)
      ins23 (S k) (MkMuIOL (y ** (l, r))) (MkMuIOL (p ** (lt, Right (q ** (mt, rt))))) | Right ge | Right ge1 | Left rt1 = 
        Left $ MkMuIOL (p ** (lt, Right (q ** (mt, rt1))))
      ins23 (S k) (MkMuIOL (y ** (l, r))) (MkMuIOL (p ** (lt, Right (q ** (mt, rt))))) | Right ge | Right ge1 | Right (r0 ** (rlt, rrt)) =
        Right (q ** (MkMuIOL (p ** (lt, Left mt)), MkMuIOL (r0 ** (rlt, Left rrt))))

Tree23 : {t : Type} -> Rel t -> Type 
Tree23 l = (h ** Mu23 l h (Bot, Top))

insert23 : DecRel t l => (p : t) -> Tree23 l -> Tree23 l
insert23 p (h ** tr) with (ins23 h (MkMuIOL (p ** ((), ()))) tr) 
  insert23 p (h ** tr) | Left tr1              = (h ** tr1)
  insert23 p (h ** tr) | Right (r ** (lt, rt)) = (S h ** MkMuIOL (r ** (lt, Left rt)))

sort : DecRel t l => MuJJ f t -> MuIOList l (Bot, Top)
sort mu = flattenIO $ snd $ JJ.foldr insert23 (Z ** MkMuIOL ()) mu

-- deletion

interface TransRel (t : Type) (l : Rel t) | l where
  transrel : {x, z : t} -> (y : t) -> l (x,y) -> l (y,z) -> l (x,z)

btrans : TransRel t l => (BRel l /\. BRel l) lu -> BRel l lu
btrans {lu=(_    , Top  )}  _           = ()
btrans {lu=(Bot  , Bot  )}  _           = ()
btrans {lu=(Bot  , Box _)}  _           = ()
btrans {lu=(Top  , _    )} (_ ** (s,_)) = absurd s
btrans {lu=(Box _, Box _)} (p ** (s,t)) = transrel p s t
btrans {lu=(Box _, Bot  )} (_ ** (_,t)) = absurd t

Short23 : {l : Rel p} -> Nat -> Rel (TopBot p)
Short23      Z    _  = Void
Short23 {l} (S k) lu = Mu23 l k lu

Del23 : {l : Rel p} -> Nat -> Rel (TopBot p)
Del23 {l} h lu = Either (Short23 {l} h lu) (Mu23 l h lu)

Re2 : {l : Rel p} -> Nat -> Rel (TopBot p)
Re2 {l} h = Short23 {l} (S h) +. (Mu23 l h /\. Mu23 l h)

d2t : {h : Nat} -> {l : Rel p} -> (Del23 {l} h /\. Mu23 l h) lu -> Re2 {l} h lu
d2t {h}     (p ** (Right lp, pu))                                        = 
  Right (p ** (lp, pu))
d2t {h=Z}   (p ** (Left v, pu))                                          = 
  absurd v
d2t {h=S k} (p ** (Left lp, MkMuIOL (q ** (pq, Left qu))))               = 
  Left $ MkMuIOL (p ** (lp, Right (q ** (pq, qu))))
d2t {h=S k} (p ** (Left lp, MkMuIOL (q ** (pq, Right (r ** (qr, ru)))))) = 
  Right (q ** (MkMuIOL (p ** (lp, Left pq)), MkMuIOL (r ** (qr, Left ru))))

t2d : {h : Nat} -> {l : Rel p} -> (Mu23 l h /\. Del23 {l} h) lu -> Re2 {l} h lu
t2d {h}     (p ** (lp, Right pu))                                        = 
  Right (p ** (lp, pu))
t2d {h=Z}   (p ** (lp, Left v))                                          = 
  absurd v
t2d {h=S k} (p ** (MkMuIOL (n ** (ln, Left np)), Left pu))               = 
  Left $ MkMuIOL (n ** (ln, Right (p ** (np, pu))))
t2d {h=S k} (p ** (MkMuIOL (m ** (lm, Right (n ** (mn, np)))), Left pu)) = 
  Right (n ** (MkMuIOL (m ** (lm, Left mn)), MkMuIOL (p ** (np, Left pu))))

rd : {h : Nat} -> {l : Rel p} -> Re2 {l} h lu -> Del23 {l} (S h) lu
rd (Left s)                = Left s
rd (Right (p ** (lp, pu))) = Right $ MkMuIOL (p ** (lp, Left pu))

r3t : {h : Nat} -> {l : Rel p} -> (Re2 {l} h /\. Mu23 l h) lu -> Del23 {l} (S h) lu
r3t (p ** (Left   lp            , pu)) = Right $ MkMuIOL (p ** (lp, Left pu))
r3t (p ** (Right (m ** (lm, mp)), pu)) = Right $ MkMuIOL (m ** (lm, Right (p ** (mp, pu))))

t3r : {h : Nat} -> {l : Rel p} -> (Mu23 l h /\. Re2 {l} h) lu -> Del23 {l} (S h) lu
t3r (p ** (lp, Left   pu            )) = Right $ MkMuIOL (p ** (lp, Left pu))
t3r (p ** (lp, Right (q ** (pq, qu)))) = Right $ MkMuIOL (p ** (lp, Right (q ** (pq, qu))))

extr : {h : Nat} -> {l : Rel t} -> Mu23 l (S h) lu -> (Del23 {l} (S h) /\. BRel l) lu
extr {h=Z}   (MkMuIOL (r ** (lr, Left $ MkMuIOL n0)))             = (r ** (Left lr, n0))
extr {h=Z}   (MkMuIOL (p ** (lp, Right (r ** (pr, MkMuIOL n0))))) = (r ** (Right $ MkMuIOL (p ** (lp, Left pr)), n0))
extr {h=S k} (MkMuIOL (p ** (lp, Left pu)))                       with (extr pu) 
  | (r ** (pr, nr)) = (r ** (rd (t2d (p ** (lp, pr))), nr))
extr {h=S k} (MkMuIOL (p ** (lp, Right (q ** (pq, qu)))))         with (extr qu) 
  | (r ** (qr, nr)) = (r ** (t3r (p ** (lp, t2d (q ** (pq, qr)))), nr))

delp : TransRel t l => {h : Nat} -> (Mu23 l h /\. Mu23 l h) lu -> Re2 {l} h lu 
delp @{tr} {lu} {h=Z}   (p ** (MkMuIOL n0, MkMuIOL n1)) = 
  Left $ MkMuIOL $ btrans @{tr} {lu} (p ** (n0, n1))
delp @{tr} {t} {h=S k} (p ** (lp, pu)) with (extr lp)
  delp @{tr} {t} {h=S k} (p ** (lp, pu)) | (r ** (lr, nr)) = d2t (r ** (lr, weak pu))
  where 
    weak : {u : TopBot t} -> Mu23 l h (Box p, u) -> Mu23 l h (Box r, u)
    weak {h=Z} {u} (MkMuIOL n0)              = MkMuIOL $ btrans @{tr} {lu = (Box r, u)} (p ** (nr, n0))
    weak {h=S k}   (MkMuIOL (q ** (pq, qu))) = MkMuIOL $ (q ** (weak pq, qu))

del23 : (DecEq t, TransRel t l, DecRel t l) => {h : Nat} -> MuIOInterval l lu -> Mu23 l h lu -> Del23 {l} h lu
del23 {h=Z}   _ n0 = Right n0
del23 @{de} @{tr} @{dr} {h=S k} (MkMuIOL (y ** (l,r))) (MkMuIOL (p ** (lp, pu))) with (decEq y p)
  del23 @{de} @{tr} @{dr} {h=S k} (MkMuIOL (y ** (l,r))) (MkMuIOL (y ** (lp, Left pu)))               | Yes Refl = 
    rd (delp @{tr} (y ** (lp, pu)))
  del23 @{de} @{tr} @{dr} {h=S k} (MkMuIOL (y ** (l,r))) (MkMuIOL (y ** (lp, Right (q ** (pq, qu))))) | Yes Refl = 
    r3t (q ** (delp @{tr} (y ** (lp, pq)), qu))
  del23 @{de} @{tr} @{dr} {h=S k} (MkMuIOL (y ** (l,r))) (MkMuIOL (p ** (lp, pu))) | No _ with (decRel @{dr} y p)
    del23 @{de} @{tr} @{dr} {h=S k} (MkMuIOL (y ** (l,r))) (MkMuIOL (p ** (lp, Left pu)))               | No _ | Left le = 
      rd (d2t (p ** (del23 (MkMuIOL (y ** (l, le))) lp, pu)))
    del23 @{de} @{tr} @{dr} {h=S k} (MkMuIOL (y ** (l,r))) (MkMuIOL (p ** (lp, Right (q ** (pq, qu))))) | No _ | Left le = 
      r3t (q ** (d2t (p ** (del23 (MkMuIOL (y ** (l, le))) lp, pq)), qu))
    del23 @{de} @{tr} @{dr} {h=S k} (MkMuIOL (y ** (l,r))) (MkMuIOL (p ** (lp, Left pu)))               | No _ | Right ge = 
      rd (t2d (p ** (lp, del23 (MkMuIOL (y ** (ge, r))) pu)))
    del23 @{de} @{tr} @{dr} {h=S k} (MkMuIOL (y ** (l,r))) (MkMuIOL (p ** (lp, Right (q ** (pq, qu))))) | No _ | Right ge with (decEq y q)
      del23 @{de} @{tr} @{dr} {h=S k} (MkMuIOL (y ** (l,r))) (MkMuIOL (p ** (lp, Right (y ** (pq, qu))))) | No _ | Right ge | Yes Refl = 
        t3r (p ** (lp, delp (y ** (pq, qu))))
      del23 @{de} @{tr} @{dr} {h=S k} (MkMuIOL (y ** (l,r))) (MkMuIOL (p ** (lp, Right (q ** (pq, qu))))) | No _ | Right ge | No _ with (decRel @{dr} y q)
        del23 @{de} @{tr} @{dr} {h=S k} (MkMuIOL (y ** (l,r))) (MkMuIOL (p ** (lp, Right (q ** (pq, qu))))) | No _ | Right ge | No _ | Left le1  = 
          r3t (q ** (t2d (p ** (lp, del23 (MkMuIOL (y ** (ge, le1))) pq)), qu))
        del23 @{de} @{tr} @{dr} {h=S k} (MkMuIOL (y ** (l,r))) (MkMuIOL (p ** (lp, Right (q ** (pq, qu))))) | No _ | Right ge | No _ | Right ge1 = 
          t3r (p ** (lp, t2d (q ** (pq, del23 (MkMuIOL (y ** (ge1, r))) qu))))