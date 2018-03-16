module Agda.Pivotal.IOU

import Agda.Pivotal.JJ

%default total

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

MuIOList : Rel t -> Rel (TopBot t)
MuIOList l = MuIOlte IOList l ()

MuIOTree : Rel t -> Rel (TopBot t)
MuIOTree l = MuIOlte IOTree l ()

MuIOInterval : Rel t -> Rel (TopBot t)
MuIOInterval l = MuIOlte IOInterval l ()

IOVec : Nat -> IOU Nat
IOVec Z = I
IOVec (S n) = I `Pv` R n

IOEven : Nat -> IOU Nat
IOEven  Z        = I
IOEven (S  Z)    = O
IOEven (S (S n)) = I `Pv` (I `Pv` R n)

treeIO : {rt : Rel t} -> {j : i} -> MuIOlte f rt j lu1 -> MuIOTree rt lu1
treeIO {f} {rt} {i} {j} {t} (MkMuIOlte tr) = go {lu=lu1} (f j) tr 
  where     
  go : {lu : (TopBot t, TopBot t)} -> (g : IOU i) -> IntIOlte g (MuIOlte f rt) rt lu -> MuIOTree rt lu
  go (R _)     br           = treeIO br                    
  go  O        br           = absurd br
  go  I        br           = MkMuIOlte $ Left br
  go (Pl s _) (Left l)      = go s l
  go (Pl _ t) (Right r)     = go t r
  go (Pv s t) (p ** (l, r)) = MkMuIOlte $ Right (p ** (go s l, go t r))

RepLIO : Rel p -> Rel (TopBot p)
RepLIO {p} l (n,u) = {m : TopBot p} -> BRel l (m,n) -> MuIOList l (m,u)  

flattenIO : {rt : Rel t} -> {j : i} -> MuIOlte f rt j (l,u) -> MuIOList rt (l,u)
flattenIO {f} (MkMuIOlte tr) = go (f j) tr (MkMuIOlte . Left)
  where
  go : (g : IOU i) -> IntIOlte g (MuIOlte f rt) rt (l,n) -> RepLIO rt (n,u) -> MuIOList rt (l,u)
  go (R i)     (MkMuIOlte t) ys = go (f i) t ys             
  go  O         br           _  = absurd br
  go  I         br           ys = ys br
  go (Pl s _)  (Left l)      ys = go s l ys                 
  go (Pl _ t)  (Right r)     ys = go t r ys                 
  go (Pv s t)  (p ** (l, r)) ys = go s l (\z => MkMuIOlte $ Right (p ** (z, go t r ys)))

-- 2-3 trees

IOTree23 : Nat -> IOU Nat
IOTree23 Z = I
IOTree23 (S h) = R h `Pv` (R h `Pl` (R h `Pv` R h))

Mu23 : Rel t -> Nat -> Rel (TopBot t)
Mu23 l = MuIOlte IOTree23 l

ins23 : DecRel t l => (h : Nat) -> MuIOInterval l lu -> Mu23 l h lu -> Either (Mu23 l h lu) (p ** (Mu23 l h (fst lu, Box p), Mu23 l h (Box p, snd lu)))
ins23        Z    (MkMuIOlte (y ** (l, r))) _ = Right (y ** (MkMuIOlte l, MkMuIOlte r))
ins23 @{dr} (S k) (MkMuIOlte (y ** (l, r))) (MkMuIOlte (p ** (lt, rest))) with (decRel @{dr} y p)
  ins23 (S k) (MkMuIOlte (y ** (l, r))) (MkMuIOlte (p ** (lt, rest))) | Left le with (ins23 k (MkMuIOlte (y ** (l, le))) lt)
    ins23 (S k) (MkMuIOlte (y ** (l, r))) (MkMuIOlte (p ** (lt, rest)))                  | Left le | Left lt1                 = 
      Left $ MkMuIOlte (p ** (lt1, rest))
    ins23 (S k) (MkMuIOlte (y ** (l, r))) (MkMuIOlte (p ** (lt, Left rt)))               | Left le | Right (r0 ** (llt, lrt)) = 
      Left $ MkMuIOlte (r0 ** (llt, Right (p ** (lrt, rt))))
    ins23 (S k) (MkMuIOlte (y ** (l, r))) (MkMuIOlte (p ** (lt, Right (q ** (mt, rt))))) | Left le | Right (r0 ** (llt, lrt)) = 
      Right (p ** (MkMuIOlte (r0 ** (llt, Left lrt)), MkMuIOlte (q ** (mt, Left rt))))
  ins23 (S k) (MkMuIOlte (y ** (l, r))) (MkMuIOlte (p ** (lt, Left rt))) | Right ge with (ins23 k (MkMuIOlte (y ** (ge, r))) rt)
    ins23 (S k) (MkMuIOlte (y ** (l, r))) (MkMuIOlte (p ** (lt, Left rt))) | Right ge | rt0 = Left $ MkMuIOlte (p ** (lt, rt0))
  ins23 @{dr} (S k) (MkMuIOlte (y ** (l, r))) (MkMuIOlte (p ** (lt, Right (q ** (mt, rt))))) | Right ge with (decRel @{dr} y q)
    ins23 (S k) (MkMuIOlte (y ** (l, r))) (MkMuIOlte (p ** (lt, Right (q ** (mt, rt))))) | Right ge | Left le1 with (ins23 k (MkMuIOlte (y ** (ge, le1))) mt)
      ins23 (S k) (MkMuIOlte (y ** (l, r))) (MkMuIOlte (p ** (lt, Right (q ** (mt, rt))))) | Right ge | Left le1 | Left mt1 = 
        Left $ MkMuIOlte (p ** (lt, Right (q ** (mt1, rt))))
      ins23 (S k) (MkMuIOlte (y ** (l, r))) (MkMuIOlte (p ** (lt, Right (q ** (mt, rt))))) | Right ge | Left le1 | Right (r1 ** (mlt, mrt)) = 
        Right (r1 ** (MkMuIOlte (p ** (lt, Left mlt)), MkMuIOlte (q ** (mrt, Left rt))))
    ins23 (S k) (MkMuIOlte (y ** (l, r))) (MkMuIOlte (p ** (lt, Right (q ** (mt, rt))))) | Right ge | Right ge1 with (ins23 k (MkMuIOlte (y ** (ge1, r))) rt)
      ins23 (S k) (MkMuIOlte (y ** (l, r))) (MkMuIOlte (p ** (lt, Right (q ** (mt, rt))))) | Right ge | Right ge1 | Left rt1 = 
        Left $ MkMuIOlte (p ** (lt, Right (q ** (mt, rt1))))
      ins23 (S k) (MkMuIOlte (y ** (l, r))) (MkMuIOlte (p ** (lt, Right (q ** (mt, rt))))) | Right ge | Right ge1 | Right (r0 ** (rlt, rrt)) =
        Right (q ** (MkMuIOlte (p ** (lt, Left mt)), MkMuIOlte (r0 ** (rlt, Left rrt))))

Tree23 : {t : Type} -> Rel t -> Type 
Tree23 l = (h ** Mu23 l h (Bot, Top))

insert23 : DecRel t l => (p : t) -> Tree23 l -> Tree23 l
insert23 p (h ** tr) with (ins23 h (MkMuIOlte (p ** ((), ()))) tr) 
  insert23 p (h ** tr) | Left tr1              = (h ** tr1)
  insert23 p (h ** tr) | Right (r ** (lt, rt)) = (S h ** MkMuIOlte (r ** (lt, Left rt)))

sort : DecRel p l => MuJJ f p -> MuIOList l (Bot, Top)
sort mu = flattenIO $ snd $ JJ.foldr insert23 (Z ** MkMuIOlte ()) mu

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

Short23 : Nat -> Rel (TopBot p)
Short23      Z    _  = Void
Short23 {p} (S k) lu = {l : Rel p} -> Mu23 l k lu

Del23 : Nat -> Rel (TopBot p)
Del23 {p} h lu = Either (Short23 h lu) ({l : Rel p} -> Mu23 l h lu)
