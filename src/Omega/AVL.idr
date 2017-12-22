module Omega.AVL

%default total

mutual 
  data Avl : Nat -> Type where
    Leaf : Avl Z
    Node : Balance hL hR hMax -> Avl hL -> Int -> Avl hR -> Avl (S hMax)

  data Balance : (hL : Nat) -> (hR : Nat) -> (hMax : Nat) -> Type where
    Less : Balance    h (S h) (S h)
    Same : Balance    h    h     h
    More : Balance (S h)   h  (S h)

data AVL = MkAVL (Avl h)    

empty : AVL
empty = MkAVL Leaf

elem : Int -> Avl h -> Bool
elem _ Leaf = False
elem x (Node _ l y r) with (compare x y)
  | LT = elem x l
  | EQ = True
  | GT = elem x r

element : Int -> AVL -> Bool
element x (MkAVL t) = elem x t

rotr : Avl (2+n) -> Int -> Avl n -> Either (Avl (2+n)) (Avl (3+n))
rotr Leaf _ _ impossible
rotr (Node Less _ _ Leaf ) _ _ impossible
-- single rotations
rotr (Node Same a x b) y c = Right (Node Less a x (Node More b y c))
rotr (Node More a x b) y c = Left (Node Same a x (Node Same b y c))
-- double rotations
rotr (Node Less a x (Node Same b y c)) z d = Left (Node Same (Node Same a x b) y (Node Same c z d))
rotr (Node Less a x (Node Less b y c)) z d = Left (Node Same (Node More a x b) y (Node Same c z d))
rotr (Node Less a x (Node More b y c)) z d = Left (Node Same (Node Same a x b) y (Node Less c z d))

rotl : Avl n -> Int -> Avl (2+n) -> Either (Avl (2+n)) (Avl (3+n))
rotl _ _ Leaf impossible
rotl _ _ (Node More Leaf _ _) impossible
-- single rotations
rotl a u (Node Same b v c) = Right (Node More (Node Less a u b) v c)
rotl a u (Node Less b v c) = Left (Node Same (Node Same a u b) v c)
-- double rotations
rotl a u (Node More (Node Same x m y) v c)= Left (Node Same (Node Same a u x) m (Node Same y v c))
rotl a u (Node More (Node Less x m y) v c)= Left (Node Same (Node More a u x) m (Node Same y v c))
rotl a u (Node More (Node More x m y) v c)= Left (Node Same (Node Same a u x) m (Node Less y v c))

ins : Int -> Avl n -> Either (Avl n) (Avl (S n))
ins x Leaf = Right (Node Same Leaf x Leaf)
ins x (Node bal a y b) with (compare x y) 
  | LT = case ins x a of 
           Left la => Left (Node bal la y b)
           Right ra => case bal of 
                         Less => Left (Node Same ra y b)
                         Same => Right (Node More ra y b)
                         More => rotr ra y b -- rebalance
  | EQ = Left (Node bal a y b)
  | GT = case ins x b of 
           Left lb => Left (Node bal a y lb)
           Right rb => case bal of 
                         Less => rotl a y rb -- rebalance
                         Same => Right (Node Less a y rb)
                         More => Left (Node Same a y rb)
insert : Int -> AVL -> AVL
insert x (MkAVL t) = either MkAVL MkAVL $ ins x t
   
delMin : Avl (S n) -> (Int, Either (Avl n) (Avl (S n)))
delMin Leaf impossible
delMin (Node Less Leaf x r) = (x, Left r)
delMin (Node Same Leaf x r) = (x, Left r)
delMin (Node More Leaf x r) impossible
delMin (Node bal l@(Node _ _ _ _) x r) = 
  case delMin l of 
    (y, Right lr) => (y, Right (Node bal lr x r))
    (y, Left ll) => 
      case bal of 
        Same => (y, Right (Node Less ll x r))
        More => (y, Left (Node Same ll x r))
        Less => (y, rotl ll x r) -- rebalance
        
del : Int -> Avl n -> Either (Avl n) (m ** (S m = n, Avl m))
del _ Leaf = Left Leaf
del y (Node {hL} {hR} bal l x r) with (compare y x)
  | LT = case del y l of 
           Left ll => Left (Node bal l x r)
           Right (m**(prf,lr)) => 
             case bal of 
                Same => Left (Node (rewrite sym prf in Less) lr x (rewrite prf in r))
                More => Right (S m ** (cong prf, Node Same lr x (rewrite succInjective m hR prf in r))) 
                Less => 
                  case rotl lr x (rewrite prf in r) of --rebalance
                    Left tl => Right (S (S m) ** (cong {f = S . S} prf, tl)) 
                    Right tr => Left (rewrite sym prf in tr)
  | EQ = case r of 
           Leaf => 
             case bal of 
               Same => Right (0 ** (Refl, l))
               More => Right (1 ** (Refl, l))
               Less impossible
           Node _ _ _ _ =>
             case (bal, delMin r) of
               (_, z, Right rr) => Left (Node bal l z rr)
               (Same, z, Left rl) => Left (Node More l z rl)
               (Less {h}, z, Left rl) => Right (S h ** (Refl, Node Same l z rl))
               (More {h=S h}, z, Left rl) => 
                 case rotr l z rl of --rebalance
                   Left tl => Right (S (S h) ** (Refl, tl))
                   Right tr => Left tr
  | GT = case del y r of 
           Left rl => Left (Node bal l x rl)
           Right (m**(prf,rr)) => 
             case bal of 
                Same => Left (Node (rewrite sym prf in More) (rewrite prf in l) x rr)
                Less => Right (S m ** (cong prf, Node Same (rewrite succInjective m hL prf in l) x rr))
                More => 
                  case rotr {n=m} (rewrite prf in l) x rr of --(rewrite prf in l) x rr of --rebalance
                    Left tl => Right (S (S m) ** (cong {f = S . S} prf, tl)) 
                    Right tr => Left (rewrite sym prf in tr)

delete : Int -> AVL -> AVL
delete x (MkAVL t) = 
  case del x t of 
    Left tl => MkAVL tl
    Right (_ ** (_,tr)) => MkAVL tr
                    