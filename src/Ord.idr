module Ord

%default total
%access public export

%hide Nat.LT
%hide Nat.GT

compareOp : Ordering -> Ordering
compareOp LT = GT
compareOp EQ = EQ
compareOp GT = LT

Uninhabited (LT = EQ) where
  uninhabited Refl impossible

Uninhabited (EQ = LT) where
  uninhabited Refl impossible

Uninhabited (LT = GT) where
  uninhabited Refl impossible

Uninhabited (GT = LT) where
  uninhabited Refl impossible

Uninhabited (GT = EQ) where
  uninhabited Refl impossible

Uninhabited (EQ = GT) where
  uninhabited Refl impossible

-- Nat reflection  

cmpOp : (a, b : Nat) -> compare a b = compareOp (compare b a)
cmpOp  Z     Z    = Refl
cmpOp  Z    (S _) = Refl
cmpOp (S _)  Z    = Refl
cmpOp (S a) (S b) = cmpOp a b 

cmpEq : (a, b : Nat) -> compare a b = EQ -> a = b
cmpEq  Z     Z    Refl = Refl
cmpEq  Z    (S _) prf  = absurd prf
cmpEq (S _)  Z    prf  = absurd prf
cmpEq (S a) (S b) prf  = cong $ cmpEq a b prf

cmpTotal : (a, b : Nat) -> Either (LTE (S a) b) (LTE b a)
cmpTotal  Z     Z    = Right LTEZero
cmpTotal  Z    (S _) = Left $ LTESucc LTEZero
cmpTotal (S _)  Z    = Right LTEZero
cmpTotal (S a) (S b) = case cmpTotal a b of 
  Left l => Left $ LTESucc l
  Right r => Right $ LTESucc r

cmpLt : (a, b : Nat) -> compare a b = LT -> LTE (S a) b
cmpLt  Z     Z    prf  = absurd prf
cmpLt  Z    (S _) Refl = LTESucc LTEZero
cmpLt (S _)  Z    prf  = absurd prf
cmpLt (S a) (S b) prf  = LTESucc $ cmpLt a b prf

ltCmp : (a, b : Nat) -> LTE (S a) b -> compare a b = LT
ltCmp  Z     Z    prf               = absurd prf
ltCmp  Z    (S _) (LTESucc LTEZero) = Refl
ltCmp (S _)  Z    prf               = absurd prf
ltCmp (S a) (S b) (LTESucc prf)     = ltCmp a b prf
