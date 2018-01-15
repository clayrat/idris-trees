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

cmpLemma : (a, b : Nat) -> compare a b = compareOp (compare b a)
cmpLemma  Z     Z    = Refl
cmpLemma  Z    (S _) = Refl
cmpLemma (S _)  Z    = Refl
cmpLemma (S a) (S b) = cmpLemma a b 

cmpEqLemma : (a, b : Nat) -> compare a b = EQ -> a = b
cmpEqLemma  Z     Z    Refl = Refl
cmpEqLemma  Z    (S _) prf = absurd prf
cmpEqLemma (S _)  Z    prf = absurd prf
cmpEqLemma (S a) (S b) prf = cong $ cmpEqLemma a b prf

cmpLtLemma : (a, b : Nat) -> compare a b = LT -> LTE (S a) b
cmpLtLemma   Z     Z    prf = absurd prf
cmpLtLemma   Z    (S _) Refl = LTESucc LTEZero
cmpLtLemma  (S _)  Z    prf = absurd prf
cmpLtLemma  (S a) (S b) prf = LTESucc $ cmpLtLemma a b prf