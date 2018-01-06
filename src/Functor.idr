module Functor

%default total
%access public export

data Id a = MkId a

-- product functor
data ProdF : (f : a -> b) -> (g : a -> b) -> (x : a) -> Type where
  MkProdF : f a -> g a -> ProdF f g a
  
-- functor composition
data CompF : (f : b -> c) -> (g : a -> b) -> (x : a) -> Type where
  MkCompF : f (g a) -> CompF f g a

-- sum functor
data SumF : (f : a -> b) -> (g : a -> b) -> (x : a) -> Type where
  InL : f a -> SumF f g a
  InR : g a -> SumF f g a

-- rightfolded composition

data CompRF : (f : Type -> Type) -> Nat -> (Type -> Type) where
  CRFZ : a -> CompRF f Z a
  CRFS : CompF f (CompRF f n) a -> CompRF f (S n) a

Functor f => Functor (CompRF f n) where
  map h (CRFZ a) = CRFZ (h a)
  map h (CRFS (MkCompF fa)) = CRFS (MkCompF $ map (map h) fa)

Applicative f => Applicative (CompRF f n) where
  pure {n=Z}   a = CRFZ a
  pure {n=S k} a = CRFS (MkCompF $ pure (pure a))
  (<*>) (CRFZ f)  (CRFZ x)  = CRFZ (f x)
  (<*>) (CRFS (MkCompF fs)) (CRFS (MkCompF xs)) = CRFS (MkCompF $ liftA2 (<*>) fs xs)

-- leftfolded composition

data CompLF : (f : Type -> Type) -> Nat -> (Type -> Type) where
  CLFZ : a -> CompLF f Z a
  CLFS : CompLF f n (f a) -> CompLF f (S n) a

Functor f => Functor (CompLF f n) where
  map h (CLFZ a) = CLFZ (h a)
  map h (CLFS r) = CLFS (map (map h) r)

Applicative f => Applicative (CompLF f n) where
  pure {n=Z}   a = CLFZ a
  pure {n=S k} a = CLFS (pure (pure a))
  (<*>) (CLFZ f)  (CLFZ x)  = CLFZ (f x)
  (<*>) (CLFS fs) (CLFS xs) = CLFS (liftA2 (<*>) fs xs)
