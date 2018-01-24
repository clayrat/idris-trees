module Agda.Pivotal.JJ

import Data.So

%default total

data JJ : Type where
  R : JJ               -- recursive substructure
  P : JJ               -- parameter
  U : JJ               -- 1
  Pl : JJ -> JJ -> JJ
  Ti : JJ -> JJ -> JJ

Interp : JJ -> Type -> Type -> Type
Interp R A _ = A
Interp P _ B = B
Interp U _ _ = ()
Interp (Pl S T) A B = Either (Interp S A B) (Interp T A B)
Interp (Ti S T) A B = (Interp S A B, Interp T A B)

data MuJJ : (f : JJ) -> (p : Type) -> Type where
  MkMuJJ : Interp f (MuJJ f p) p -> MuJJ f p 

traverse : Applicative h => (a -> h b) -> MuJJ f a -> h (MuJJ f b)
traverse {h} ahb t = go R t 
  where
  go : (g : JJ) -> Interp g (MuJJ f a) a -> h (Interp g (MuJJ f b) b)
  go R (MkMuJJ t) = pure MkMuJJ <*> go f t
  go P x = ahb x
  go U () = pure ()
  go (Pl S _) (Left s) = pure Left <*> go S s
  go (Pl _ T) (Right t) = pure Right <*> go T t
  go (Ti S T) (s,t) = pure MkPair <*> go S s <*> go T t

[idFun] Functor (\x => x) where
  map = id

using implementation idFun
  [idApp] Applicative (\x => x) where
    pure = id
    (<*>) = id
