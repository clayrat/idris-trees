module Omega.Basic

%default total

data Shape : Type where
  Tp : Shape    
  Nd : Shape    
  Fk : Shape -> Shape -> Shape

data Path : Shape -> Type -> Type where
  None : Path Tp a  
  Here : a -> Path Nd a
  Left : Path x a -> Path (Fk x y) a  
  Right : Path y a -> Path (Fk x y) a  

data Tree : Shape -> Type -> Type where
  Tip : Tree Tp a  
  Node : a -> Tree Nd a  
  Fork : Tree x a -> Tree y a -> Tree (Fk x y) a   
  
find : (a -> a -> Bool) -> a -> Tree sh a -> List (Path sh a)
find  _ _  Tip = []
find eq n (Node m) = if eq n m then [Here n] else []
find eq n (Fork x y) = map Left (find eq n x) ++ map Right (find eq n y)