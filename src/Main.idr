module Main

import TrieMap

Semigroup () where
  (<+>) _ _ = ()

Monoid () where
  neutral = ()

insertPaths : Ord a => List (List a, b) -> TrieMap a (List b) -> TrieMap a (List b)
insertPaths = flip $ foldr (\(ks,v) => insertWith ks (maybe [v] (v::))) 

test : List (List String, String)
test = 
  [ ( [ "Basic" ] , "Category")
  , ( [ "Basic" ] , "Functor")
  , ( [ "Basic" ], "Isomorphism")
  , ( [ "Basic" ], "NaturalTransformation")
  , ( [ "Basic" , "Isomorphism"] , "Natural")
  , ( [ "Discrete" ], "DiscreteCategory")
  , ( [ "Discrete" ], "FunctionAsFunctor")
  , ( [ "Idris" ], "TypesAsCategory")
  ]

walkPaths : TrieMap String (List String) -> IO ()
walkPaths = foldWithKeysM 
               (printLn . concat . intersperse "/") 
               (\ks => map concat . traverse (\v => printLn $ concat $ intersperse "/" (ks++[v])))

main : IO ()
main = walkPaths $ insertPaths test empty
