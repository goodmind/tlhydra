module TL.CodeGen.TypeScript

import List.Split
import Text.Casing
import TL.Types
import TL.Store.Store

%access public export

interface TSNamed a where
  toTypeName : a -> String

interface TSNamed a => TSInterface a where
  toTypeDecl : a -> String

interface TSNamed a => TSUnion a where
  toUnionDecl : a -> String -> String

TSNamed (List a) where
  toTypeName _ = "List"

TSNamed a => TSUnion (List a) where
  toUnionDecl xs name = "type " ++ name ++ " = " ++ (union' "" xs) ++ ";\n" where
    union' acc []        = acc
    union' acc [x]       = acc ++ (toTypeName x)
    union' acc (x :: xs) = union' (acc ++ (toTypeName x) ++ "\n | ") xs

toIdent : String -> String -> String
toIdent name prefix = prefix ++ (pascal . replace' "." "_") name

TSNamed TLType where
  toTypeName (MkTLType name _) = toIdent name "T"
  toTypeName (MkTLTypeBuiltin x) = show x

TSInterface TLType where
  toTypeDecl t = case t of
    MkTLType name _ => """
interface """ ++ toTypeName t ++ """ {
  _: '""" ++ name ++ """';
  // """ ++ show t ++ """
}
"""
    MkTLTypeBuiltin => """
interface """ ++ toTypeName t ++ """ {}
"""

TSNamed TLSConstructor where
  toTypeName (MkTLSConstructor identifier _ _ _ _) = toIdent identifier "C"

TSInterface TLSConstructor where
  toTypeDecl t = let (MkTLSConstructor identifier _ _ _ _) = t in """
interface """ ++ toTypeName t ++ """ {
  _: '""" ++ identifier ++ """';
  // """ ++ show t ++ """
}
"""

TSNamed TLSFunction where
  toTypeName (MkTLSFunction identifier _ _ _) = toIdent identifier "F"

TSInterface TLSFunction where
  toTypeDecl t = let (MkTLSFunction identifier _ _ _) = t in """
interface """ ++ toTypeName t ++ """ {
  _: '""" ++ identifier ++ """';
  // """ ++ show t ++ """
}
""" 

TSNamed TLStore where
  toTypeName _ = "TLStore"

TSInterface TLStore where
  toTypeDecl (MkTLStore types functions constructors) = ""
    ++ (concat $ map toTypeDecl types) 
    ++ (toUnionDecl types "TLType")
    ++ (concat $ map toTypeDecl functions)
    ++ (toUnionDecl functions "TLSFunction")
    ++ (concat $ map toTypeDecl constructors)
    ++ (toUnionDecl constructors "TLSConstructor") 
    ++ """
interface TLStore {
  types: TLType[];
  functions: TLSFunction[];
  constructors: TLSConstructor[];
}
"""