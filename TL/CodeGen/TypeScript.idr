module TL.CodeGen.TypeScript

import Prelude.List
import List.Split
import Text.Casing
import TL.Types
import TL.Store.Store
import Effects
import Effect.State
import Effect.Exception
import Effect.StdIO

%access public export

TSEff : Type -> Type
TSEff ret = Effects.SimpleEff.Eff ret [
  Store ::: STATE TLStore,
  EXCEPTION String
]

interface TSNamed a where
  toTypeName : a -> TSEff String

interface TSNamed a => TSInterface a where
  toTypeDecl : a -> TSEff String
  toExportedTypeDecl : a -> TSEff String

  toExportedTypeDecl t = do
    name <- toTypeDecl t
    pure $ "export" ++ name

interface TSInterfaceProperty a where
  toPropDecl : a -> TSEff String

interface TSNamed a => TSFunction a where
  toFunDecl : a -> TSEff String
  toExportedFunDecl : a -> TSEff String

  toExportedFunDecl t = do
    fun <- toFunDecl t
    pure $ "export " ++ fun

interface TSNamed a => TSUnion a where
  toUnionDecl : a -> String -> TSEff String
  toExportedUnionDecl : a -> String -> TSEff String

  toExportedUnionDecl xs name = do
    union <- toUnionDecl xs name
    pure $ "export " ++ union

interface TSModule a where
  toModuleDef : a -> Either String String

toIdent : String -> String -> String
toIdent name prefix = prefix ++ (pascal . replace' "." "_") name
  
wrapInModule : String -> String
wrapInModule x = """declare module 'tl' {
""" ++ x ++ """
}"""

TSNamed (List a) where
  toTypeName _ = pure "List"

TSNamed a => TSUnion (List a) where
  toUnionDecl xs name = do
      types <- union' "" xs
      pure $ "type " ++ name ++ " = " ++ types ++ ";\n" 
    where
      union' : String -> (List a) -> TSEff String
      union' acc []        = pure acc
      union' acc [x]       = do
        v <- toTypeName x
        pure $ acc ++ v
      union' acc (x :: xs) = do
        name <- toTypeName x
        union' (acc ++ name ++ "\n | ") xs

TSNamed TLType where
  toTypeName (MkTLType name _) = pure $ toIdent name "T"
  toTypeName (MkTLTypeBuiltin x) = pure $ show x

TSNamed TLSConstructor where
  toTypeName (MkTLSConstructor identifier _ _ _ _) = pure $ toIdent identifier "C"

TSNamed TLSFunction where
  toTypeName (MkTLSFunction identifier _ _ _) = pure $ toIdent identifier "F"

TSNamed TLBuiltIn where
  toTypeName TLInt = pure "number"
  toTypeName TLNat = pure "number"
  toTypeName TLLong = pure "string"
  toTypeName TLString = pure "string"
  toTypeName TLDouble = pure "number"
  toTypeName TLTType = pure "any"
  toTypeName TLInt128 = pure "number"
  toTypeName TLInt256 = pure "number"

TSNamed TypeRef where
  toTypeName (Left a) = toTypeName a
  toTypeName (Right (a, b)) = do
    store <- Store :- get
    let c = storeGetType (Right (a, b)) store
    pure $ show a ++ ", " ++ show b ++ ", " ++ toTypeName c

TSNamed TLSTypeExpr where
  toTypeName (MkTLSTypeExpr type children) = do 
    name <- toTypeName type
    pure $ name ++ "/*" ++ (show children) ++ "*/ "
  toTypeName (MkTLSTypeArray mult args) = pure $ (show mult) ++ "*" ++ (show args)
  toTypeName (MkTLSTypeVar ref) = pure $ "/*generic*/ #" ++ (show ref)
  toTypeName (MkTLSTypeBare expr) = do 
    name <- toTypeName expr
    pure $ "/*bare*/" ++ name
  toTypeName (MkTLSTypeBang expr) = do
    name <- toTypeName expr
    pure $ "/*bang*/" ++ name
  toTypeName (MkTLSTypeHole name exprs) = pure $ "?hole " ++ (show name) ++ " " ++ (show exprs)

TSInterfaceProperty TLSArg where
  toPropDecl (MkTLSArg id var_num type) = do
    name <- toTypeName type
    pure $ id ++ ": " ++ name
  toPropDecl (MkTLSArgOpt id var_num type) = do
    name <- toTypeName type
    pure $ "{" ++ id ++ ": " ++ name ++ "}"
  toPropDecl (MkTLSArgCond id var_num cond type) = do
    name <- toTypeName type
    pure $ id ++ "?: " ++ name ++ " /*cond*/" ++ (show cond)

TSInterface TLType where
  toTypeDecl t = do
    interfaceName <- toTypeName t
    pure $ case t of
      MkTLType name _ => """
interface """ ++ interfaceName ++ """ {
  _: '""" ++ name ++ """';
  // """ ++ show t ++ """
}
"""
      MkTLTypeBuiltin => """
interface """ ++ interfaceName ++ """ {}
"""

TSInterface TLSConstructor where
  toTypeDecl t@(MkTLSConstructor identifier _ args _ _) = do
    typeName <- toTypeName t
    props <- mapE (\x => toPropDecl x) args
    pure $ """
interface """ ++ typeName ++ """ {
  // """ ++ show t ++ """
  _: '""" ++ identifier ++ """';
  """ ++ concat (intersperse ";\n  " props) ++ """
}
"""

TSInterface TLSFunction where
  toTypeDecl t@(MkTLSFunction identifier _ args resultType) = do 
    typeName <- toTypeName t
    props <- mapE (\x => toPropDecl x) args
    pure $ """
interface """ ++ typeName ++ """ {
  // """ ++ show t ++ """
  // """ ++ show args ++ """
  // """ ++ show resultType ++ """
  _: '""" ++ identifier ++ """';
  """ ++ concat (intersperse ";\n  " props) ++ """
}
"""

TSFunction TLSFunction where
  toFunDecl t@(MkTLSFunction identifier _ _ _) = do
    typeName <- toTypeName t
    pure $ "function invoke(method: '" ++ identifier ++ "', input: " ++ typeName ++ "): void\n"

TSNamed TLStore where
  toTypeName _ = pure $ "TLStore"

TSInterface TLStore where
  toTypeDecl _ = pure $ """
interface TLStore {
  types: TLType[];
  functions: TLSFunction[];
  constructors: TLSConstructor[];
}
"""

mkString' : TSEff String
mkString' = do
  store <- Store :- get
  -- let (MkTLStore types functions constructors) = store
  newTypes <- mapE (\x => toTypeDecl x) (types store)
  newFuns <- mapE (\x => toTypeDecl x) (functions store)
  newFunsDecl <- mapE (\x => toFunDecl x) (functions store)
  newCons <- mapE (\x => toTypeDecl x) (constructors store)
  typesUnion <- toUnionDecl (types store) "TLType"
  funUnion <- toUnionDecl (functions store) "TLSFunction"
  conUnion <- toUnionDecl (constructors store) "TLSConstructor"
  newStore <- toTypeDecl store
  pure $ ""
    ++ (concat $ newTypes)
    ++ typesUnion
    ++ (concat $ newFuns)
    ++ (concat $ newFunsDecl)
    ++ funUnion
    ++ (concat $ newCons)
    ++ conUnion
    ++ newStore

mkExportedString' : TSEff String
mkExportedString' = do
  store <- Store :- get
  -- let (MkTLStore types functions constructors) = store
  newTypes <- mapE (\x => toExportedTypeDecl x) (types store)
  newFuns <- mapE (\x => toExportedTypeDecl x) (functions store)
  newFunsDecl <- mapE (\x => toExportedFunDecl x) (functions store)
  newCons <- mapE (\x => toExportedTypeDecl x) (constructors store)
  typesUnion <- toExportedUnionDecl (types store) "TLType"
  funUnion <- toExportedUnionDecl (functions store) "TLSFunction"
  conUnion <- toExportedUnionDecl (constructors store) "TLSConstructor"
  newStore <- toExportedTypeDecl store
  pure $ ""
    ++ (concat $ newTypes)
    ++ typesUnion
    ++ (concat $ newFuns)
    ++ (concat $ newFunsDecl)
    ++ funUnion
    ++ (concat $ newCons)
    ++ conUnion
    ++ newStore


{-
mkExportedString' : TSEff String
mkExportedString' = do
  store <- Store :- get
  let (MkTLStore types functions constructors) = store
  pure $ ""
    ++ (concat $ map toExportedTypeDecl types)
    ++ toExportedUnionDecl types "TLType"
    ++ (concat $ map toExportedTypeDecl functions)
    ++ (concat $ map toExportedFunDecl functions)
    ++ toExportedUnionDecl functions "TLSFunction"
    ++ (concat $ map toExportedTypeDecl constructors)
    ++ toExportedUnionDecl constructors "TLSConstructor"
    ++ (toExportedTypeDecl store)
-}

TSModule TLStore where
  toModuleDef store = runInit [ 
    Store := store,
    default
  ] mkString'

[ExportAll] TSModule TLStore where
  toModuleDef store = runInit [ 
    Store := store,
    default
  ] mkExportedString'
