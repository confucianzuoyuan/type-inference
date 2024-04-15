{-# LANGUAGE TemplateHaskell #-}
module QuasiQuote (toExpr, toType, convertExpr, convertType) where
  
import qualified Language.Haskell.TH as TH
import Language.Haskell.TH.Syntax (Lift(..))

import DataTypes

-- This is an optional module that helps you write tests for your type inference algorithm.
-- It uses Template Haskell (Haskell's metaprogramming system) to
-- convert Haskell expressions and types to our own data types.
-- This is useful for writing more comlicated test cases,
-- because it's easier to to write expressions and types in Haskell,
-- than to construct them manually in our own data types.
-- For example, instead of writing `App (App (Var "+") (CInt 1)) (CInt 2)`,
-- you can write `$(toExpr [| 1 + 2 |])` and get the same result.

-- The `toExpr` and `toType` functions are the main interface to this module.
-- Write $(toExpr [| ... |]) to convert a Haskell expression to our Expr data type,
-- and $(toType [t| ... |]) to convert a Haskell type to our Type data type.
-- The `t` in front of the type quotation is important,
-- it tells GHC that you want to quote a type, not an expression.
-- For types that contains type variables, you need to use the `forall` keyword,
-- like this: $(toType [t| forall a b. a -> b |]).

-- To use this module, you need to
--   1. Install the `template-haskell` package into your environment
--   2. Add `{-# LANGUAGE TemplateHaskell #-}` at the top of your test file (like this file)
--   2. import this module
-- You can also load this module into GHCi by running
-- $ ghci -XTemplateHaskell QuasiQuote.hs
-- then you can use the syntax described above to quickly create expressions and types.
-- For example:
-- ghci> $(toExpr [| (\x -> x) :: Int -> Int |])
-- Ann (Lam "x" (Var "x")) (TFun TInt TInt)

-- usage: $(toExpr [| 1 + 2 |]) --> App (App (Var "+") (CInt 1)) (CInt 2)
toExpr :: TH.Quote m => m TH.Exp -> m TH.Exp
toExpr = (>>= lift) . fmap convertExpr

-- usage: $(toType [t| forall a. a -> Int |]) --> TFun (TVar "a") TInt
toType :: TH.Quote m => m TH.Type -> m TH.Exp
toType = (>>= lift) . fmap convertType

convertExpr :: TH.Exp -> Expr
convertExpr (TH.LitE (TH.IntegerL n)) = CInt (fromIntegral n)
convertExpr (TH.ConE c)
  | c == 'True = CBool True
  | c == 'False = CBool False
  | otherwise = error "Unknown constructor"
convertExpr (TH.VarE v)
  | v == 'negate = Var "-"
  | otherwise = Var (TH.nameBase v)
convertExpr (TH.UnboundVarE v) = Var (TH.nameBase v)
convertExpr (TH.InfixE (Just e1) op (Just e2)) =
  App (App (convertExpr op) (convertExpr e1)) (convertExpr e2)
convertExpr (TH.AppE e1 e2) = App (convertExpr e1) (convertExpr e2)
convertExpr (TH.LamE [TH.VarP v] e) = Lam (TH.nameBase v) (convertExpr e)
convertExpr (TH.TupE [Just e1, Just e2]) = Pair (convertExpr e1) (convertExpr e2)
convertExpr (TH.SigE e t) = Ann (convertExpr e) (convertType t)

convertType :: TH.Type -> Type
convertType (TH.ConT c)
  | c == ''Int = TInt
  | c == ''Bool = TBool
  | otherwise = error "Unknown type constructor"
convertType (TH.AppT (TH.AppT TH.ArrowT t1) t2) =
  TFun (convertType t1) (convertType t2)
convertType (TH.AppT (TH.AppT (TH.TupleT 2) t1) t2) =
  TPair (convertType t1) (convertType t2)
convertType (TH.ForallT _ _ t) = convertType t
convertType (TH.VarT v) = TVar (TH.nameBase v)

instance Lift Expr where
  lift (CInt n) = [| CInt n |]
  lift (CBool b) = [| CBool b |]
  lift (Var v) = [| Var v |]
  lift (App e1 e2) = [| App e1 e2 |]
  lift (Lam v e) = [| Lam v e |]
  lift (Pair e1 e2) = [| Pair e1 e2 |]
  lift (Ann e t) = [| Ann e t |]
  liftTyped _ = error "liftTyped not implemented"

instance Lift Type where
  lift TInt = [| TInt |]
  lift TBool = [| TBool |]
  lift (TFun t1 t2) = [| TFun t1 t2 |]
  lift (TPair t1 t2) = [| TPair t1 t2 |]
  lift (TVar v) = [| TVar v |]
  liftTyped _ = error "liftTyped not implemented"
