module TypeInference where

import DataTypes (Expr(..), Type(..), Env, Constraint, Subst) -- import the data type definitions
import Unification (unify, substType) -- import the unification module (task 2)

{- Add your imports from the base package here (if necessary) -}
import Data.Maybe (fromJust)
import Control.Monad.Trans.State

-- Types for primitive operations
primitives :: Env
primitives  = [ ("+", TFun TInt (TFun TInt TInt))
              , ("*", TFun TInt (TFun TInt TInt))
              , ("-", TFun TInt TInt)
              , ("<", TFun TInt (TFun TInt TBool))
              , ("not", TFun TBool TBool)
              , ("and", TFun TBool (TFun TBool TBool))
              , ("ite", TFun TBool (TFun TInt (TFun TInt TInt))) ]

{- Task 1: Simple Inference -}

-- Infer the type of an expression from the given environment
simpleInfer :: Env -> Expr -> Maybe Type
simpleInfer env (CBool _) = Just TBool
simpleInfer env (CInt _) = Just TInt
simpleInfer env (Pair e1 e2) = Just (TPair (fromJust (simpleInfer env e1)) (fromJust (simpleInfer env e2)))
simpleInfer env (Var s) = do
    let typ = lookup s env
    case typ of
        Just t -> Just t
        Nothing -> Nothing
simpleInfer env (Ann _ t) = Just t
simpleInfer env (App e1 e2) = do
    let e1_type = simpleInfer env e1
    let e2_type = simpleInfer env e2
    case e1_type of
        Just (TFun t1 t2) | fromJust e2_type == t1 -> Just t2
        _ -> Nothing
simpleInfer env _ = Nothing

simpleInferWithPrimitives :: Env -> Expr -> Maybe Type
simpleInferWithPrimitives env expr = simpleInfer (env ++ primitives) expr

{- Task 2: Unification (see Unification.hs) -}



{- Task 3: Type Inference -}

-- A stateful monad for generating fresh type variables
type FreshM a = State Int a

-- Generate a type variable with a unique name (e.g. _t0, _t1, ...) using the counter in the state
-- You are not required to implement this function, but it may be useful
freshTVar :: FreshM Type
freshTVar = do
    n <- get
    put (n + 1)
    return $ TVar ("_t" ++ show n)

-- Run the FreshM monad with an initial counter value of 0
-- You are not required to implement this function, but it may be useful
runFreshM :: FreshM a -> a
runFreshM action = evalState action 0

-- Given an environment and an expression, generate a type and a set of constraints
-- You are free to change the type of this function if you want
-- You may assume that all free variables in the input expression are bound in the environment,
-- and that all types in the input environment are concrete (i.e. no type variables)
getConstraints :: Env -> Expr -> FreshM (Type, [Constraint])
getConstraints env expr = case expr of
    Var x -> case lookup x env of
        Just t -> return (t, [])
        Nothing -> error $ "Unbound variable: " ++ x
    CBool _ -> return (TBool, [])
    CInt _ -> return (TInt, [])
    Pair e1 e2 -> do
        (t1, c1) <- getConstraints env e1
        (t2, c2) <- getConstraints env e2
        return (TPair t1 t2, c1 ++ c2)
    App e1 e2 -> do
        (t1, c1) <- getConstraints env e1
        (t2, c2) <- getConstraints env e2
        tv <- freshTVar
        return (tv, (t1, TFun t2 tv) : c1 ++ c2)
    Lam x e -> do
        tv <- freshTVar
        (te, ce) <- getConstraints ((x, tv) : env) e
        return (TFun tv te, ce)
    Ann e t -> do
        (te, ce) <- getConstraints env e
        return (t, (te, t) : ce)

-- Infer the type of an expression from the given environment, using getConstraints, unify, and substType
inferType :: Env -> Expr -> Maybe Type
inferType env expr = evalState (do
    -- Generate type and constraints for the expression
    (t, constraints) <- getConstraints env expr
    -- Attempt to unify the constraints
    return $ do
        subst <- unify constraints
        -- Apply the resulting substitution to the type
        return $ applySubst subst t
    ) 0
  where
    applySubst :: Subst -> Type -> Type
    applySubst subst = substType subst


inferTypeWithPrimitives :: Env -> Expr -> Maybe Type
inferTypeWithPrimitives env expr = inferType (env ++ primitives) expr
