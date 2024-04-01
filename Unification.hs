module Unification where

import DataTypes (Type (..), Constraint, Subst)

{- Add your imports from the base package here (if necessary) -}

{- Task 2: Substitution and Unification -}

-- substitute :: (String, Type) -> Type -> Type
-- substitute _ TBool = TBool
-- substitute _ TInt = TInt
-- substitute (x, u) (TVar c) = if c == x then u else TVar c
-- substitute (x, u) (TFun t1 t2) = TFun (substitute (x, u) t1) (substitute (x, u) t2)

substitute :: (String, Type) -> Type -> Type
substitute (var, newType) t = case t of
    TVar x
        | x == var -> newType  -- 如果类型变量匹配，进行替换
        | otherwise -> t  -- 否则，保持不变
    TFun t1 t2 -> TFun (substitute (var, newType) t1) (substitute (var, newType) t2)
    TPair t1 t2 -> TPair (substitute (var, newType) t1) (substitute (var, newType) t2)
    _ -> t  -- 对于其他类型，没有子类型需要递归替换，直接返回


-- Apply a substitution to a type
substType :: Subst -> Type -> Type
substType subs t = foldr substitute t subs

-- Apply a substitution to a constraint
substConstraint :: Subst -> Constraint -> Constraint
substConstraint = undefined

-- Apply a substitution to a list of constraints
substConstraints :: Subst -> [Constraint] -> [Constraint]
substConstraints = undefined

-- Check if a variable name occurs in a type
occursIn :: String -> Type -> Bool
occursIn name (TVar s) = name == s
occursIn name (TFun t1 t2) = (occursIn name t1) || (occursIn name t2)
occursIn _ _ = False

unifyOne :: Constraint -> Maybe Subst
unifyOne (TInt, TInt) = Just []
unifyOne (TBool, TBool) = Just []
unifyOne (TVar x, z) = if not (occursIn x z) then Just [(x, z)] else Nothing
unifyOne (z, TVar x) = if not (occursIn x z) then Just [(x, z)] else Nothing
unifyOne (TFun a b, TFun x y) = unify [(a, x), (b, y)]
unifyOne _ = Nothing

-- Given a list of constraints, generate the _most general unifier_ for the constraints if it exists
unify :: [Constraint] -> Maybe Subst
unify [] = Just []
unify ((x, y):xs) = do
    let t2 = unify xs
    case t2 of
        Just _t2 -> do
            let t1 = unifyOne ((substType _t2 x), (substType _t2 y))
            case t1 of
                Just _t1 -> Just (_t1 ++ _t2)
                _ -> Nothing
        _ -> Nothing


