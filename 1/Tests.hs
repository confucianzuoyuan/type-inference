import Test.Tasty
import Test.Tasty.HUnit

import DataTypes (Expr(..), Type(..), Env, Constraint, Subst)
import TypeInference (simpleInfer, inferType, simpleInferWithPrimitives, inferTypeWithPrimitives)
import Unification (unify)

import Data.Maybe (fromJust)
import Data.List (union, foldl', nub, (\\))
import Control.Monad.Trans.State
import Control.Monad (zipWithM)

main = defaultMain (testGroup "A2 Tests" [task1, task2, task3])

checkSimpleInfer :: HasCallStack => Env -> Expr -> Maybe Type -> Assertion
checkSimpleInfer env expr expected = simpleInferWithPrimitives env expr @?= expected

task1 = testGroup "Task 1" [test11, test12, test13, test14]
  where
    test11 = testGroup "Bool constants, Int constants, and pairing only"
      [ testCase "1.1.1" $
          checkSimpleInfer [] (Pair (CBool True) (Pair (CBool False) (CInt 3))) (Just (TPair TBool (TPair TBool TInt)))
      ]

    test12 = testGroup "Bool constants, Int constants, pairing, and variables"
      [ testCase "1.2.1" $
          checkSimpleInfer [("x", TInt)] (Pair (CBool True) (Pair (CBool False) (Var "x"))) (Just (TPair TBool (TPair TBool TInt)))
      ]

    test13 = testGroup "Guaranteed to be typeable"
      [ testCase "1.3.1" $
          checkSimpleInfer [("x", TInt)] (App (Ann (App (Var "+") (Var "x")) (TFun TInt TInt)) (CInt 1)) (Just TInt)
      ]

    test14 = testGroup "No constraints"
      [ testCase "1.4.1" $
          checkSimpleInfer [("x", TBool)] (App (App (Var "+") (Var "x")) (CInt 1)) Nothing
      ]

type Rename = [(String, String)]

-- Check if a rename is an isomorphism
isIsomorphism :: Rename -> Bool
isIsomorphism f = let g = nub f
  in let len = length g
  in let l = nub (map fst g)
  in let r = nub (map snd g)
  in len == length l && len == length r

-- Match two types and generate a matching between type variables
matchType :: Type -> Type -> Maybe Rename
matchType (TVar v) (TVar v') = Just [(v, v')]
matchType (TFun t1 t2) (TFun t1' t2') = do
  r1 <- matchType t1 t1'
  r2 <- matchType t2 t2'
  return (r1 ++ r2)
matchType (TPair t1 t2) (TPair t1' t2') = do
  r1 <- matchType t1 t1'
  r2 <- matchType t2 t2'
  return (r1 ++ r2)
matchType TBool TBool = Just []
matchType TInt TInt = Just []
matchType _ _ = Nothing

-- Lookup a variable in a substitution
lookupSubst :: String -> Subst -> Type
lookupSubst v s = case lookup v s of
  Just t -> t
  Nothing -> TVar v

-- Match two substitutions
matchSubst :: Subst -> Subst -> [String] -> Maybe Rename
matchSubst s1 s2 [] = Just []
matchSubst s1 s2 (v:vs) = do
  t1 <- matchType (lookupSubst v s1) (lookupSubst v s2)
  t2 <- matchSubst s1 s2 vs
  return (t1 ++ t2)

-- Check if two types are the same, up to type variable renaming
sameType :: Type -> Type -> Bool
sameType t1 t2 = case matchType t1 t2 of
  Just r -> isIsomorphism r
  Nothing -> False

-- Check if two substitutions are the same, up to type variable renaming
sameSubst :: Subst -> Subst -> [String] -> Bool
sameSubst s1 s2 dom = case matchSubst s1 s2 dom of
  Just r -> isIsomorphism r
  Nothing -> False

-- Get the list of type variables in a type
typeVars :: Type -> [String]
typeVars (TVar v) = [v]
typeVars (TFun t1 t2) = typeVars t1 ++ typeVars t2
typeVars (TPair t1 t2) = typeVars t1 ++ typeVars t2
typeVars _ = []

-- Get the list of type variables in a list of constraints
constraintVars :: [Constraint] -> [String]
constraintVars cs = nub (concatMap (\(t1, t2) -> typeVars t1 ++ typeVars t2) cs)

-- Get the domain of a substitution
domSubst :: Subst -> [String]
domSubst s = nub (map fst s)

-- Check if the result of unification is equivalent to the reference solution
checkUnify :: HasCallStack => [Constraint] -> Maybe Subst -> Assertion
checkUnify cs Nothing =
  unify cs == Nothing @?
    "Expected unification to fail, but succeeded."
      ++ "\n constraints: " ++ show cs
      ++ "\n result: " ++ show (unify cs)
checkUnify cs (Just sref) = do
  let result = unify cs
  (result /= Nothing) @?
    "Expected unification to succeed, but failed."
      ++ "\n constraints: " ++ show cs
      ++ "\n expected: " ++ show sref
  let (Just s) = unify cs
  let csVars = constraintVars cs
  domSubst s `isSubsetOf` csVars @?
    "Domain of unification result contains variables not present in the constraints."
      ++ "\n result: " ++ show s
      ++ "\n redundant variables: " ++ show (domSubst s \\ csVars)
      ++ "\n constraints: " ++ show cs
  sameSubst s sref csVars @?
    "Result of unification does not match the reference solution."
      ++ "\n result: " ++ show s
      ++ "\n expected: " ++ show sref
      ++ "\n constraints: " ++ show cs
  where
    isSubsetOf :: Eq a => [a] -> [a] -> Bool
    isSubsetOf xs ys = all (`elem` ys) xs

task2 = testGroup "Task 2" [test21, test22, test23, test24]
  where
    test21 = testGroup "Variables only"
      [ testCase "2.1.3" $
          checkUnify [(x, y), (y, z)] (Just [("x", z), ("y", z)])
      ]

    test22 = testGroup "Variables and constants"
      [ testCase "2.2.1" $
          checkUnify [(c, x)] (Just [("x", c)])
      ]
    
    test23 = testGroup "Guaranteed to be solvable"
      [ testCase "2.3.1" $
          checkUnify [(TFun x c, TFun c y)] (Just [("x", c), ("y", c)])
      ]
    
    test24 = testGroup "No constraints"
      [ testCase "2.4.1" $
          checkUnify [(TFun (TVar "x") (TVar "y"), TVar "x")] Nothing
      ]
    
    x = TVar "x" :: Type
    y = TVar "y" :: Type
    z = TVar "z" :: Type
    c = TFun TInt TInt :: Type
    d = TFun TBool TBool :: Type

checkInferType :: HasCallStack => Env -> Expr -> Maybe Type -> Assertion
checkInferType env expr Nothing =
  inferTypeWithPrimitives env expr == Nothing @?
    "Expected type inference to fail, but succeeded."
      ++ "\n env: " ++ show env
      ++ "\n expr: " ++ show expr
      ++ "\n result: " ++ show (inferTypeWithPrimitives env expr)
checkInferType env expr (Just tref) = do
  let result = inferTypeWithPrimitives env expr
  (result /= Nothing) @?
    "Expected type inference to succeed, but failed."
      ++ "\n env: " ++ show env
      ++ "\n expr: " ++ show expr
      ++ "\n expected: " ++ show tref
  let (Just t) = result
  sameType t tref @?
    "Result of type inference does not match the reference solution."
      ++ "\n env: " ++ show env
      ++ "\n expr: " ++ show expr
      ++ "\n result: " ++ show t
      ++ "\n expected: " ++ show tref

task3 = testGroup "Task 3" [test31, test32, test33, test34, test35]
  where
    test31 = testGroup "Same assumption as Task 1"
      [ testCase "3.1.1" $
          checkInferType
            [("x", TInt)]
            (App (Ann (App (Var "+") (Var "x")) (TFun TInt TInt)) (CInt 1))
            (Just TInt)
      ]

    test32 = testGroup "Lambda abstractions are annotated"
      [ testCase "3.2.1" $
          checkInferType
            [("x", TBool)]
            (App (Ann (Lam "x" (Var "x")) (TFun TInt TInt)) (CInt 1))
            (Just TInt)
      ]

    test33 = testGroup "All bound variables are distinct"
      [ testCase "3.3.1" $
          checkInferType
            []
            (App (Lam "x" (Var "x")) (Lam "y" (Var "y")))
            (Just (TFun (TVar "t") (TVar "t")))
      ]

    test34 = testGroup "Guaranteed to be typeable"
      [ testCase "3.4.1" $
          checkInferType
            []
            (Pair (Lam "x" (Lam "y" (Var "y"))) (Lam "x" (App (Var "not") (Var "x"))))
            (Just (TPair (TFun (TVar "a") (TFun (TVar "b") (TVar "b"))) (TFun TBool TBool)))
      ]

    test35 = testGroup "No constraints"
      [ testCase "3.5.1" $
          checkInferType
            []
            (Lam "x" (App (Var "x") (Var "x")))
            Nothing
      ]
