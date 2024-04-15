import Control.Monad.State.Lazy
import Data.Map.Strict qualified as Map
import Data.Maybe
import Data.Set qualified as Set
import System.Environment
import System.IO
import Prelude

type VarId = String

data Type
  = TInt
  | TBool
  | TError
  | TVar Int
  | TArr Type Type
  deriving (Eq, Ord, Read, Show)

data Constraint
  = CEq Type Type
  | CError
  deriving (Eq, Ord, Read, Show)

type ConstraintSet = Set.Set Constraint

type ConstraintList = [Constraint]

data Expr
  = CInt Int
  | CBool Bool
  | Var VarId
  | Plus Expr Expr
  | Minus Expr Expr
  | Equal Expr Expr
  | ITE Expr Expr Expr
  | Abs VarId Expr
  | App Expr Expr
  | LetIn VarId Expr Expr
  deriving (Eq, Ord, Read, Show)

type Env = Map.Map VarId Type

type InferState a = State Int a

type Substitution = Map.Map Type Type

-- 用来产生新的独一无二的变量
getFreshTVar :: InferState Type
getFreshTVar = do
  n <- get
  put (n + 1)
  return (TVar n)

infer :: Env -> Expr -> InferState (Type, ConstraintSet)
infer g (CInt _) = return (TInt, Set.empty)
infer g (Abs x e) = do
  y <- getFreshTVar
  (t, c) <- infer (Map.insert x y g) e
  return (TArr y t, c)
infer g (CBool _) = return (TBool, Set.empty)
infer g (Plus a b) = do
  (t1, c1) <- infer g a
  (t2, c2) <- infer g b
  return (TInt, Set.insert (CEq t2 TInt) (Set.insert (CEq t1 TInt) (Set.union c1 c2)))
infer g (Minus a b) = do
  (t1, c1) <- infer g a
  (t2, c2) <- infer g b
  return (TInt, Set.insert (CEq t2 TInt) (Set.insert (CEq t1 TInt) (Set.union c1 c2)))
infer g (Equal a b) = do
  (t1, c1) <- infer g a
  (t2, c2) <- infer g b
  return (TBool, Set.insert (CEq t1 t2) (Set.union c1 c2))
-- LetIn "x" (CInt 1) (Var "x")
infer g (LetIn x a b) = do
  y <- getFreshTVar
  (t1, c1) <- infer (Map.insert x y g) a
  (t2, c2) <- infer (Map.insert x y g) b
  return (t2, Set.insert (CEq y t1) (Set.union c1 c2))
infer g (ITE cond a b) = do
  (t1, c1) <- infer g cond
  (t2, c2) <- infer g a
  (t3, c3) <- infer g b
  return (t2, Set.insert (CEq t2 t3) (Set.insert (CEq t1 TBool) (Set.union c3 (Set.union c1 c2))))
-- App (Abs "x" (Var "x")) (CInt 1)
infer g (App a b) = do
  (t1, c1) <- infer g a
  (t2, c2) <- infer g b
  x1 <- getFreshTVar
  x2 <- getFreshTVar
  return (x2, Set.insert (CEq t1 (TArr x1 x2)) (Set.insert (CEq t2 x1) (Set.union c1 c2)))
infer g (Var varID) = do
  case Map.lookup varID g of
    Nothing -> return (TError, Set.singleton CError)
    Just x -> return (x, Set.empty)

inferExpr :: Expr -> (Type, ConstraintSet)
inferExpr expr = evalState (infer Map.empty expr) 1

toCstrList :: ConstraintSet -> ConstraintList
toCstrList = Set.toList

applySub :: Substitution -> Type -> Type
applySub subs var = case var of
  TError -> TError
  TInt -> TInt
  TBool -> TBool
  (TArr a b) -> TArr (applySub subs a) (applySub subs b)
  (TVar a) -> Data.Maybe.fromMaybe (TVar a) (Map.lookup (TVar a) subs)

applySubToCstrList :: Substitution -> ConstraintList -> ConstraintList
applySubToCstrList subs (c : cs) = case c of
  (CEq a b) -> CEq (applySub subs a) (applySub subs b) : applySubToCstrList subs cs
  CError -> CError : applySubToCstrList subs cs
applySubToCstrList _ cList = cList

composeSub :: Substitution -> Substitution -> Substitution
composeSub = Map.union

tvars :: Type -> Set.Set Type
tvars TInt = Set.empty
tvars TBool = Set.empty
tvars TError = Set.insert TError Set.empty
tvars (TVar a) = Set.insert (TVar a) Set.empty
tvars (TArr a b) = Set.union (tvars a) (tvars b)

-- follow the slide 20 p28 algorithm
unify :: ConstraintList -> Maybe Substitution
-- unify conList = case conList of
--   [] -> Just Map.empty
--   (CError : cs) -> Nothing
--   ((CEq s t) : cs) -> unifyAux (CEq s t) cs
unify [] = Just Map.empty
unify (CError : constraints) = Nothing
unify ((CEq t1 t2) : constraints) = unifyHelper (CEq t1 t2) constraints

unifyHelper :: Constraint -> ConstraintList -> Maybe Substitution
unifyHelper (CEq s t) cs =
  if s == t
    then unify cs
    else case s of
      (TVar a) ->
        if Set.member (TVar a) (tvars t)
          then Nothing
          else case unify (applySubToCstrList (Map.insert (TVar a) t Map.empty) cs) of
            Just subs -> Just (Map.insert (TVar a) t subs)
            Nothing -> Nothing
      (TArr s1 s2) -> case t of
        (TArr t1 t2) -> unify (cs ++ [CEq s1 t1] ++ [CEq s2 t2])
        _ -> Nothing
      _ -> case t of
        (TVar a) ->
          if Set.member (TVar a) (tvars s)
            then Nothing
            else case unify (applySubToCstrList (Map.insert (TVar a) s Map.empty) cs) of
              Just subs -> Just (Map.insert (TVar a) s subs)
              Nothing -> Nothing
        _ -> Nothing

typing :: Expr -> Maybe Type
typing expr = case unify (toCstrList constraintSet) of
  Just subs -> Just (applySub subs resultType)
  Nothing -> Nothing
  where
    (resultType, constraintSet) = inferExpr expr

typeInfer :: Expr -> String
typeInfer e = case typing e of
  Just v -> show (relabel v)
  Nothing -> "Type Error"

-- main logic, no need to modify

testProgram :: String -> String
testProgram [] = []
testProgram s = typeInfer (readExpr s)

readExpr :: String -> Expr
readExpr s = read s :: Expr

processExpr :: [String] -> String
processExpr [] = []
processExpr (x : xs) = typeInfer (readExpr x) ++ "\n" ++ processExpr xs

main :: IO ()
main = do
  fileName <- getArgs
  handle <- openFile (head fileName) ReadMode
  contents <- hGetContents handle
  let ls = lines contents
  putStr (processExpr ls)
  hClose handle

-- Apendix
type RelabelState a = State (Map.Map Int Int) a

relabel :: Type -> Type
relabel t = evalState (go t) Map.empty
  where
    go :: Type -> RelabelState Type
    go TInt = return TInt
    go TBool = return TBool
    go TError = return TError
    go (TVar x) = do
      m <- get
      case Map.lookup x m of
        Just v -> return (TVar v)
        Nothing -> do
          let n = 1 + Map.size m
          put (Map.insert x n m)
          return (TVar n)
    go (TArr t1 t2) = do
      t1' <- go t1
      t2' <- go t2
      return (TArr t1' t2')
