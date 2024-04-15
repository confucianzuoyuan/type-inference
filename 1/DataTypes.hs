module DataTypes where

data Expr
  = Var String          -- Variable
  | CBool Bool          -- Bool constant
  | CInt Int            -- Int constant
  | Pair Expr Expr      -- Pairing
  | App Expr Expr       -- Application
  | Lam String Expr     -- Lambda abstraction
  | Ann Expr Type       -- Annotation
  deriving (Show, Eq)

data Type
  = TBool               -- Bool
  | TInt                -- Int
  | TVar String         -- Type variable
  | TFun Type Type      -- Function type
  | TPair Type Type     -- Pair type
  deriving (Show, Eq)

type Env = [(String, Type)]    -- Environment (variable name : type)

type Constraint = (Type, Type) -- Type constraint (t1 = t2)

type Subst = [(String, Type)]  -- Substitution (variable name ↦ type)
