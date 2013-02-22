module Lang where

type Id = String
type Constructor = String
type Type = String

data Expr =
    App Expr [Expr]
  | Let Binding Expr
  | Case Expr [CaseBranch]
  | Literal Int
  | Const Constructor
  | Var String {- for debugging -} Int {- deBruijn index -}
  | Ite Expr Expr Expr
  | Lambda String Expr
  deriving (Eq, Ord, Read, Show)

data Reduced =
    RLiteral Int
  | RConst Constructor [Reduced]
  | RLambda String Expr [Reduced] {- bindings for free variables inside expr, shifted by one (binding for str not included, obviously) -}

data Binding = Binding Id [Id] Expr
  deriving (Eq, Ord, Read, Show)

data CaseBranch = CaseBranch Constructor [Id] Expr
  deriving (Eq, Ord, Read, Show)

data Program = Program [Adt] [Binding]
  deriving (Eq, Ord, Read, Show)

data Adt = Adt Type [(Constructor,[Type])]
  deriving (Eq, Ord, Read, Show)

data Constraint =
    Unify EL CAdt
  | System [Equation]
  | CaseBranch EL [[EL]]
  | Construct EL EL EL
  -- | Invoke is just a special case of Unify (ELs are relative; the context for the parameters will be just one function high (the current function)
  deriving (Eq, Ord, Read, Show)

data CAdt =
    Constant Reduced
  | Atomic EL
  | Term EL {- constructor -} [CAdt]
  deriving (Eq, Ord, Read, Show)

data Equation = Eq Sum Sum
  deriving (Eq, Ord, Read, Show)

data Sum = Sum [EL] {- added -} [EL] {- subtracted -}
  deriving (Eq, Ord, Read, Show)

type EL = [Invocation]

data Invocation = Invocation { loc :: ExprLoc, iteration :: Int }

data ExprLoc = ExprLoc { line :: Int, column :: Int }

resolve :: Constraint -> Constraint -> Maybe [Constraint]
resolve (Unify v1 t1) (Unify v2 t2) = z where
  z = if v1 == v2 then joinCAdt t1 t2 else if v1 `inside` t2 then Just [Unify 
    then case (t1, t2) of
           (Constant r1, Constant r2) -> if betaEq r1 r2 then Just [] else Nothing
           (Constant r1, Atomic el) -> Just [Unify e1 r1]
           (Constant (RConst c1 args1), (Term c2 args2)) -> Just (Unify c2 (Constant (RConst c1 [])) : error 
