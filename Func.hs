module Func where

data Expr =
    Var Int
  | App Expr Expr
  | Lambda String Expr
  deriving (Eq, Ord, Read, Show)

{-
type ExprIndex = EI
data EI = Stop | LeftApp EI | RightApp EI 
data LambdaIndex -- int? line and col no.?
type GlobalExprIndex = (LambdaIndex, EI)
-}

data CVar = Foo -- CVar GlobalExprIndex Usage

{-
data Usage = Main | InvocationOf CVar
-}

genConstraints :: Expr -> C ()
genConstraints e =
  case e of
    Var i -> do
      x <- recall i
      constrain (Equal x)
    App e1 e2 -> do
      l <- left
      r <- right
      within l (genConstraints e1)
      within r (genConstraints e2)
      constrain (Invoke l r)
    Lambda _ e -> do
      a <- arg
      b <- body
      remember a (within b (genConstraints e))
      constrain (Abstract a b)

type Clause = [Constraint] -- Or'd together

data C a
instance Monad C

recall :: Int -> C CVar
recall = undefined

constrain :: (CVar -> Constraint) -> C ()
constrain = undefined

within :: CVar -> C a -> C a
within = undefined

remember :: CVar -> C a -> C a
remember = undefined

left, right, arg, body :: C CVar
left = undefined
right = undefined
arg = undefined
body = undefined

runC :: C a -> [Clause]
runC = undefined

data Constraint = Equal HC HC
  deriving (Eq, Ord, Read, Show)

-- data HalfConstraint = HC Env HC
type HalfConstraint = HC
data HC =
    HCVar Int
  | HCApp HC HC
  | HCLam String HC
  | HCCVar CVar
  deriving (Eq, Ord, Read, Show)

resolve :: CVar -> Constraint -> Constraint -> R [Constraint]
resolve commonVar implier unsatisfied =
  let (puzzle, piece) =
        case (implier,unsatisfied) of
          (Equal (HCCVar cv) _ | cv == commonVar
{-
data Constraint =
    Equal CVar CVar
  | Invoke CVar {- ^ applier -} CVar {- ^ applied -} CVar {- ^ result -}
  | Abstract CVar {- ^ arg -} CVar {- ^ body -} CVar {- ^ lambda -}
  deriving (Eq, Ord, Read, Show)

data Reason =
    ImpliedLeft
  | ImpliedRight
  | ImpliedApplier
  | ImpliedApplied
  | ImpliedResult
  | ImpliedArg
  | ImpliedBody
  | ImpliedLambda
  deriving (Bounded, Enum, Eq, Ord, Read, Show)
  -}

{-
resolve :: Reason -> Constraint -> Constraint -> R Constraint
resolve reason implier unsatisfied =
  let br = badReason reason implier
      bi = badImplication reason implier unsatisfied in
  case implier of
    Equal a b -> do
      (joiner, var) <- case reason of
               ImpliedLeft -> return (a, b)
               ImpliedRight -> return (b, a)
               _ -> br
      case unsatisfied of
        Equal c d | joiner == c -> constrain (Equal var d)
                  | joiner == d -> constrain (Equal c var)
                  | otherwise -> bi
        Invoke l r o | joiner == l -> constrain (Invoke var r   o)
                     | joiner == r -> constrain (Invoke l   var o)
                     | joiner == o -> constrain (Invoke l   r   var)
                     | otherwise -> bi
        Abstract a b l | joiner == a -> constrain (Abstract var b   l)
                       | joiner == b -> constrain (Abstract a   var l)
                       | joiner == l -> constrain (Abstract a   b   var)
                       | otherwise -> bi
    Invoke l r o ->
      case reason of
        ImpliedApplier ->
        ImpliedApplied ->
        ImpliedResult -> do
          case unsatisfied of
            Equal a b | o == a -> constrain (Invoke l r b)
                      | o == b -> constrain (Invoke l r a)
                      | otherwise -> bi
            Invoke l' r' o' | o == o' -> askUser -- constrain (SameApplication l r l' r')
                            | o == l' -> askUser -- constrain (Appl (Appl l r) r' o')
                            | o == r' -> askUser -- constrain (Appl l' (Appl l r) o')
                            | otherwise -> bi
            Abstract a b lm | o == a -> askUser -- constrain (Subst (Appl l r) b lm)
                            | o == b -> askUser -- constrain (Abstract a (Appl l r) lm)
                            | o == lm -> askUser -- constrain (Abstract a b (Appl lr))
                            | otherwise -> bi
        _ -> br
        -}
