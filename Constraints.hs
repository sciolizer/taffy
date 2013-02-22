module Constraints where

type Constructor = String

data Val =
    I Int
  | ADT Constructor [Val]
  | F (Val -> Val) 

type FunctionName = String
data Invocation = Invocation { caller :: FunctionName, callerLoc :: Loc }
type Stack = [Invocation]

-- this is actually a really lame index... the problem is
-- that iterations can stomp on each other. Todo: think of a better
-- index.
data FunctionIndex = FunctionIndex { stack :: Stack, iteration :: Int }

data EL = ExpressionLocation { index :: FunctionIndex, lineNumber :: Int, colNumber :: Int }

data Constraint =
    Unify (ADT,ADT) -- use for linking function args and results, and for multiple uses within a single function
  | System [Equation]
  | CaseBranch EL {- case _ of -} [[EL]] {- bindings in each branch -}
  | Application EL EL EL -- only for constructor application; function application is handled by Equal

data Equation = Equation Poly Poly

data Poly = Use EL | Add Poly Poly | Multiply Poly Poly

data ADT = Merely EL | Struct String [ADT]

{- resolution:
Unify with Unify makes Unify
Unify with System is sometimes a System (make a substituion), otherwise is ?
Unify with CaseBranch discriminant is sometimes a CaseBranch (make a substitution), otherwise is ?
Unify with CaseBranch binding is sometimes a CaseBranch (make a substitution), 
Equal with a makes a (substitute EL in the other)
System with System is another system (just concatenate the equations)
System with CaseBranch discriminant is a type error
System with CaseBranch binding is ?
System with Application result or applier is type error
System with Application arg is ?
CaseBranch discriminant with Application result is a collection of Equals
CaseBranch discriminant with Application applier is a type error
CaseBranch discriminant with Application arg is ?
CaseBranch binding with Application result is ? (possible if we have a unifier primitive)
CaseBranch binding with Application arg is ?
CaseBranch binding with Application applier is ?
Application result with Application result is a collection of Equals
Application result with Application arg is ?
Application arg with Application arg is ?

-- so actually, caseBranch and Application can probably be subsumed under
-- a more general form of structural equality
-- Essentially, unification.
-}
