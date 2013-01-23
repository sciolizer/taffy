module Debugger where

import Control.Monad
import Data.IORef

import Types

showStage :: Stage c -> String
showStage x =
  case x of
    Uninjecting _ Before -> "before uninjecting"
    Uninjecting _ After -> "after uninjecting"
    Injecting _ _ Before -> "before injecting"
    Injecting _ _ After -> "after injecting"
    PoppedConstraint (Just _) -> "popped a constraint"
    PoppedConstraint Nothing -> "popped no constraint"
    PoppedVar (Just _) -> "popped a var"
    PoppedVar Nothing -> "popped no var"
    CountedValues _ _ -> "counted values"
    JumpingBack Before -> "before jumping back"
    JumpingBack After -> "after jumping back"
    SteppingBack Before -> "before stepping back"
    SteppingBack After -> "after stepping back"
    WillRunSideEffect _ -> "before running side effect"
    RanSideEffect _ _ _ -> "after running side effect"
    AccumulatingAffectedConstraints Before -> "before accumulating affected constraints"
    AccumulatingAffectedConstraints After -> "after accumulating affected constraints"

cliDebugger :: IO (Debugger constraint -> Stage constraint -> IO ())
cliDebugger = do
  ref <- newIORef False
  return $ \d stage -> do
    b <- readIORef ref
    when (not b) $ putStrLn "Type 'help' to get a list of commands."
    writeIORef ref True
    putStrLn (showStage stage)
    readLn
