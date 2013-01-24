{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Debugger where

import Control.Applicative
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Reader
import Data.IORef
import Data.Maybe
import qualified Data.Set as S
import Safe

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

stages = map showStage $ concat [
  ba $ Uninjecting u,
  ba $ Injecting u u,
  one $ PoppedConstraint (Just u),
  one $ PoppedConstraint Nothing,
  one $ PoppedVar (Just u),
  one $ PoppedVar Nothing,
  one $ CountedValues u u,
  ba $ JumpingBack,
  ba $ SteppingBack,
  one $ WillRunSideEffect u,
  one $ RanSideEffect u u u,
  ba $ AccumulatingAffectedConstraints ] where
    u = error "allStages"
    one x = [x]
    ba f = [f Before, f After]

cliDebugger :: (Ord constraint) => IO (Debugger constraint -> Stage constraint -> IO ())
cliDebugger = do
  ref <- newIORef False
  breaksRef <- newIORef (S.fromList stages)
  return $ \d stage -> flip runDM breaksRef $ do
    let shown = showStage stage
    ss <- getBreaks
    if (not $ S.member shown ss) then return () else do
    liftIO $ do
      b <- readIORef ref
      when (not b) $ putStrLn "Type 'help' to get a list of commands."
      writeIORef ref True
      putStrLn (showStage stage)
      putStrLn $ "assignments: " ++ show (length (assignments d)) ++ "\tinstance constraints: " ++ show (S.size (S.filter (isJust . snd) (outstandingConstraints d)))
    input d
    return ()

input d = do
  x <- liftIO getLine
  case x of
    ('h':_) {- help -} -> do
      liftIO $ putStrLn "break, nobreak, assignments"
      input d
    ('b':_) {- break -} -> breaks True >> input d
    ('n':_) {- nobreak -} -> breaks False >> input d
    ('a':_) {- assignments -} -> do
      liftIO . putStrLn . show . map fst . assignments $ d
      input d
    "" {- continue -} -> return ()

    _ -> liftIO (putStrLn "I don't understand. Try 'help'") >> input d

breaks :: Bool -> DM ()
breaks b = do
  ss <- getBreaks
  join $ liftIO $ do
    mapM_ (\(i, s) -> putStrLn $ show i ++ ": " ++ s ++ (if S.member s ss then " (*)" else "")) (zip [0..] stages)
    l <- getLine
    if l == ""
      then return (return ())
      else
        if l == "*"
          then return (modifyBreaks (const $ if b then S.fromList stages else S.empty))
          else
            case readMay l of
              Nothing -> do
                putStrLn "Please enter a number."
                return (breaks b)
              Just i ->
                case stages `atMay` i of
                  Nothing -> putStrLn "Out of range." >> return (breaks b)
                  Just s -> return $ do
                              modifyBreaks ((if b then S.insert else S.delete) s)
                              breaks b

newtype DM a = DM (ReaderT (IORef (S.Set String)) IO a)
  deriving (Applicative, Functor, Monad, MonadIO)

getBreaks = DM $ do
  ref <- ask
  liftIO $ readIORef ref

type Breaks = S.Set String

modifyBreaks :: (Breaks -> Breaks) -> DM ()
modifyBreaks mod = DM $ do
  ref <- ask
  liftIO $ modifyIORef ref mod

runDM (DM m) ref = runReaderT m ref
