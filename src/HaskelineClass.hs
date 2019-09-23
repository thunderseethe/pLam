{-# LANGUAGE FlexibleInstances, GeneralizedNewtypeDeriving, InstanceSigs, MultiParamTypeClasses, UndecidableInstances #-}
module HaskelineClass where

import Control.Monad.Trans.Except
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.State.Strict

import qualified System.Console.Haskeline as H
import System.Console.Haskeline.MonadException

newtype HaskelineT m a = HaskelineT { unHaskeline :: H.InputT m a }
  deriving (Functor, Applicative, Monad, MonadIO, MonadException, MonadTrans, MonadHaskeline)

runHaskelineT :: MonadException m => H.Settings m -> HaskelineT m a -> m a
runHaskelineT settings = H.runInputT settings . unHaskeline

class MonadException m => MonadHaskeline m where
  getInputLine :: String -> m (Maybe String)
  getInputChar :: String -> m (Maybe Char)
  outputStr :: String -> m ()
  outputStrLn :: String -> m ()

instance (MonadException m) => MonadException (ExceptT e m) where
    controlIO :: (RunIO (ExceptT e m) -> IO (ExceptT e m a)) -> ExceptT e m a
    controlIO f = ExceptT $ controlIO $ \(RunIO run) -> let
        run' = RunIO (fmap ExceptT . run . runExceptT)
        in runExceptT <$> f run'

instance MonadException m => MonadHaskeline (H.InputT m) where
  getInputLine = H.getInputLine
  getInputChar = H.getInputChar
  outputStr = H.outputStr
  outputStrLn = H.outputStrLn

instance MonadState s m => MonadState s (HaskelineT m) where
  get = lift get
  put = lift . put
  state = lift . state

instance MonadHaskeline m => MonadHaskeline (StateT s m) where
  getInputLine = lift . getInputLine
  getInputChar = lift . getInputChar
  outputStr = lift . outputStr
  outputStrLn = lift . outputStrLn

instance MonadHaskeline m => MonadHaskeline (ExceptT e m) where
  getInputLine = lift . getInputLine
  getInputChar = lift . getInputChar
  outputStr = lift . outputStr
  outputStrLn = lift . outputStrLn