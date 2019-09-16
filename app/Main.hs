{-# LANGUAGE LambdaCase #-}
import           Config
import           Evaluator
import           HaskelineClass
import           Helper
import           Parser
import           Reducer
import           Syntax

import           Control.Applicative
import           Control.Monad
import           Control.Monad.State
import           Control.Monad.Except           ( runExceptT
                                                , catchError
                                                )
import           Debug.Trace
import           Data.Bifunctor
import           Data.Maybe
import           System.IO                      ( hFlush
                                                , stdout
                                                , hPutStrLn
                                                , hClose
                                                , openFile
                                                , IOMode(WriteMode)
                                                )
import           System.Exit
import           System.Console.Haskeline
                                         hiding ( getInputLine
                                                , getInputChar
                                                , outputStr
                                                , outputStrLn
                                                )
import           System.Environment
import           System.Directory               ( doesFileExist )
import           Text.Parsec


version = "2.2.0"
heading =
    "\x1b[1;36m\
\         _\n\
\        | |\n\
\    ____| |   ___  __  __\n\
\    | _ \\ |__| _ \\|  \\/  |\n\
\    |  _/____|____\\_\\__/_| \x1b[32mv"
        ++ version
        ++ "\n\
\    \x1b[1;36m|_| \x1b[0mpure λ-calculus interpreter\n\
\   \x1b[1;36m=================================\n"
-------------------------------------------------------------------------------------

execJustProg :: Eval [String] -> Eval Environment
execJustProg = (=<<) go
  where
    go = \case
        []          -> get
        (line : ls) -> readLine line >>= handle ls

    handle :: [String] -> Command -> Eval Environment
    handle ls = \case
        Import f -> do
            executeFile f >>= put
            execJustProg (return ls)
        Define v e -> do
            evalDefine v e
            execJustProg (return ls)
        Evaluate det cbv e -> decideEvaluateProg det cbv e
        Review r           -> do
            env <- get
            case r of
                "all" -> do
                    liftIO $ putStrLn " ENVIRONMENT:"
                    mapM_ printGlobal env
                _ ->
                    liftIO
                        $ putStrLn
                              (  "--- definition of "
                              ++ show r
                              ++ ": "
                              ++ fromMaybe "none" (reviewVariable env r)
                              )
            go ls
        Print s -> do
            liftIO $ putStrLn s
            go ls
        _ -> go ls

execAll :: Eval [String] -> Eval Environment
execAll m = m >>= go
  where
    go :: [String] -> Eval Environment
    go = \case
        []          -> get
        (line : ls) -> readLine line >>= handle ls

    handle ls = \case
        Import f   -> executeFile f >> execAll (return ls)
        Define v e -> do
            res <- evalDefine v e
            go ls
        Evaluate det cbv rawE -> decideEvaluate det cbv rawE
        Print s               -> do
            outputStrLn s
            go ls
        _ -> go ls

executeFile :: String -> Eval Environment
executeFile f =
    let contents = liftIO $ readFile (importPath ++ f ++ ".plam")
    in  execAll $ lines <$> contents

execute :: Eval String -> Eval Environment
execute m = handle =<< (readLine =<< m)
  where
    handle :: Command -> Eval Environment
    handle = \case
        Define v e         -> evalDefine v e >>= const get
        Evaluate det cbv e -> decideEvaluate det cbv e
        Import f           -> executeFile f
        Export f           -> do
            fileExists <- liftIO $ doesFileExist (importPath ++ f ++ ".plam")
            env        <- get
            if not fileExists
                then do
                    outFile <- liftIO
                        $ openFile (importPath ++ f ++ ".plam") WriteMode
                    liftIO $ mapM_ (saveGlobal outFile) (reverse env)
                    liftIO $ hClose outFile
                    outputStrLn
                        ("--- successfully exported to import/" ++ f ++ ".plam")
                else outputStrLn
                    ("--- export failed : " ++ f ++ " already exists")
            return env
        Review r -> do
            env <- get
            case r of
                "all" -> outputStrLn " ENVIRONMENT:" >> mapM_ showGlobal env
                _ ->
                    outputStrLn
                        (  "--- definition of "
                        ++ show r
                        ++ ": "
                        ++ fromMaybe "none" (reviewVariable env r)
                        )
            return env
        Run   f -> executeFile f
        Print s -> do
            outputStrLn s
            outputStrLn
                "(NOTE: it makes more sense to use a comment line (starts with double '-' than :print command when you are in interactive mode)"
            get
        Comment c -> get

-------------------------------------------------------------------------------------
isplam :: String -> Bool
isplam (c : cs) | (length cs == 5) && (cs == ".plam") = True
                | length cs < 5                       = False
                | otherwise                           = isplam cs

-------------------------------------------------------------------------------------
                   -- MAIN with Read-Evaluate-Print Loop --
-------------------------------------------------------------------------------------
repl :: Eval ()
repl = do
    mline <- getInputLine "\x1b[1;36mpLam>\x1b[0m "
    maybe (return ()) handleLine mline
  where
    handleLine :: String -> Eval ()
    handleLine line = if line == ":quit" || line == ":q"
        then outputStrLn "\x1b[1;32mGoodbye!\x1b[0m"
        else do
            void (execute $ return line) `catchError` (liftIO . print)
            repl

decideRun :: [String] -> IO (Either Error (), Environment)
decideRun [] = do
    putStrLn heading
    runEvaluator repl
decideRun [arg]
    | arg == ":nohead" = runEvaluator repl
    | isplam arg = do
        content <- readFile arg
        let exprs = lines content
        output <- runEvaluator $ execJustProg (return exprs)
        putStrLn "\x1b[1;32mDone.\x1b[0m"
        return $ first (second $ const ()) output
decideRun _ = do
    putStrLn "\x1b[31mignoring argument(s)...\x1b[0m"
    putStrLn heading
    runEvaluator repl

runEvaluator :: Eval a -> IO (Either Error a, Environment)
runEvaluator = runEvalToIO [] settings

settings :: (MonadIO m) => Settings m
settings = defaultSettings { historyFile = Just ".plam-history" }

main :: IO ()
main = do
    args     <- getArgs
    (err, _) <- decideRun args
    either print (\_ -> return ()) err

------- REPL Debug Functions -----
par input =
    debruijnify $ either undefined id $ parse parseSingleton "parser" input
