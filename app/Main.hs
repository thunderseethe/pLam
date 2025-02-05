{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
import           Config
import           Evaluator
import           HaskelineClass
import           Helper
import           Parser
import           Syntax

import           Control.Monad
import           Control.Monad.State
import           Control.Monad.Except
import           Data.Bifunctor
import           Data.Functor.Identity
import qualified Data.Map                      as Map
import           Data.Maybe
import qualified Data.Text                     as Text
import           Data.Text                      ( Text )
import qualified Data.Text.IO                  as TIO
import           Formatting
import           System.Console.Haskeline       ( Settings
                                                , historyFile
                                                , defaultSettings
                                                )
import           System.Environment
import           System.Directory               ( doesFileExist )
import           Text.Megaparsec


version :: Text
version = "2.2.0"

heading :: Text
heading = Text.concat
    [ "\x1b[1;36m\
\         _\n\
\        | |\n\
\    ____| |   ___  __  __\n\
\    | _ \\ |__| _ \\|  \\/  |\n\
\    |  _/____|____\\_\\__/_| \x1b[32mv"
    , version
    , "\n\
\    \x1b[1;36m|_| \x1b[0mpure λ-calculus interpreter\n\
\   \x1b[1;36m=================================\n"
    ]
-------------------------------------------------------------------------------------

execAll :: (Text -> Eval ()) -> [Text] -> Eval ()
execAll printLn = go
  where
    go :: [Text] -> Eval ()
    go = \case
        []          -> return ()
        (line : ls) -> readLine line >>= handle ls

    handle :: [Text] -> Command -> Eval ()
    handle ls cmd = do
        case cmd of
            Import f -> do
                exprs <- importFile f
                go exprs
            Define v e            -> void $ evalDefine v e
            Evaluate _ _ rawE -> void $ decideEvaluate rawE
            Print s               -> printLn s
            _                     -> return ()
        go ls

execute :: Text -> Eval ()
execute line = do
    cmd <- readLine line
    handle cmd
  where
    handle :: Command -> Eval ()
    handle = \case
        Define v e         -> void $ evalDefine v e
        Evaluate _ _ e -> void $ decideEvaluate e
        Import f           -> do
            exprs <- importFile f
            execAll (outputStrLn . Text.unpack) exprs
        Export f -> exportFile f
        Review r -> reviewSymbol r
        Run    f -> void $ importFile f
        Print  s -> do
            outputStrLn $ Text.unpack s
            outputStrLn
                "(NOTE: it makes more sense to use a comment line (starts with double '-' than :print command when you are in interactive mode)"
        Comment _ -> return ()

-------------------------------------------------------------------------------------
                   -- Command Handlers --
-------------------------------------------------------------------------------------

filePath :: Text -> FilePath
filePath = formatToString (string % stext % ".plam") importPath

importFile :: Text -> Eval [Text]
importFile f =
    Text.lines <$> liftIO (TIO.readFile (filePath f))

exportFile :: Text -> Eval ()
exportFile f = do
    fileExists <- liftIO $ doesFileExist (filePath f)
    env <- get
    if not fileExists
        then liftIO $ TIO.writeFile (filePath f) (convertEnvironmentToFile env)
        else throwError
            (FatalError $ Text.concat ["--- export failed : " , f, " already exists"])
    outputStrLn ("--- successfully exported to " ++ filePath f)

reviewSymbol :: Text -> Eval ()
reviewSymbol r = do
    env <- get :: Eval Environment
    case r of
        "all" ->
            outputStrLn " ENVIRONMENT:" >> mapM_ showGlobal (Map.toList env)
        _ -> outputStrLn . Text.unpack $ sformat
            ("--- definition of " % stext % ": " % stext
            ) r (fromMaybe
                "none"
                (reviewVariable env r))

-------------------------------------------------------------------------------------
isplam :: Text -> Bool
isplam = Text.isSuffixOf ".plam"

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
            void (execute $ Text.pack line) `catchError` (outputStrLn . show)
            repl

decideRun :: [String] -> IO (Either Error (), Environment)
decideRun [arg]
    | arg == ":nohead" = runEvaluator repl
    | isplam (Text.pack arg) = do
        content <- TIO.readFile arg
        let exprs = Text.lines content
        output <- runEvaluator $ execAll (liftIO . TIO.putStrLn) exprs
        TIO.putStrLn "\x1b[1;32mDone.\x1b[0m"
        return $ first (second $ const ()) output
decideRun args = do
    unless (Prelude.null args)
           (TIO.putStrLn "\x1b[31mignoring argument(s)...\x1b[0m")
    TIO.putStrLn heading
    runEvaluator repl

runEvaluator :: Eval a -> IO (Either Error a, Environment)
runEvaluator = runEvalToIO Map.empty settings

settings :: (MonadIO m) => Settings m
settings = defaultSettings { historyFile = Just ".plam-history" }

main :: IO ()
main = do
    args     <- getArgs
    (err, _) <- decideRun args
    either print (\_ -> return ()) err

-- REPL specific functions --
type PureEval a = StateT Environment (ExceptT Error Identity) a

_par :: Text -> Term
_par input =
    let debruijn =
                (evalExp $ either undefined id $ parse parseExpr
                                                       "parser"
                                                       input
                ) :: PureEval Term
    in  either undefined id $ runIdentity . runExceptT $ evalStateT
            debruijn
            Map.empty
