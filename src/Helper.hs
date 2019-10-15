{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
module Helper where

import           Evaluator
import           HaskelineClass
import           Parser
import           Reducer
import           Syntax

import           Control.Comonad.Trans.Cofree
import qualified Control.Comonad.Cofree        as CF
import           Control.Monad.State
import           Control.Monad.Except
import           Data.Functor.Foldable
import qualified Data.Map                      as Map
import           Data.Map                       ( (!?) )
import qualified Data.Text                     as Text
import qualified Data.Text.IO                  as TIO
import           Data.Text                      ( Text )
import           Formatting
import           System.Console.Haskeline
                                         hiding ( outputStrLn
                                                , outputStr
                                                , getInputLine
                                                , getInputChar
                                                )


-------------------------------------------------------------------------------------
showGlobal :: (MonadHaskeline m) => (Text, Term) -> m ()
showGlobal (n, e) =
    outputStrLn $ Text.unpack $ Text.concat ["--- ", n, " = ", printUncurried e]

printGlobal :: (MonadIO m) => (Text, Expression) -> m ()
printGlobal (n, e) =
    liftIO $ TIO.putStrLn $ Text.concat ["--- ", n, " = ", Text.pack $ show e]

removeLambda :: Text -> Text
removeLambda = Text.replace "λ" "\\"

convertEnvironmentToFile :: Environment -> Text
convertEnvironmentToFile = Map.foldrWithKey' appendEntry Text.empty
  where
    appendEntry name value accum = Text.concat
        [name, " = ", removeLambda $ printUncurried value, "\n", accum]

convertToName :: Environment -> Term -> Maybe Text
convertToName env term = Map.foldrWithKey
    findAlphaEquiv
    (Text.pack . show <$> findNumeral term)
    env
  where
    findAlphaEquiv key val acc = if alphaEquiv val term then Just key else acc

colorOutput :: Bool -> Text -> Text
colorOutput colored =
    if colored then sformat ("\x1b[1;32m" % stext % "\x1b[0m") else id

convertToNames' :: Bool -> Environment -> Term -> Text
convertToNames' colored env = go False False (LambdaVar "")
  where
    go :: Bool -> Bool -> LambdaVar -> Term -> Text
    go redexFound redexVarFind redexVar term = case convertToName env term of
        Just name -> colorOutput colored name
        Nothing   -> case project term of
            v@(LambdaVar name) :< Var _ -> if redexVarFind && v == redexVar
                then sformat ("\x1b[0;31m" % stext % "\x1b[0m") name
                else name

            LambdaVar v :< Abs e -> sformat
                lambdaFmtStr
                v
                (go redexFound redexVarFind redexVar e)

            _ :< App abst@(v@(LambdaVar name) CF.:< Abs e) n -> if redexFound
                then sformat appFmtStr
                             (go True False redexVar abst)
                             (go True False redexVar n)
                else sformat substFmtStr
                             name
                             (go True True v e)
                             (go True False redexVar n)

            _ :< App m n -> sformat appFmtStr
                                    (go redexFound redexVarFind redexVar m)
                                    (go redexFound redexVarFind redexVar n)

    lambdaFmtStr :: Format r (Text -> Text -> r)
    lambdaFmtStr = if colored
        then
            "\x1b[0;36m(\x1b[1;36mλ\x1b[0m"
            % stext
            % "\x1b[1;36m.\x1b[0m "
            % stext
            % "\x1b[0;36m)\x1b[0m"
        else "(λ" % stext % ". " % stext % ")"

    afs fmt = if colored
        then "\x1b[0;35m(\x1b[0m" % fmt % " " % stext % "\x1b[0;35m)\x1b[0m"
        else "(" % fmt % " " % stext % ")"

    appFmtStr :: Format r (Text -> Text -> r)
    appFmtStr = afs stext

    substFmtStr :: Format r (Text -> Text -> Text -> r)
    substFmtStr = afs lambdaFmtStr

convertToNames :: Environment -> Term -> Text
convertToNames = convertToNames' False
--------------------------------------------------------------------------------------------------
-- same as convertToNames, but with additional coloring meant for beta nf terms mostly 
---------------------------------------------------------------------------------------------------
convertToNamesResult :: Environment -> Term -> Text
convertToNamesResult = convertToNames' True

-----------------------------------------------------------------------------------------------------------
isDefined :: Environment -> Text -> Bool
isDefined = flip Map.member

reviewVariable :: Environment -> Text -> Maybe Text
reviewVariable env key = printUncurried <$> (env !? key)
-------------------------------------------------------------------------------------

-------------------------------------------------------------------------------------
-- construct Expression for numeral from num and check equality
---- before was checking alpha equivalence, but we restrict it now
---- numerals will always be with same variables
---- reduces execution time, esspecially for Churchs
findChurch :: Term -> Maybe Text
findChurch term = case term of
    _ CF.:< Abs (_ CF.:< Abs body) -> Text.pack . show <$> isChurchBody body
    _                              -> Nothing
  where
    isChurchBody :: Term -> Maybe Int
    isChurchBody = para alga

    alga :: Base Term (Term, Maybe Int) -> Maybe Int
    alga = \case
        _ :< Var i                -> if i == 0 then Just 0 else Nothing
        -- If we see any Abs this is not a church numeral
        _ :< Abs _                -> Nothing
        _ :< App (varl, _) (_, n) -> case project varl of
            _ :< Var f -> if f == 1 then (+ 1) <$> n else Nothing
            _          -> Nothing

findBinary :: Term -> Maybe Text
findBinary term = go 0
  where
    -- Stop recursing at this stage
    go 2047 = Nothing
    go num  = if term == evalState (betaNF (createBinary num)) 0
        then Just $ sformat ("0b" % bin) num
        else go (num + 1)

findNumeral :: Term -> Maybe Text
findNumeral = findChurch

-------------------------------------------------------------------------------------
goodCounter :: Int -> Int -> Int
goodCounter num rednum | rednum == 0 = num
                       | otherwise   = rednum

-------------------------------------------------------------------------------------
showResult :: (MonadState Environment m) => Term -> Int -> m Text
showResult term num =
    let (term', nf) = runState (betaNF term) 0
        count       = goodCounter num nf
    in  showSummary term' count

showProgResult :: (MonadState Environment m) => Term -> Int -> m Text
showProgResult = showResult

showSummary :: (MonadState Environment m) => Term -> Int -> m Text
showSummary term count = do
    env <- get
    return $ sformat
        ("\x1b[1;32m|> \x1b[0;33mreductions count               : \x1b[1;31m"
        % int
        % "\n\x1b[1;32m|> \x1b[0;33muncurried \x1b[1;33mβ-normal\x1b[0;33m form        : \x1b[0m"
        % stext
        % "\n\x1b[1;32m|> \x1b[0;33mcurried (partial) \x1b[1;33mα-equivalent\x1b[0;33m : \x1b[0m"
        % stext
        )
        count
        (printUncurried term)
        (convertToNamesResult env term)

printUncurried :: Term -> Text
printUncurried = histo alga
  where
    alga :: Base Term (CF.Cofree (Base Term) Text) -> Text
    alga = \case
        LambdaVar lv :< Var _ -> lv
        LambdaVar arg :< Abs (outtermostOutput CF.:< body) ->
            Text.concat ["(λ", arg, combineAbsArgs outtermostOutput body, ")"]
        _ :< App (e1 CF.:< _) (e2 CF.:< rightTerm) ->
            Text.concat [e1, " ", paranRightAssocApps e2 rightTerm]

    combineAbsArgs :: Text -> Base Term (CF.Cofree (Base Term) Text) -> Text
    combineAbsArgs output body = case body of
        LambdaVar arg :< Abs (output' CF.:< body') ->
            Text.concat [" ", arg, combineAbsArgs output' body']
        _ -> Text.concat [". ", output]

    paranRightAssocApps
        :: Text -> Base Term (CF.Cofree (Base Term) Text) -> Text
    paranRightAssocApps output term = case term of
        _ :< App (e1 CF.:< _) (e2 CF.:< term') ->
            Text.concat ["(", e1, " ", paranRightAssocApps e2 term', ")"]
        _ -> output

-- Base Term (Cofree (Base Term) Text) = LambdaVar :< DeBruijnF (Cofree (Base Term) Text)
-- (Text CF.:< Base Term (Cofree (Base Term) Text))
-- CofreeF DeBruijnF LambdaVar (Cofree (CofreeF DeBruijnF LambdaVar) Text)

manualReduce
    :: (MonadIO m, MonadException m, MonadHaskeline m, MonadState Environment m)
    => Term
    -> Int
    -> m ()
manualReduce term num = do
    env <- get
    outputStrLn $ Text.unpack $ sformat
        ("\x1b[1;35m#" % int % ":\x1b[0m" % stext)
        num
        (convertToNames env term)
    line <- getInputLine
        "\x1b[1;33mNext step?\x1b[0m [Y/n/f] (f: finish all remaining steps): "
    case line of
        Just "n" -> showSummary term num >>= outputStrLn . Text.unpack
        Just "f" -> autoReduce term num
        _        -> if hasBetaRedex term
            then uncurry manualReduce $ runState (betaReduction term) num
            else showResult term num >>= outputStrLn . Text.unpack


autoReduce'
    :: (MonadState Environment m) => (String -> m ()) -> Term -> Int -> m ()
autoReduce' printOp term num = do
    env <- get
    printOp $ Text.unpack $ sformat
        ("\x1b[1;35m#" % int % ":\x1b[0m" % stext)
        num
        (convertToNames env term)
    if hasBetaRedex term
        then uncurry (autoReduce' printOp) $ runState (betaReduction term) num
        else printOp . Text.unpack =<< showResult term num


autoReduce
    :: (MonadIO m, MonadHaskeline m, MonadState Environment m)
    => Term
    -> Int
    -> m ()
autoReduce = autoReduce' outputStrLn

autoProgReduce :: (MonadIO m, MonadState Environment m) => Term -> Int -> m ()
autoProgReduce = autoReduce' (liftIO . putStrLn)

-------------------------------------------------------------------------------------
decideEvaluate :: Expression -> Eval Environment
decideEvaluate e =
    handleOutput e (\x n -> showProgResult x n >>= outputStrLn . Text.unpack)

selectStepOption :: Expression -> Eval Environment
selectStepOption e = do
    term <- evalExp e
    op   <-
        getInputLine
            "\x1b[1;33mChoose stepping option\x1b[0m ([default] a: auto all, m: manual step-by-step): "
    env <- get
    opFn op term 0
    return env
  where
    opFn = \case
        Just "a" -> autoReduce
        Just "m" -> manualReduce
        _        -> autoReduce

decideEvaluateProg :: Expression -> Eval Environment
decideEvaluateProg e = handleOutput
    e
    (\term n -> showProgResult term n >>= (liftIO . TIO.putStrLn))

handleOutput
    :: (MonadState Environment m, MonadError Error m)
    => Expression
    -> (Term -> Int -> m ())
    -> m Environment
handleOutput e action = do
    term <- evalExp e
    env  <- get
    action term 0
    return env
