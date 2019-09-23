{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
module Helper where

import           Evaluator
import           HaskelineClass
import           Parser
import           Reducer
import           Syntax

import           Control.Applicative
import           Control.Comonad.Cofree
import           Control.Monad.State
import           Control.Monad.Except
import           System.IO                      ( Handle
                                                , hPutStrLn
                                                )
import           System.Console.Haskeline
                                         hiding ( outputStrLn
                                                , outputStr
                                                , getInputLine
                                                , getInputChar
                                                )
import           Data.Functor.Foldable
import           Data.Maybe


-------------------------------------------------------------------------------------
showGlobal :: (MonadHaskeline m) => (String, DeBruijn) -> m ()
showGlobal (n, e) = outputStrLn ("--- " ++ show n ++ " = " ++ printUncurried e)

printGlobal :: (MonadIO m) => (String, Expression) -> m ()
printGlobal (n, e) = (liftIO . putStrLn) ("--- " ++ show n ++ " = " ++ show e)

removeLambda :: String -> String
removeLambda = map repl
  where
    repl 'λ' = '\\'
    repl c   = c

saveGlobal :: (MonadIO m) => Handle -> (String, DeBruijn) -> m ()
saveGlobal h (n, e) =
    liftIO $ hPutStrLn h (n ++ " = " ++ removeLambda (printUncurried e))

convertToName :: Environment -> DeBruijn -> Maybe String
convertToName [] term = show <$> findNumeral term
convertToName ((v, e) : rest) ex | alphaEquiv e ex = Just v
                                 | otherwise       = convertToName rest ex

convertToNames' :: Bool -> Environment -> DeBruijn -> String
convertToNames' colored env = go False False (LambdaVar ".")
  where
    colorOutput =
        if colored then (\a -> "\x1b[1;32m" ++ a ++ "\x1b[0m") else id

    go :: Bool -> Bool -> LambdaVar -> DeBruijn -> String
    go redexFound redexVarFind redexVar term = case unfix term of
        Var _ v -> if redexVarFind && v == redexVar
            then "\x1b[0;31m" ++ show v ++ "\x1b[0m"
            else show v
        redex@(App (Fix (Abs e v)) n) -> if redexFound
            then
                let redex1 = convertToName env (Fix redex)
                in  fromMaybe
                        (  "("
                        ++ go True False redexVar (Fix $ Abs e v)
                        ++ " "
                        ++ go True False redexVar n
                        ++ ")"
                        )
                        redex1
            else
                "\x1b[0;35m(\x1b[1;36m(λ\x1b[1;31m"
                ++ show v
                ++ "\x1b[1;36m.\x1b[0;36m "
                ++ go True True v e
                ++ "\x1b[1;36m) \x1b[1;32m"
                ++ go True False redexVar n
                ++ "\x1b[0;35m)\x1b[0m"
        appl@(App m n) ->
            let app1 = convertToName env (Fix appl)
            in  maybe
                    (  (if colored then "\x1b[0;35m(\x1b[0m" else "(")
                    ++ go redexFound redexVarFind redexVar m
                    ++ " "
                    ++ go redexFound redexVarFind redexVar n
                    ++ (if colored then "\x1b[0;35m)\x1b[0m" else ")")
                    )
                    colorOutput
                    app1
        abst@(Abs e v) ->
            let abs1 = convertToName env (Fix abst)
            in  maybe
                    ((if colored then "\x1b[0;36m(\x1b[1;36mλ\x1b[0m" else "(λ")
                    ++ show v
                    ++ (if colored then "\x1b[1;36m.\x1b[0m " else ". ")
                    ++ go redexFound redexVarFind redexVar e
                    ++ (if colored then "\x1b[0;36m)\x1b[0m" else ")")
                    )
                    colorOutput
                    abs1

convertToNames :: Environment -> DeBruijn -> String
convertToNames = convertToNames' False
--------------------------------------------------------------------------------------------------
-- same as convertToNames, but with additional coloring meant for beta nf terms mostly 
---------------------------------------------------------------------------------------------------
convertToNamesResult :: Environment -> DeBruijn -> String
convertToNamesResult = convertToNames' True

-----------------------------------------------------------------------------------------------------------
isDefined :: Environment -> String -> Bool
isDefined [] _ = False
isDefined ((v, _) : rest) s | v == s    = True
                            | otherwise = isDefined rest s

reviewVariable :: Environment -> String -> Maybe String
reviewVariable [] _ = Nothing
reviewVariable ((v, e) : rest) variable
    | v == variable = Just $ show e
    | otherwise     = reviewVariable rest variable
-------------------------------------------------------------------------------------

-------------------------------------------------------------------------------------
-- construct Expression for numeral from num and check equality
---- before was checking alpha equivalence, but we restrict it now
---- numerals will always be with same variables
---- reduces execution time, esspecially for Churchs
findChurch :: DeBruijn -> Maybe LambdaVar
findChurch term = case term of
    -- A church numeral starts with exactly two abstractions
    Fix (Abs (Fix (Abs body _)) _) -> LambdaVar . show <$> isChurchBody body
    _                              -> Nothing
  where
    isChurchBody :: DeBruijn -> Maybe Int
    isChurchBody = para alga

    alga :: Base DeBruijn (DeBruijn, Maybe Int) -> Maybe Int
    alga = \case
        Var i _ -> if i == 0 then Just 0 else Nothing
        -- If we see any abs this is not a church numeral
        Abs _ _ -> Nothing
        App (Fix (Var f _), _) (_, n) ->
            if f == 1 then (+ 1) <$> n else Nothing
        _ -> Nothing

--findChurch' :: DeBruijn -> Maybe String
--findChurch' term = go 0
--  where
--    go num | term == createChurch num = Just $ show num
--           | num == 199               = Nothing
--           | otherwise                = go (num + 1)

findBinary :: DeBruijn -> Maybe LambdaVar
findBinary term = go 0
  where
    -- Stop recursing at this stage
    go 2047 = Nothing
    go num  = if term == evalState (betaNF None (createBinary num)) 0
        then Just . LambdaVar $ show num ++ "b"
        else go (num + 1)

findNumeral :: DeBruijn -> Maybe LambdaVar
findNumeral term = findChurch term <|> findBinary term

-------------------------------------------------------------------------------------
goodCounter :: Int -> Int -> Int
goodCounter num rednum | rednum == 0 = num
                       | otherwise   = rednum

-------------------------------------------------------------------------------------
showResult
    :: (MonadState Environment m)
    => EvaluateOption
    -> DeBruijn
    -> Int
    -> m String
showResult evop term num =
    let (term', nf) = runState (betaNF evop term) 0
        count       = goodCounter num nf
    in  showSummary term' count

showProgResult
    :: (MonadState Environment m)
    => EvaluateOption
    -> DeBruijn
    -> Int
    -> m String
showProgResult = showResult

showSummary :: (MonadState Environment m) => DeBruijn -> Int -> m String
showSummary term count = do
    env <- get
    return
        $  "\x1b[1;32m|> \x1b[0;33mreductions count               : \x1b[1;31m"
        ++ show count
        ++ "\n"
        ++ "\x1b[1;32m|> \x1b[0;33muncurried \x1b[1;33mβ-normal\x1b[0;33m form        : \x1b[0m"
        ++ printUncurried term
        ++ "\n"
        ++ "\x1b[1;32m|> \x1b[0;33mcurried (partial) \x1b[1;33mα-equivalent\x1b[0;33m : \x1b[0m"
        ++ convertToNamesResult env term

printUncurried :: DeBruijn -> String
printUncurried = histo alga
  where
    alga :: Base DeBruijn (Cofree (Base DeBruijn) String) -> String
    alga = \case
        Var _ lv -> show lv
        Abs (outtermostOutput :< body) arg ->
            "(λ" ++ show arg ++ combineAbsArgs outtermostOutput body ++ ")"
        App (e1 :< _) (e2 :< rightTerm) ->
            e1 ++ " " ++ paranRightAssocApps e2 rightTerm


    combineAbsArgs output body = case body of
        Abs (output' :< body') arg ->
            " " ++ show arg ++ combineAbsArgs output' body'
        _ -> "." ++ output

    paranRightAssocApps output term = case term of
        App (e1 :< _) (e2 :< term') ->
            "(" ++ e1 ++ " " ++ paranRightAssocApps e2 term' ++ ")"
        _ -> output



manualReduce
    :: (MonadIO m, MonadException m, MonadHaskeline m, MonadState Environment m)
    => EvaluateOption
    -> DeBruijn
    -> Int
    -> m ()
manualReduce evop term num = do
    env <- get
    outputStrLn
        ("\x1b[1;35m#" ++ show num ++ ":\x1b[0m" ++ convertToNames env term)
    line <- getInputLine
        "\x1b[1;33mNext step?\x1b[0m [Y/n/f] (f: finish all remaining steps): "
    case line of
        Just "n" -> showSummary term num >>= outputStrLn
        Just "f" -> autoReduce evop term num
        _        -> if hasBetaRedex term
            then uncurry (manualReduce evop)
                $ runState (betaReduction evop term) num
            else showResult evop term num >>= outputStrLn


autoReduce'
    :: (MonadState Environment m)
    => (String -> m ())
    -> EvaluateOption
    -> DeBruijn
    -> Int
    -> m ()
autoReduce' printOp evop term num = do
    env <- get
    printOp ("\x1b[1;35m#" ++ show num ++ ":\x1b[0m" ++ convertToNames env term)
    if hasBetaRedex term
        then uncurry (autoReduce' printOp evop)
            $ runState (betaReduction evop term) num
        else printOp =<< showResult evop term num


autoReduce
    :: (MonadIO m, MonadHaskeline m, MonadState Environment m)
    => EvaluateOption
    -> DeBruijn
    -> Int
    -> m ()
autoReduce = autoReduce' outputStrLn

autoProgReduce
    :: (MonadIO m, MonadState Environment m)
    => EvaluateOption
    -> DeBruijn
    -> Int
    -> m ()
autoProgReduce = autoReduce' (liftIO . putStrLn)

-------------------------------------------------------------------------------------
decideEvaluate
    :: EvaluateOption -> EvaluateOption -> Expression -> Eval Environment
decideEvaluate det cbt e = case (det, cbt) of
    (None, CallByValue) -> handleOutput
        (e, CallByValue)
        (\c x n -> showProgResult c x n >>= outputStrLn)
    (Detailed, None) -> selectStepOption None e
    (Detailed, CallByValue) -> selectStepOption CallByValue e
    _ -> handleOutput (e, None)
                      (\c x n -> showProgResult c x n >>= outputStrLn)

selectStepOption :: EvaluateOption -> Expression -> Eval Environment
selectStepOption cbt e = do
    term <- evalExp e
    op   <-
        getInputLine
            "\x1b[1;33mChoose stepping option\x1b[0m ([default] a: auto all, m: manual step-by-step): "
    env <- get
    opFn op cbt term 0
    return env
  where
    opFn = \case
        Just "a" -> autoReduce
        Just "m" -> manualReduce
        _        -> autoReduce

decideEvaluateProg
    :: EvaluateOption -> EvaluateOption -> Expression -> Eval Environment
decideEvaluateProg det cbt e = case (det, cbt) of
    (Detailed, None       ) -> handleOutput (e, None) autoProgReduce
    (None    , CallByValue) -> handleOutput
        (e, CallByValue)
        (\cbv term n -> showProgResult cbv term n >>= (liftIO . putStrLn))
    (Detailed, CallByValue) -> handleOutput (e, CallByValue) autoProgReduce
    _                       -> handleOutput
        (e, None)
        (\cbv term n -> showProgResult cbv term n >>= (liftIO . putStrLn))

handleOutput
    :: (MonadState Environment m, MonadError Error m)
    => (Expression, EvaluateOption)
    -> (EvaluateOption -> DeBruijn -> Int -> m ())
    -> m Environment
handleOutput (e, cbt) action = do
    term <- evalExp e
    env  <- get
    action cbt term 0
    return env
