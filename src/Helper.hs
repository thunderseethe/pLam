{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
module Helper where

import           Evaluator
import           HaskelineClass
import           Parser
import           Reducer
import           Syntax

import           Control.Monad.State
import           Control.Monad.Except
import           System.IO                      ( hFlush
                                                , stdout
                                                , Handle
                                                , hPutStrLn
                                                )
import           Debug.Trace
import           System.Console.Haskeline
                                         hiding ( outputStrLn
                                                , outputStr
                                                , getInputLine
                                                , getInputChar
                                                )
import           Data.Maybe


-------------------------------------------------------------------------------------
showGlobal :: (MonadHaskeline m) => (String, Expression) -> m ()
showGlobal (n, e) = outputStrLn ("--- " ++ show n ++ " = " ++ show e)

printGlobal :: (MonadIO m) => (String, Expression) -> m ()
printGlobal (n, e) = (liftIO . putStrLn) ("--- " ++ show n ++ " = " ++ show e)

removeLambda :: String -> String
removeLambda = map repl
  where
    repl 'λ' = '\\'
    repl c   = c

saveGlobal :: Handle -> (String, Expression) -> IO ()
saveGlobal h (n, e) = hPutStrLn h (n ++ " = " ++ removeLambda (show e))

convertToName :: Environment -> Expression -> Maybe String
convertToName [] exp = findNumeral exp
convertToName ((v, e) : rest) ex | alphaEquiv e ex = Just v
                                 | otherwise       = convertToName rest ex

convertToNames'
    :: (String -> String)
    -> Environment
    -> Expression
    -> String
convertToNames' modifyOutput env = go False False (LambdaVar '.' 0)
  where
    go redexFound redexVarFind redexVar = \case
        Variable v -> if redexVarFind && v == redexVar
            then "\x1b[0;31m" ++ show v ++ "\x1b[0m"
            else show v
        redex@(Application (Abstraction v e) n) -> if redexFound
            then
                let redex1 = convertToName env redex
                    defaultStr =
                        "("
                            ++ go
                                               True
                                               False
                                               redexVar
                                               (Abstraction v e)
                            ++ " "
                            ++ go
                                               True
                                               False
                                               redexVar
                                               n
                            ++ ")"
                in  fromMaybe defaultStr redex1
            else
                "\x1b[0;35m(\x1b[1;36m(λ\x1b[1;31m"
                ++ show v
                ++ "\x1b[1;36m.\x1b[0;36m "
                ++ go True True v e
                ++ "\x1b[1;36m) \x1b[1;32m"
                ++ go True False redexVar n
                ++ "\x1b[0;35m)\x1b[0m"
        app@(Application m n) ->
            let app1 = convertToName env app
            in  maybe
                    (  "("
                    ++ go
                                       redexFound
                                       redexVarFind
                                       redexVar
                                       m
                    ++ " "
                    ++ go 
                                       redexFound
                                       redexVarFind
                                       redexVar
                                       n
                    ++ ")"
                    )
                    modifyOutput
                    app1
        abs@(Abstraction v e) ->
            let abs1 = convertToName env abs
            in  maybe
                    (  "(λ"
                    ++ show v
                    ++ ". "
                    ++ go
                                       redexFound
                                       redexVarFind
                                       redexVar
                                       e
                    ++ ")"
                    )
                    modifyOutput
                    abs1

convertToNames = convertToNames' id
convertToNamesResult = convertToNames' (\a -> "\x1b[1;32m" ++ a ++ "\x1b[0m")
-- same as convertToNames, but with additional coloring meant for beta nf terms mostly 
---------------------------------------------------------------------------------------------------
--convertToNamesResult
--    :: Bool -> Bool -> Expression -> Environment -> Expression -> String
--convertToNamesResult redexFound redexVarFind redexVar env (Variable v) =
--    if redexVarFind && Variable v == redexVar
--        then "\x1b[0;31m" ++ show v ++ "\x1b[0m"
--        else show v
--convertToNamesResult redexFound redexVarFind redexVar env redex@(Application (Abstraction v e) n)
--    = if redexFound
--        then
--            let redex1 = convertToName env redex
--            in maybe ("("
--                        ++ convertToNamesResult True
--                                                False
--                                                redexVar
--                                                env
--                                                (Abstraction v e)
--
--                        ++ " "
--                        ++ convertToNamesResult True False redexVar env n
--                        ++ ")") id redex1
--        else
--            "\x1b[0;35m(\x1b[1;36m(λ\x1b[1;31m"
--            ++ show v
--            ++ "\x1b[1;36m.\x1b[0;36m "
--            ++ convertToNamesResult True True (Variable v) env e
--            ++ "\x1b[1;36m) \x1b[1;32m"
--            ++ convertToNamesResult True False redexVar env n
--            ++ "\x1b[0;35m)\x1b[0m"
--convertToNamesResult redexFound redexVarFind redexVar env app@(Application m n)
--    =
--        let app1 = convertToName env app
--        in maybe
--                ("\x1b[0;35m(\x1b[0m"
--                    ++ convertToNamesResult redexFound
--                                            redexVarFind
--                                            redexVar
--                                            env
--                                            m
--                    ++ " "
--                    ++ convertToNamesResult redexFound
--                                            redexVarFind
--                                            redexVar
--                                            env
--                                            n
--                    ++ "\x1b[0;35m)\x1b[0m") (\a -> "\x1b[1;32m" ++ a ++ "\x1b[0m") app1
--convertToNamesResult redexFound redexVarFind redexVar env abs@(Abstraction v e)
--    = let abs1 = convertToName env abs
--      in maybe ("\x1b[0;36m(\x1b[1;36mλ\x1b[0m"
--                    ++ show v
--                    ++ "\x1b[1;36m.\x1b[0m "
--                    ++ convertToNamesResult redexFound
--                                            redexVarFind
--                                            redexVar
--                                            env
--                                            e
--                    ++ "\x1b[0;36m)\x1b[0m") (\a -> "\x1b[1;32m" ++ a ++ "\x1b[0m") abs1

-----------------------------------------------------------------------------------------------------------
isDefined :: Environment -> String -> Bool
isDefined [] s = False
isDefined ((v, e) : rest) s | v == s    = True
                            | otherwise = isDefined rest s

reviewVariable :: Environment -> String -> Maybe String
reviewVariable [] var = Nothing
reviewVariable ((v, e) : rest) var | v == var  = Just $ show e
                                   | otherwise = reviewVariable rest var
-------------------------------------------------------------------------------------

-------------------------------------------------------------------------------------
-- construct Expression for numeral from num and check equality
---- before was checking alpha equivalence, but we restrict it now
---- numerals will always be with same variables
---- reduces execution time, esspecially for Churchs
findChurch :: Expression -> Int -> Maybe String
findChurch exp num
    | exp == createChurch num (Variable (LambdaVar 'x' 0)) = Just $ show num
    | num == 199 = Nothing
    | otherwise  = findChurch exp (num + 1)

findBinary :: Expression -> Int -> Maybe String
findBinary exp num
    | exp == fst (betaNF None 0 (createBinary num)) = Just $ show num ++ "b"
    | num == 2047 = Nothing
    | otherwise   = findBinary exp (num + 1)

findNumeral :: Expression -> Maybe String
findNumeral abs@(Abstraction (LambdaVar v n) e) | v == 'f'  = findChurch abs 0
                                                | v == 'p'  = findBinary abs 0
                                                | otherwise = Nothing
findNumeral exp = Nothing


-------------------------------------------------------------------------------------
goodCounter :: Int -> Int -> Int
goodCounter num rednum | rednum == 0 = num
                       | otherwise   = rednum

-------------------------------------------------------------------------------------
showResult :: Environment -> EvaluateOption -> Expression -> Int -> String
showResult env evop exp num =
    let expnf = betaNF evop 0 exp
        count = goodCounter num (snd expnf)
    in  showSummary env (fst expnf) count

showProgResult :: Environment -> EvaluateOption -> Expression -> Int -> String
showProgResult env evop exp num =
    let expnf = betaNF evop 0 exp
        count = goodCounter num (snd expnf)
    in  showSummary env (fst expnf) count

showSummary :: Environment -> Expression -> Int -> String
showSummary env exp count =
    "\x1b[1;32m|> \x1b[0;33mreductions count               : \x1b[1;31m"
        ++ show count
        ++ "\n"
        ++ "\x1b[1;32m|> \x1b[0;33muncurried \x1b[1;33mβ-normal\x1b[0;33m form        : \x1b[0m"
        ++ show exp
        ++ "\n"
        ++ "\x1b[1;32m|> \x1b[0;33mcurried (partial) \x1b[1;33mα-equivalent\x1b[0;33m : \x1b[0m"
        ++ convertToNamesResult env exp


manualReduce
    :: (MonadIO m, MonadException m, MonadHaskeline m)
    => Environment
    -> EvaluateOption
    -> Expression
    -> Int
    -> m ()
manualReduce env evop exp num = do
    outputStrLn
        (  "\x1b[1;35m#"
        ++ show num
        ++ ":\x1b[0m"
        ++ convertToNames env exp
        )
    line <- getInputLine
        "\x1b[1;33mNext step?\x1b[0m [Y/n/f] (f: finish all remaining steps): "
    case line of
        Just "n" -> outputStrLn $ showSummary env exp num
        Just "f" -> autoReduce env evop exp num
        _        -> if hasBetaRedex exp
            then
                let e2b = betaReduction evop num exp
                in  uncurry (manualReduce env evop) e2b
            else outputStrLn $ showResult env evop exp num


autoReduce' :: (Monad m) => (String -> m ()) -> Environment -> EvaluateOption -> Expression -> Int -> m ()
autoReduce' printOp env evop exp num = do
    printOp
        ( "\x1b[1;35m#"
        ++ show num
        ++ ":\x1b[0m"
        ++ convertToNames env exp
        )
    if hasBetaRedex exp
        then uncurry (autoReduce' printOp env evop) $ betaReduction evop num exp
        else printOp $ showResult env evop exp num


autoReduce
    :: (MonadIO m, MonadHaskeline m)
    => Environment
    -> EvaluateOption
    -> Expression
    -> Int
    -> m ()
autoReduce = autoReduce' outputStrLn

autoProgReduce
    :: (MonadIO m) => Environment -> EvaluateOption -> Expression -> Int -> m ()
autoProgReduce = autoReduce' (liftIO . putStrLn)

-------------------------------------------------------------------------------------
decideEvaluate
    :: EvaluateOption -> EvaluateOption -> Expression -> Eval Environment
decideEvaluate det cbt e = case (det, cbt) of
        (None, None) -> handleOutput
            (e, None)
            (\e c x n -> outputStrLn $ showProgResult e c x n)
        (None, CallByValue) -> handleOutput
            (e, CallByValue)
            (\e c x n -> outputStrLn $ showProgResult e c x n)
        (Detailed, None) -> do
            exp <- evalExp e
            op  <-
                getInputLine
                    "\x1b[1;33mChoose stepping option\x1b[0m ([default] a: auto all, m: manual step-by-step): "
            env <- get
            opFn op env None exp 0
            return env
        (Detailed, CallByValue) -> do
            exp <- evalExp e
            op  <-
                getInputLine
                    "\x1b[1;33mChoose stepping option\x1b[0m ([default] a: auto all, m: manual step-by-step): "
            env <- get
            opFn op env CallByValue exp 0
            return env

opFn
    :: (MonadIO m, MonadHaskeline m)
    => Maybe String
    -> (Environment -> EvaluateOption -> Expression -> Int -> m ())
opFn = \case
    Just "a" -> autoReduce
    Just "m" -> manualReduce
    _        -> autoReduce

decideEvaluateProg
    :: EvaluateOption -> EvaluateOption -> Expression -> Eval Environment
decideEvaluateProg det cbt e = case (det, cbt) of
        (None, None) -> handleOutput
            (e, None)
            (\env cbt exp n -> liftIO $ putStrLn $ showProgResult env cbt exp n)
        (Detailed, None       ) -> handleOutput (e, None) autoProgReduce
        (None    , CallByValue) -> handleOutput
            (e, CallByValue)
            (\env cbt exp n -> liftIO $ putStrLn $ showProgResult env cbt exp n)
        (Detailed, CallByValue) -> handleOutput (e, CallByValue) autoProgReduce

handleOutput
    :: (MonadState Environment m, MonadError Error m)
    => (Expression, EvaluateOption)
    -> (Environment -> EvaluateOption -> Expression -> Int -> m ())
    -> m Environment
handleOutput (e, cbt) action = do
    exp <- evalExp e
    env <- get
    action env cbt exp 0
    return env
