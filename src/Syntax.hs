module Syntax where

import Control.Monad.State
import Text.Parsec hiding (State)

type Variable = String

data Expression = Variable Variable
                | Abstraction Variable Expression
                | Application Expression Expression
                deriving (Eq)

instance Show Expression where
    show (Variable v)        = v
    show (Abstraction n t)   = "λ" ++ n ++ "." ++ show t
    show (Application t1 t2) = "(" ++ show t1 ++ " " ++ show t2 ++ ")"

data Command = Define Variable Expression
             | Execute Expression
             | Import String
             | Review String
             | Comment String
             deriving (Eq, Show)

data LCILine = Command Command
             | Expression Expression
             deriving (Eq, Show)

type Environment = [(Variable, Expression)]

type Program = State Environment

data Error = SyntaxError ParseError
           | UndeclaredVariable Variable
           | FatalError String

instance Show Error where
    show (SyntaxError se)        = show se
    show (UndeclaredVariable uv) = " ERROR: undeclared variable " ++ show uv ++ "\n- type \"review all\" to see all environment variables you can use\n- type \"define <variable name> = <lambda expression>\" to add new variables to environment"
    show (FatalError fe)         = show fe

type Failable = Either Error

