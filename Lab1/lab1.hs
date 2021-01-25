-- DSLsofMath 2020: Assignment 1

 
data TERM v = Empty
            | Singleton v
            | (TERM v) `U` (TERM v)
            | (TERM v) `I` (TERM v)
            --Potensmängd?
            | Var v
    deriving (Show)

type Env var dom = [(var,dom)]

data PRED v = Elem v (TERM v)
            | Sub (TERM v) (TERM v)
            | (PRED v) `And` (PRED v)
            | (PRED v) `Or` (PRED v)
            | (PRED v) `Implies` (PRED v)
            | Not (PRED v)
    deriving (Show) 

set1 :: TERM v
set1 = Empty

set2 :: TERM (TERM v)
set2 = Singleton Empty

newtype Set = S [Set ]
    deriving Show

eval :: Eq v => Env v Set -> TERM v -> Set
eval [(var,dom)] set = undefined 

check :: Eq v => Env v Set -> PRED v -> Bool
check [(var,dom)] set = undefined 