-- DSLsofMath 2020: Assignment 1

import Data.Maybe
import Data.List
import Test.QuickCheck
 
data TERM v = Empty
            | Sing (TERM v)
            | (TERM v) `U` (TERM v)
            | (TERM v) `I` (TERM v)
            --Potensmängd?
            | Var v
    deriving (Show)

data PRED v = Elem (TERM v) (TERM v)
            | Sub (TERM v) (TERM v)
            | (PRED v) `And` (PRED v)
            | (PRED v) `Or` (PRED v)
            | (PRED v) `Implies` (PRED v)
            | Not (PRED v)
    deriving (Show) 

type Env var dom = [(var,dom)]
type Table v = Env v Set 

newtype Set = S [Set]
    deriving (Show, Eq)


--------------------------Part 2

eval :: Eq v => Table v -> TERM v -> Set
eval t Empty = S []
eval t (Sing v) = S [ eval t v ]
eval t (s1 `U` s2) = mergeSet (eval t s1) (eval t s2) (++)
eval t (s1 `I` s2) = mergeSet (eval t s1) (eval t s2) intersect
eval t (Var v) = fromJust (lookup v t)


check :: Eq v => Table v -> PRED v -> Bool
check t (Elem Empty t2)      = True
check t (Elem t1 t2)         = eval t t1 `elem` a2
        where (S a2)         = eval t t2
check t (Sub p1 p2)          = sub (eval t p1) (eval t p2)        
check t (And p1 p2)          = check t p1 && check t p2    
check t (Or p1 p2)           = check t p1 || check t p2
check t (Implies p1 p2)      = imp (check t p1) (check t p2)
check t (Not p)              = not (check t p)

--------------------------Helper funcs
convSet :: Set -> Set -> ([Set] -> [Set] -> [Set]) -> Set
convSet (S a1) (S a2) op = S (a1 `op` a2)

mergeSet :: Set -> Set -> ([Set] -> [Set] -> [Set]) -> Set
mergeSet s1@(S a1) s2@(S a2) op = f eq
    where f True = s1
          f False = S (a1 `op` a2)
          eq = s1 == s2

sub :: Set -> Set -> Bool
sub (S a1) (S a2) = and [e `elem` a2 | e <- a1]

imp :: Bool -> Bool -> Bool
imp True False = False
imp _ _ = True

--------------------------Part 3

vonNeumann :: (Eq t, Num t) => t -> TERM v
vonNeumann 0 = Empty
vonNeumann (n) = U (vonNeumann (n-1)) (Sing (vonNeumann (n-1)))

--If you have a neumann(n1) set and neumann(n2) set where n1 <= n2, this implies that
--neumann(n1)  is a subset of neumann(n2).
claim1 :: (Ord t, Num t) => t -> t -> Bool
claim1 n1 n2 = imp (n1 <= n2) (check tab (Sub (vonNeumann n1) (vonNeumann n2)))
 
--neumann(n) = [neumann(0), neumann(1) ... neumann(n-1)], the set n is composed of the previous n sets
claim2 :: (Eq t, Num t, Enum t) => t -> Bool
claim2 n = eval tab (vonNeumann n) == S [eval tab (vonNeumann s) | s <- [0..n-1]]

--------------------------Testing 
--[(m0,{1,2,3})]
tab :: Table String 
tab = [("m0", S []), ("m1", S [S [S [S []]]]), ("m2", S [S [], S []])]


a0 :: PRED [Char]
a0 = (Elem Empty (Var "m2")) --true

a1 :: PRED [Char]
a1 = (Sub Empty (Var "m1")) --true

chk :: PRED String -> Bool
chk a = check tab a

--tautology
t1 :: PRED String -> Bool
t1 a = check tab (a `Or` (Not a))

--contradiction
t2 :: PRED String -> Bool
t2 a = check tab (a `And` (Not a))

--double negation
t3 :: PRED String -> Bool
t3 a = check tab (Not (Not a))

--tautology 
t4 :: PRED String -> PRED String -> Bool
t4 a b = check tab ( (a `Implies` b) `Or` (b `Implies` a))

--big test
t5 :: PRED String -> PRED String -> Bool
t5 a b = (t4 a b) && (t1 a) && (t1 b) && (not (t2 a))




