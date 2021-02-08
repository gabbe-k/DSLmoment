-- DSLsofMath 2020: Assignment 1

import Data.Maybe
import Data.List
import Test.QuickCheck
 
data TERM v = Empty
            | Sing (TERM v)
            | (TERM v) `U` (TERM v)
            | (TERM v) `I` (TERM v)
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
    deriving (Show)

instance Eq Set where 
    (==) = setEq

--Sets are equal independent of order and eventual duplicates
setEq :: Set -> Set -> Bool 
setEq (S a1) (S a2) = null (s1 \\ s2) && null (s2 \\ s1)
    where s1 = nub a1
          s2 = nub a2

--------------------------Part 2

eval :: Eq v => Table v -> TERM v -> Set
eval t Empty = S []
eval t (Sing v) = S [eval t v]
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
vonNeumann n = U (vonNeumann (n-1)) (Sing (vonNeumann (n-1)))

--If you have a neumann(n1) set and neumann(n2) set where n1 <= n2, this implies that
--neumann(n1)  is a subset of neumann(n2).
claim1 :: (Ord t, Num t) => t -> t -> Bool
claim1 n1 n2 = imp (n1 <= n2) (check tab (Sub (vonNeumann n1) (vonNeumann n2)))
 
--neumann(n) = [neumann(0), neumann(1) ... neumann(n-1)], the set n is composed of the previous n sets
claim2 :: (Eq t, Num t, Enum t) => t -> Bool
claim2 n = eval tab (vonNeumann n) == S [eval tab (vonNeumann s) | s <- [0..n-1]]

card :: Set -> Int
card (S a1) = length (nub a1)

--Quality of life improvements
chk :: PRED String -> Bool
chk a = check tab a

evl :: TERM String -> Set
evl a = eval tab a

--------------------------Testing 
tab :: Table String 
tab = [("m0", S []), ("m1", S [S [S [S []]], S [S []], S [S []], S [S[S[S[]]]]]), ("m2", S [S [S []], S [S[S[S[]]]]])]

a0 :: PRED [Char]
a0 = (Elem Empty (Var "m2")) --true

a1 :: PRED [Char]
a1 = (Sub Empty (Var "m1")) --true

eval1 :: Set --returns empty because you take intersection \w empty
eval1 = eval tab ((Sing (Empty) `U` (Var "m1")) `I` (Empty `U` (Empty `U` (Var "m0"))))


cardCheck :: TERM String -> TERM String -> Bool
cardCheck a b = (card (eval tab (a `U` b))) + (card (eval tab (a `I` b))) == 
                (card (eval tab a)) + (card (eval tab b))




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
t5 a b = t4 a b && t1 a && t1 b && not (t2 a)

--big test combined with von neumann
t6 :: (Eq t, Num t) => t -> Bool
t6 n = t5 a0 (Elem a b) && t5 a0 (Elem b a)
    where a = vonNeumann n
          b = vonNeumann (2*n)

--cardinality test 1
t7 :: (Eq t, Num t) => t -> Bool
t7 n = cardCheck (vonNeumann n) (vonNeumann (2*n)) && cardCheck (vonNeumann (2*n)) (vonNeumann n)

--cardinaltiy test 2
t8 :: Bool
t8 = card (evl (Sing (Sing Empty))) == 1 && card (evl Empty) == 0

t9 :: TERM v -> TERM v -> PRED v
t9 a b = Implies (Elem (Empty) (a `U` b)) (Or (Elem Empty a) (Elem Empty b))

t10 :: TERM v -> TERM v -> PRED v
t10 a b = Implies (Or (Elem Empty a) (Elem Empty b)) (Elem Empty (a `U` b))

--test of implies, elem, union.. -- tautology because of "Elem Empty x"
t11 :: TERM String -> TERM String -> Bool
t11 a b = chk (t9 a b `And` t10 a b)

t12 :: (Num t, Eq t) => t -> Bool
t12 n = t11 (vonNeumann n) (vonNeumann (n^2))

--Intersection commutativity
t13 :: Bool
t13 = evl (Var "m1" `I` Var "m2") == evl (Var "m2" `I` Var "m1")
t14 :: Bool
t14 = evl (Var "m1" `U` Var "m2") == evl (Var "m2" `U` Var "m1")

