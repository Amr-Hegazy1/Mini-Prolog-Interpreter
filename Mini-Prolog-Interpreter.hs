data Term = Cons String | Var String deriving (Show,Eq)

data Predicate = P String [Term] deriving (Show,Eq)

type Goal = [Predicate] 

data Rule = Fact Predicate | R Predicate Goal deriving (Show,Eq)

data Solution = No | Yes [(Term,Term)] deriving (Show,Eq)


unifyWithHead (P name1 (h1:t1)) ( P name2 (h2:t2) ) | name1 == name2 = unifyWithHeadHelper (h1:t1) (h2:t2) []
                                                    | otherwise = No

unifyWithHeadHelper [] [] acc = (Yes acc)

unifyWithHeadHelper ((Var a):t1) ((Var b):t2) acc = unifyWithHeadHelper t1 t2 (((Var a),(Var b)) : acc)


unifyWithHeadHelper ((Var a):t1) ((Cons b):t2) acc = unifyWithHeadHelper t1 t2 ((((Var a),(Cons b))) : acc)

unifyWithHeadHelper ((Cons a):t1) ((Var b):t2) acc = unifyWithHeadHelper t1 t2 ((((Cons a),(Var b))) : acc)

unifyWithHeadHelper ((Cons a):t1) ((Cons b):t2) acc | a == b =  unifyWithHeadHelper t1 t2 acc
                                                    | otherwise = No


applySolSubInBody (Yes []) p = p

applySolSubInBody (Yes (h:t)) p = applySolSubInBody (Yes t) (sub h p)  

applySolSubInBody No _ = []  

sub _ [] = []

sub (Var x, Var y) ((P n l) : t) = (P n (map (sub_help (Var x, Var y)) l)) : sub (Var x, Var y) t

sub (Var x, Cons y) ((P n l) : t) = (P n (map (sub_help (Var x, Cons y)) l)) : sub (Var x, Cons y) t

sub (Cons x, Var y) ((P n l) : t) = (P n (map (sub_help (Cons x, Var y)) l)) : sub (Cons x, Var y) t

sub_help (Var x, Var y) (Var k) | x == k = (Var y)
                                | otherwise = (Var k)

sub_help (Var x, Cons y) (Var k) | x == k = (Cons y)
                                 | otherwise = (Var k)

sub_help (Cons x, Var y) (Var k) | y == k = (Cons x)
                                 | otherwise = (Var k)

sub_help (_, _) (Cons k) = (Cons k)


                                 



allSolutions q r = (sol q r) 

sol _ [] = []

sol h (hr:tr) | unifyWithHead h hr == No = sol h tr
              | otherwise = applySolSubInBody (unifyWithHead h hr) tr



