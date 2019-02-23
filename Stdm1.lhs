-------------------------------------------------------------------------------
	       Software Tools for Discrete Mathematics
		   Cordelia Hall and John O'Donnell
-------------------------------------------------------------------------------

Last modified: April 2, 2000

This software is intended to be used with the book "Discrete
Mathematics Using a Computer", by Cordelia Hall and John O'Donnell,
which was published by Springer in January, 2000.  Softcover, ISBN
1-85233-089-9.

The software is written in Haskell 98, the standard functional
programming language.  It runs interactively under the Hugs 98
implementation.  Under Unix, you can start hugs with the command

  hugs -98

which tells it to use the standard Haskell 98 language, but not the
experimental language extensions.

This software, and its documentation, can be downloaded from the book
web page:

	    www.dcs.gla.ac.uk/~jtod/discrete-mathematics/

It's a good idea to check the web page periodically to keep the
software up to date.

The program is a "literate script".  Each line that begins with "> "
is Haskell source code that can be executed; all other lines are
documentation which will be ignored by the compiler.


> module Stdm where

-------------------------------------------------------------------------------
			 Operator Precedence
-------------------------------------------------------------------------------

> infix 1 <=>
> infix 2 ==>
> infix 3 \/
> infix 4 /\
> infix 3 +++
> infix 4 ~~~
> infix 4 ***
> infix 5 !!!

-------------------------------------------------------------------------------
		   Chapter 2.  Propositional Logic
-------------------------------------------------------------------------------


> (<=>) :: Bool -> Bool -> Bool
> (<=>) a b = a == b

> (==>) :: Bool -> Bool -> Bool
> (==>) True False = False
> (==>) a b = True

> (\/) = (||)

> (/\) = (&&)


-------------------------------------------------------------------------------
  A Mini-tutorial on Using the Proof Checker for Propositional Logic
-------------------------------------------------------------------------------

And Introduction
~~~~~~~~~~~~~~~~

Here is a theorem and a valid proof using the And Introduction rule:

Theorem AI1.  q,r  |-  q&r

> thAI1 = Theorem [Q,R] (Q `And` R)
> prAI1 = AndI (Assume Q, Assume R) (And Q R)

To check that Proof prAI1 is a valid proof of Theorem thAI1, execute
the following expression interactively:

	check_proof thAI1 prAI1

The next theorem is similar, but it's incorrect because Q `And` S
doesn't follow from assuming Q and R.

Theorem AI2.  q,r  |-  q&s

Here are the theorem and an invalid proof of it, using the And
Introduction rule incorrectly.

> thAI2 = Theorem [Q,R] (Q `And` S)
> prAI2 =
>   AndI (Assume Q, Assume R)
>        (And Q S)

Try it out with the proof checker by evaluating the following
interactively:

	check_proof thAI2 prAI2

And Elimination (Left)
~~~~~~~~~~~~~~~~~~~~~~

Here is a theorem and a valid proofs using And Elimination (Left).
Test it by evaluating

	check_proof thAEL1 prAEL1

Theorem AEL1.  p&q |-  p

> thAEL1 = Theorem [P `And` Q] P
> prAEL1 = AndEL (Assume (And P Q)) P

This is a slightly more complex theorem, again with a valid proof
using And Elimination (Left).  Check it with

	check_proof thAEL2 prAEL2

Theorem AEL2.  (P|Q)&R |- (P|Q)

> thAEL2 = Theorem [(P `Or` Q) `And` R] (P `Or` Q)
> prAEL2 = AndEL (Assume (And (Or P Q) R)) (Or P Q)

Now we try some invalid proofs.  Consider the following theorem, the
theorem itself is valid but its proof is incorrect.  Check it by
evaluating the expression check_AEL3; the proof checker will tell you
exactly what is wrong with the proof.  Notice that we're moving to a
slightly more concise style, where we aren't naming both the theorem
and the proof separately.

Theorem AEL3.  p&q |-  p

> check_AEL3 =
>   check_proof
>     (Theorem [P `And` Q] P)
>    (AndEL (Assume (Or P Q)) P)

> p6 = -- p&q  |-  p
>   AndEL (Assume (And P Q)) Q
> p7 = -- P&Q  |-  R
>   AndEL (Assume (And P Q)) R

And Elimination (Right)
~~~~~~~~~~~~~~~~~~~~~~~

The following theorem and proof are correct; they are the mirror image
of the AEL1 example above.

> check_AER1 =
>   check_proof
>     (Theorem [P `And` Q] Q)
>     (AndER (Assume (P `And` Q)) Q)

This example is similar; the theorem is ok and the proof would be
valid if it used the AndEL rule, but the AndER rule does not justify
the conclusion, so the proof fails to establish the theorem.

> check_AER2 =
>   check_proof
>     (Theorem [P `And` Q] Q)
>     (AndER (Assume (P `And` Q)) P)

Imply Introduction
~~~~~~~~~~~~~~~~~~

Theorem II1.  Q |- P => P&Q

> check_II1 =
>   check_proof
>     (Theorem [Q] (P `Imp` (P `And` Q)))
>     (ImpI (AndI (Assume P, Assume Q)
>                 (And P Q))
>           (Imp P (And P Q)))


Theorem II2.  |- Q => (P => (P&Q))

> check_II2 =
>   check_proof
>     (Theorem [] (Q `Imp` (P `Imp` (P `And` Q))))
>     (ImpI (ImpI (AndI (Assume P, Assume Q)
>                       (And P Q))
>                 (Imp P (And P Q)))
>           (Imp Q (Imp P (And P Q))))

Imply Elimination
~~~~~~~~~~~~~~~~~

Theorem IE1.  P, P=>Q  |-  Q

> check_IE1 =
>   check_proof
>     (Theorem [P, P `Imp` Q] Q)
>     (ImpE (Assume P, Assume (Imp P Q))
>           Q)


Or Introduction (Left)
~~~~~~~~~~~~~~~~~~~~~~

Theorem OEL1.  P&Q |- P&Q \/ S&P

> check_OIL1 =
>   check_proof
>     (Theorem [P `And` Q, Q `And` R]
>              ((P `And` Q) `Or` (S `And` P)))
>     (OrIL (Assume (P `And` Q))
>           ((P `And` Q) `Or` (S `And` P)))

Or Introduction (Right)
~~~~~~~~~~~~~~~~~~~~~~~

Theorem OIR1.  ~S |- P \/ ~S

> check_OIR1 =
>   check_proof
>     (Theorem [Not S] (P `Or` (Not S)))
>     (OrIR (Assume (Not S))
>           (P `Or` (Not S)))

Identity
~~~~~~~~

> check_ID0 =
>   check_proof
>     (Theorem [P `And` Q] (P `And` Q))
>     (Assume (P `And` Q))

Now the same is proved using the ID inference rule.

Theorem ID1.  P&Q |- P&Q

> check_ID1 =
>   check_proof
>     (Theorem [P `And` Q] (P `And` Q))
>     (ID (Assume (P `And` Q)) (P `And` Q))
 

Contradiction
~~~~~~~~~~~~~

Theorem CTR1.  False |- P & ~P

> check_CTR1 =
>   check_proof
>     (Theorem [FALSE] (P `And` (Not P)))
>     (CTR (Assume FALSE) (P `And` (Not P)))

The next theorem isn't valid, because the premise P isn't enough to
establish P & ~P, and it isn't FALSE so the Contradiction inference
rule doesn't apply.

Theorem CTR2.  P |- P & ~P

> check_CTR2 =
>   check_proof
>     (Theorem [P] (P `And` (Not P)))
>     (CTR (Assume P) (P `And` (Not P)))

Reductio ab Absurdum
~~~~~~~~~~~~~~~~~~~~

Theorem RAA1.  ~~P |- P

> check_RAA1 =
>   check_proof
>     (Theorem [P `Imp` FALSE, (P `Imp` FALSE) `Imp` FALSE]
>              P)
>     (RAA (ImpE (Assume (P `Imp` FALSE),
>                Assume ((P `Imp` FALSE) `Imp` FALSE))
>                FALSE)
>          P)

Examples from the book
~~~~~~~~~~~~~~~~~~~~~~

Here is the theorem and  proofs that are used in the book;
run them like this:
   check_proof example_theorem proof1     (should be valid)
   check_proof example_theorem proof2     (should give error message)

> example_theorem :: Theorem
> example_theorem =
>   Theorem
>     []
>     (Imp Q (Imp (And P R) (And R Q)))

> proof1 =
>   ImpI
>     (ImpI
>        (AndI
>           ((AndER
>               (Assume (And P R))
>               R),
>             Assume Q)
>           (And R Q))
>        (Imp (And P R) (And R Q)))
>     (Imp Q (Imp (And P R) (And R Q)))

The following proof is incorrect proof, because Q^R was inferred where
R^Q was needed.

> proof2 =
>   ImpI
>     (ImpI
>        (AndI
>           (Assume Q,
>            (AndER
>               (Assume (And P R))
>               R))
>           (And R Q))
>        (Imp (And P R) (And R Q)))
>     (Imp Q (Imp (And P R) (And R Q)))

-------------------------------------------------------------------------------
     Implementation of the Proof Checker for Propositional Logic
-------------------------------------------------------------------------------

> data Prop
>   = FALSE
>   | TRUE
>   | A | B | C | D | E | G | H | I | J | K | L | M
>   | N | O | P | Q | R | S | U | V | W | X | Y | Z
>   | Pvar String
>   | And Prop Prop
>   | Or Prop Prop
>   | Not Prop
>   | Imp Prop Prop
>   deriving (Eq,Show)

> data Theorem
>   = Theorem [Prop] Prop
>   deriving (Eq,Show)

> data Proof
>   = Assume Prop
>   | AndI (Proof,Proof) Prop
>   | AndEL Proof Prop
>   | AndER Proof Prop
>   | OrIL Proof Prop
>   | OrIR Proof Prop
>   | OrE (Proof,Proof,Proof) Prop
>   | ImpI Proof Prop
>   | ImpE (Proof,Proof) Prop
>   | ID Proof Prop
>   | CTR Proof Prop
>   | RAA Proof Prop
>   deriving (Eq,Show)

When a proof is checked, several pieces of information are gathered
together into a data structure called Status.

> type Status =
>   (Bool,       -- True iff the proof is valid
>    [String],   -- messages describing errors found in the proof
>    [Prop],     -- undischarged assumptions required by the proof
>    Prop)       -- conclusion

> union :: Eq a => [a] -> [a] -> [a]
> union = (++)   -- need to remove duplicates

> setelem :: Eq a => a -> [a] -> Bool
> setelem x = any (==x)
> 
> setdif :: Eq a => [a] -> [a] -> [a]
> setdif xs ys = [x | x<-xs, not (setelem x ys)]


> check_proof :: Theorem -> Proof -> IO ()
> check_proof (Theorem thas thc) proof =
>   do let (valid, ms, uda, concl) = traverse proof
>      let allok = valid && concl==thc && jsubset uda thas
>      if allok
>        then putStr "The proof is valid\n"
>        else do
>                let nuda = length uda
>--                if nuda==0
>--                  then putStr "There are no undischarged assumptions\n"
>--                  else do putStr "Undischarged assumptions:\n"
>--                          putlist (map show uda)
>--                putStr ("The conclusion is " ++ show concl ++ "\n")
>                if length ms == 0
>                   then return ()
>                   else do putlist ms
>                putStr ("The proof is invalid\n")
>      return ()

> jsubset :: Eq a => [a] -> [a] -> Bool
> jsubset xs ys = and [elem x ys | x <- xs]

> putlist :: [String] -> IO ()
> putlist [] = return ()
> putlist (x:xs) = do putStr x
>                     putlist xs

The real work is performed in the traverse function, which has a
separate case for checking each inference rule.  Nearly all the
complexity in the following code results from an attempt to provide
meaningful error messages; if the aim were merely to decide whether a
proof is valid, then the implementation could rely much more on
Haskell's pattern matching mechanism, and everything would be much
more concise.

> traverse :: Proof -> Status

> traverse (Assume a) = (True, [], [a], a)

> traverse (AndI (a,b) c) =
>   let (avalid, amsgs, auda, aconcl) = traverse a
>       (bvalid, bmsgs, buda, bconcl) = traverse b
>       ok = c == And aconcl bconcl
>       valid = avalid && bvalid && ok
>       msgs = amsgs ++ bmsgs ++
>          if ok then []
>           else ["Invalid And-Introduction: the conclusion\n     "
>                 ++ show c
>                 ++ "\n  must be the logical And of the assumption\n     "
>                 ++ show aconcl
>                 ++ "\n  with the assumption\n     "
>                 ++ show bconcl
>                 ++ "\n"]
>       msg = "AndI: conclusion must be logical And of assumptions"
>       uda = auda `union` buda
>   in  (valid, msgs, uda, c)

> traverse (AndEL a b) =
>   let (avalid, amsgs, auda, aconcl) = traverse a
>       (ok,msg) =
>         case aconcl of
>           And p q -> if p==b then (True,[])
>                              else (False, [err1])
>           otherwise -> (False, [err2])
>       err1 = "AndEL: first arg of And assumption doesn't match conclusion\n"
>       err2 = "AndEL: assumption is not an And expression\n"
>       valid = avalid && ok
>       msgs = amsgs ++ msg
>       uda = auda
>   in (valid, msgs, uda, b)


> traverse (AndER a b) =
>   let (avalid, amsgs, auda, aconcl) = traverse a
>       (ok,msg) =
>         case aconcl of
>           And p q -> if q==b then (True,[])
>                              else (False, [err1])
>           otherwise -> (False, [err2])
>       err1 = "AndER: second arg of And assumption doesn't match conclusion\n"
>       err2 = "AndER: assumption is not an And expression\n"
>       valid = avalid && ok
>       msgs = amsgs ++ msg
>       uda = auda
>   in (valid, msgs, uda, b)

> traverse (OrIL a b) =
>   let (avalid, amsgs, auda, aconcl) = traverse a
>       (ok,ms) =
>         case b of
>           Or p q ->
>             if aconcl == p
>               then (True,[])
>               else (False,[err2])
>           otherwise -> (False,[err1])
>       err1 = "OrIL: the conclusion must be an Or expression"
>       err2 = "OrIL: the assumption must match first term in conclusion"
>       valid = avalid && ok
>       msgs = amsgs ++ ms
>       uda = auda
>   in (valid, msgs, uda, b)


> traverse (OrIR a b) =
>   let (avalid, amsgs, auda, aconcl) = traverse a
>       (ok,ms) =
>         case b of
>           Or p q ->
>             if aconcl == q
>               then (True,[])
>               else (False,[err2])
>           otherwise -> (False,[err1])
>       err1 = "OrIR: the conclusion must be an Or expression"
>       err2 = "OrIR: the assumption must match second term in conclusion"
>       valid = avalid && ok
>       msgs = amsgs ++ ms
>       uda = auda
>   in (valid, msgs, uda, b)

> traverse (ImpI a b) =
>   let (avalid, amsgs, auda, aconcl) = traverse a
>       (ok,ms) = case b of
>                   Imp p q ->
>                     if p `setelem` auda && aconcl==q
>                       then (True,[])
>                     else if not (p `setelem` auda) && aconcl==q
>                       then (False,[err2])
>                     else if p `setelem` auda && aconcl/=q
>                       then (False,[err3])
>                     else (False,[err2,err3])
>                   otherwise -> (False,[err1])
>       err1 = "ImpI: conclusion must be an implication"
>       err2 = "ImpI: antecedent must be undischarged assumption above line"
>       err3 = "ImpI: conclusion must match the conclusion above line"
>       valid = avalid && ok
>       msgs = amsgs ++ ms
>       uda = case b of
>               Imp p q -> auda `setdif` [p]
>               otherwise -> auda
>   in (valid, msgs, uda, b)

> traverse (ImpE (a,b) c) =
>   let (avalid, amsgs, auda, aconcl) = traverse a
>       (bvalid, bmsgs, buda, bconcl) = traverse b
>       (ok,ms) = case bconcl of
>                      Imp p q ->
>                        if aconcl==p && c==q
>                          then (True,[])
>                        else if aconcl/=p && c==q
>                          then (False,[err2])
>                        else if aconcl==p && c/=q
>                          then (False,[err3])
>                        else (False,[err2,err3])
>                      otherwise -> (False,[err1])
>       err1 = "ImpE: second term above line must be an implication\n"
>       err2 = "ImpE: first term must match antecedent of second term\n"
>       err3 = "ImpE: conclusion must match conclusion of second term\n"
>       valid = avalid && bvalid && ok
>       msgs = amsgs ++ bmsgs ++ ms
>       uda = auda `union` buda
>   in (valid, msgs, uda, c)

> traverse (ID a c) =
>   let (avalid, amsgs, auda, aconcl) = traverse a
>       (ok,ms) = if aconcl==c
>                  then (True,[])
>                  else (False,[err1])
>       err1 = "ID: conclusion must match the antecedent\n"
>       valid = avalid && ok
>       msgs = amsgs ++ ms
>   in (valid, msgs, auda, c)

> traverse (CTR a c) =
>   let (avalid, amsgs, auda, aconcl) = traverse a
>       (ok,ms) = if aconcl==FALSE
>                   then (True,[])
>                   else (False,[err1])
>       err1 = "CTR: the antecedent must be FALSE\n to use CTR\n"
>       valid = avalid && ok
>       msgs = amsgs ++ ms
>   in (valid, msgs, auda, c)

> traverse (RAA a c) =
>   let (avalid, amsgs, auda, aconcl) = traverse a
>       (ok,ms) = if not ((c `Imp` FALSE) `elem` auda)
>                   then (False, [err1])
>                   else if aconcl /= FALSE
>                        then (False, [err2])
>                        else (True, [])
>       err1 = "RAA: proof above the line must assume Not conclusion\n"
>       err2 = "RAA: proof above the line must conclude FALSE\n"
>       valid = avalid && ok
>       msgs = amsgs ++ ms
>   in (valid, msgs, auda, c)



-------------------------------------------------------------------------------
		     Chapter 3.  Predicate Logic
-------------------------------------------------------------------------------

> forall :: [Int] -> (Int -> Bool) -> Bool
> forall u p = all p u

> exists :: [Int] -> (Int -> Bool) -> Bool
> exists u p = any p u


-------------------------------------------------------------------------------
			Chapter 4.  Set Theory
-------------------------------------------------------------------------------

> type Set a = [a]

> errfun :: Show a => String -> a -> String -> b
> errfun f s msg = error (f ++ ": " ++ show s ++ " is not a " ++ msg)

note that subset does not reject non-sets

> subset :: (Eq a, Show a) => Set a -> Set a -> Bool
> subset set1 set2 
>      = foldr f True set1
>        where 
>        f x sofar = if elem x set2 then sofar else False

> -- note that properSubset does not reject non-sets
> properSubset :: (Eq a, Show a) => Set a -> Set a -> Bool
> properSubset set1 set2
>      = not (setEq set1 set2) /\ (subset set1 set2)

> -- note that setEq does not reject non-sets
> setEq :: (Eq a, Show a) => Set a -> Set a -> Bool
> setEq set1 set2 
>      = (set1 `subset` set2) /\ (set2 `subset` set1)

> normalForm :: (Eq a, Show a) => [a] -> Bool
> normalForm set = length (normalizeSet set) == length set

> normalizeSet :: Eq a => [a] -> Set a
> normalizeSet elts 
>      = foldr f [] elts
>        where
>        f x sofar 
>          = if x `elem` sofar then sofar else x:sofar

> (+++) :: (Eq a, Show a) => Set a -> Set a -> Set a
> (+++) set1 set2 
>      = if not (normalForm set1)
>           then errfun "+++" set1 "set"
>           else if not (normalForm set2)
>                then errfun "+++" set2 "set"
>                else normalizeSet (set1 ++ set2)

> (***) :: (Eq a, Show a) => Set a -> Set a -> Set a
> (***) set1 set2
>      = if not (normalForm set1)
>           then errfun "***" set1 "set"
>           else if not (normalForm set2)
>                then errfun "***" set2 "set"
>                else [x | x <- set1, (x `elem` set2)]

> (~~~) :: (Eq a, Show a) => Set a -> Set a -> Set a
> (~~~) set1 set2 
>      =  if not (normalForm set1)
>            then errfun "~~~" set1 "set"
>            else if not (normalForm set1)
>                 then errfun "~~~" set2 "set"
>                 else [x | x <- set1, not (x `elem` set2)]

> (!!!) :: (Eq a, Show a) => Set a -> Set a -> Set a
> (!!!) u a = if not (normalForm u)
>                then errfun "!!!" u "set"
>                else
>             if not (normalForm a)
>                then errfun "!!!" a "set"
>             else u ~~~ a

> powerset :: (Eq a, Show a) => Set a -> Set (Set a)
> powerset set
>  = if not (normalForm set)
>       then errfun "powerset" set "set"
>    else
>    powersetLoop set
>    where
>    powersetLoop [] = [[]]
>    powersetLoop (e:set)
>      = let setSoFar = powersetLoop set
>        in [e:s | s <- setSoFar] ++ setSoFar

> crossproduct :: (Eq a, Show a, Eq b, Show b) => Set a ->
>                   Set b -> Set (a,b)
> crossproduct set1 set2
>  = if not (normalForm set1)
>       then errfun "crossproduct" set1 "set"
>    else
>    if not (normalForm set2)
>       then errfun "crossproduct" set2 "set"
>    else [(a,b) | a <- set1, b <- set2]


-------------------------------------------------------------------------------
			Chapter 5.  Recursion
-------------------------------------------------------------------------------

> factorial :: Integer -> Integer
> factorial 0 = 1
> factorial (n+1) = (n+1) * factorial n

> quicksort :: Ord a => [a] -> [a]
> quicksort [] = []
> quicksort (splitter:xs) =
>   quicksort [y | y <- xs, y<=splitter]
>   ++ [splitter]
>   ++ quicksort [y | y <- xs, y>splitter]

> firsts1, firsts2 :: [(a,b)] -> [a]
> firsts1 [] = []
> firsts1 ((a,b):ps) = a : firsts1 ps

> firsts2 xs = map fst xs

> data Tree a
>   = Tip
>   | Node a (Tree a) (Tree a)
>   deriving Show

> t1, t2 :: Tree Int
> t1 = Node 6 Tip Tip
> t2 = Node 5
>        (Node 3 Tip Tip)
>        (Node 8 (Node 6 Tip Tip) (Node 12 Tip Tip))

> nodeCount :: Tree a -> Int
> nodeCount Tip = 0
> nodeCount (Node x t1 t2) = 1 + nodeCount t1 + nodeCount t2

> reflect :: Tree a -> Tree a
> reflect Tip = Tip
> reflect (Node a t1 t2) = Node a (reflect t2) (reflect t1)

> mapTree :: (a->b) -> Tree a -> Tree b
> mapTree f Tip = Tip
> mapTree f (Node a t1 t2) =
>   Node (f a) (mapTree f t1) (mapTree f t2)

> tree :: Tree (Int,Int)
> tree =
>   Node (5,10)
>     (Node (3,6)  (Node (1,1) Tip Tip)
>                  (Node (4,8) Tip Tip))
>     (Node (7,14) (Node (6,12) Tip Tip)
>                  (Node (8,16) Tip Tip))

> find :: Int -> Tree (Int,a) -> Maybe a
> find n Tip = Nothing
> find n (Node (m,d) t1 t2) =
>   if n==m then Just d
>   else if n<m then find n t1
>               else find n t2


> data Peano = Zero | Succ Peano deriving Show

> one   = Succ Zero
> two   = Succ one
> three = Succ two
> four  = Succ three
> five  = Succ four
> six   = Succ five

> data List a = Empty | Cons a (List a)

> decrement :: Peano -> Peano
> decrement Zero = Zero
> decrement (Succ a) = a

> add :: Peano -> Peano -> Peano
> add Zero     b = b
> add (Succ a) b = Succ (add a b)

> sub :: Peano -> Peano -> Peano
> sub a        Zero     = a
> sub Zero     b        = Zero
> sub (Succ a) (Succ b) = sub a b

> equals :: Peano -> Peano -> Bool
> equals Zero     Zero     = True
> equals Zero     b        = False
> equals a        Zero     = False
> equals (Succ a) (Succ b) = equals a b

> lt :: Peano -> Peano -> Bool
> lt a        Zero     = False
> lt Zero     (Succ b) = True
> lt (Succ a) (Succ b) = lt a b

> f_datarec :: a -> [a]
> f_datarec x = x : f_datarec x

> ones = f_datarec 1

> twos = 2 : twos

> object = let a = 1:b
>              b = 2:c
>              c = [3] ++ a
>          in a

-------------------------------------------------------------------------------
			Chapter 8.  Relations
-------------------------------------------------------------------------------


> type Relation a = Set (a,a)

> type Digraph a = (Set a, Relation a)

> domain :: (Eq a, Show a, Eq b, Show b) => Set (a,b) -> Set a
> domain set
>  = if not (normalForm set)
>       then errfun "domain" set "set"
>    else
>    map fst set

> codomain :: (Eq a, Show a, Eq b, Show b) => Set (a,b) -> Set b
> codomain set
>  = if not (normalForm set)
>       then errfun "codomain" set "set"
>    else
>    map snd set

> isDigraph :: (Eq a, Show a) => Digraph a -> Bool
> isDigraph (set, relation)
>  = normalForm set /\ normalForm relation

> digraphEq :: (Eq a, Show a) => Digraph a -> Digraph a -> Bool
> digraphEq digraph1 digraph2
>      = if not (isDigraph digraph1)
>           then errfun "digraphEq" digraph1 "digraph"
>        else
>        if not (isDigraph digraph2)
>           then errfun "digraphEq" digraph2 "digraph"
>        else
>        let (set1,relation1) = digraph1
>            (set2,relation2) = digraph2
>        in (setEq set1 set2) /\ (setEq relation1 relation2)

> isReflexive :: (Eq a, Show a) => Digraph a -> Bool
> isReflexive digraph
>         = if not (isDigraph digraph)
>              then errfun "isReflexive" digraph "digraph"
>           else
>           let (set, relation) = digraph
>           in and [elem (e,e) relation | e <- set]

> isIrreflexive :: (Eq a, Show a) => Digraph a -> Bool
> isIrreflexive digraph
>         = if not (isDigraph digraph)
>              then errfun "isIrreflexive" digraph "digraph"
>           else
>           let (set, relation) = digraph
>           in [a | (a,b) <- relation, a == b && elem a set] == []

> lessThan_N100 :: Digraph Int
> lessThan_N100 
>  = let set = [1..100]
>    in (set,[(a,b) | a <- set, b <- set, a < b])

> equals_N100 :: Digraph Int
> equals_N100
>  = let set = [1..100]
>    in (set,[(a,b) | a <- set, b <- set, a == b])

> greaterThan_N100 :: Digraph Int
> greaterThan_N100
>  = let set = [1..100]
>    in (set,[(a,b) | a <- set, b <- set, a > b])

> lessThanOrEq_N100 :: Digraph Int
> lessThanOrEq_N100
>  = let set = [1..100]
>    in (set,[(a,b) | a <- set, b <- set, a < b \/ a == b])

> greaterThanOrEq_N100 :: Digraph Int
> greaterThanOrEq_N100
>  = let set = [1..100]
>    in (set,[(a,b) | a <- set, b <- set, a > b \/ a == b])

> notEq_N100 :: Digraph Int
> notEq_N100 
>  = let set = [1..100]
>    in (set,[(a,b) | a <- set, b <- set, not (a == b)])

> isSymmetric ::  (Eq a, Show a) => Digraph a -> Bool
> isSymmetric digraph
>      = if not (isDigraph digraph)
>           then errfun "isSymmetric" digraph "digraph"
>        else
>        let (set, relation) = digraph
>        in
>        and [(elem (a,b) relation) ==> (elem (b,a) relation)         
>             | a <- set, b <- set]

> isAntisymmetric ::  (Eq a, Show a) => Digraph a -> Bool
> isAntisymmetric digraph
>      = if not (isDigraph digraph)
>           then errfun "isAntisymmetric" digraph "digraph"
>        else
>        let (set, relation) = digraph
>        in
>        and [((elem (x,y) relation) /\ (elem (y,x) relation))          
>             ==> (x == y) | x <- set, y <- set]

> isTransitive :: (Eq a, Show a) => Digraph a -> Bool
> isTransitive digraph
>      = if not (isDigraph digraph)
>           then errfun "isTransitive" digraph "digraph"
>        else
>        let (set, relation) = digraph
>        in
>        and [((elem (x,y) relation) /\ (elem (y,z) relation))          
>            ==> (elem (x,z) relation)                
>            | x <- set, y <- set, z <- set]

> relationalComposition :: (Show a, Eq b, Show c, Show b, Eq c, Eq a) => 
>                              Set (a,b) -> Set (b,c) -> Set (a,c)
> relationalComposition set1 set2 
>  = if not (normalForm set1)
>       then errfun "relationalComposition" set1 "relation"
>    else
>    if not (normalForm set2)
>       then errfun "relationalComposition" set2 "relation"
>    else
>    normalizeSet [(a,c) | (a,b) <- set1, (b', c) <- set2, b == b']

> equalityRelation :: (Eq a, Show a) => Set a -> Relation a
> equalityRelation set 
>  = if not (normalForm set)
>       then errfun "equalityRelation" set "set"
>    else [(e,e) | e <- set]

> relationalPower :: (Eq a, Show a) => Digraph a -> Int -> Relation a
> relationalPower digraph power
>  = if not (isDigraph digraph)
>       then errfun "relationalPower" digraph "digraph"
>    else
>    relationalPowerLoop digraph power
>    where
>    relationalPowerLoop (set,relation) 0 
>      = equalityRelation set
>    relationalPowerLoop (set,relation) n 
>      = relationalComposition 
>         (relationalPowerLoop (set,relation) (n-1)) relation

> reflexiveClosure :: (Eq a, Show a) => Digraph a -> Digraph a
> reflexiveClosure digraph
>  = if not (isDigraph digraph)
>       then errfun "reflexiveClosure" digraph "digraph"
>    else
>    let (set, relation) = digraph
>    in
>    (set, relation +++ (equalityRelation set))

> inverse :: Set (a,b) -> Set (b,a)
> inverse set = [(b,a) | (a,b) <- set]

> symmetricClosure :: (Eq a, Show a) => Digraph a -> Digraph a
> symmetricClosure digraph
>  = if not (isDigraph digraph)
>       then errfun "symmetricClosure" digraph "digraph"
>    else
>    let (set, relation) = digraph
>    in (set, relation +++ (inverse relation))

> transitiveClosure :: (Eq a, Show a) => Digraph a -> Digraph a
> transitiveClosure digraph
>  = if not (isDigraph digraph)
>       then errfun "transitiveClosure" digraph "digraph"
>    else
>    let (set, relation) = digraph
>        len = length set   
>        loop n power     
>             = if (n > len) 
>                  then []          
>                  else power +++ (loop (n+1) 
>                                  (relationalComposition power relation))
>    in
>    (set, loop 1 relation)   

> isPartialOrder :: (Eq a, Show a) => Digraph a -> Bool
> isPartialOrder digraph
>      = if not (isDigraph digraph)
>           then errfun "isPartialOrder" digraph "digraph"
>        else
>        isReflexive digraph /\
>        (isAntisymmetric digraph /\
>        isTransitive digraph)

> remTransArcs :: (Eq a, Show a) => Relation a -> Relation a
> remTransArcs relation
>  = relation ~~~ [(x,z) | (x,y) <- relation, (y',z) <- relation, y == y']
> 
> remRelArcs ::  (Eq a, Show a) => Relation a -> Relation a
> remRelArcs relation = relation ~~~ [(x,y) | (x,y) <- relation, x == y]
> 
> remReflexTransArcs :: (Eq a, Show a) => Relation a -> Relation a
> remReflexTransArcs relation
>  = remTransArcs (remRelArcs relation)

> isWeakest :: (Eq a, Show a) => Relation a -> a -> Bool
> isWeakest relation a 
>        = if not (normalForm relation)
>             then errfun "isWeakest" relation "relation"
>          else
>          and [a /= c | (b,c) <- remReflexTransArcs relation]

> isGreatest :: (Eq a, Show a) => Relation a -> a -> Bool
> isGreatest set a 
>        = if not (normalForm set)
>             then errfun "isGreatest" set "relation"
>          else
>          and [a /= b | (b,c) <- remReflexTransArcs set]

> weakestSet :: (Eq a, Show a) => Digraph a -> Set a
> weakestSet digraph
>        = if not (isDigraph digraph)
>             then errfun "weakestSet" digraph "digraph"
>          else
>          let (set, relation) = digraph
>          in
>          filter (isWeakest relation) set

> greatestSet :: (Eq a, Show a) => Digraph a -> Set a
> greatestSet digraph
>        = if not (isDigraph digraph)
>             then errfun "greatestSet" digraph "digraph"
>          else
>          let (set,relation) = digraph
>          in
>          filter (isGreatest relation) set

> isQuasiOrder :: (Eq a, Show a) => Digraph a -> Bool
> isQuasiOrder digraph
>      = if not (isDigraph digraph)
>           then errfun "isQuasiOrder" digraph "digraph"
>        else
>        isTransitive digraph /\
>        isIrreflexive digraph

> isChain :: (Eq a, Show a) => Set (a,a) -> Bool
> isChain rel
>  = let loop [] = True
>        loop ((a,b):ps) 
>          = let new_rel = [pr | pr <- rel, not (pr == (a,b))]
>            in
>            if (elem a (codomain new_rel) || elem b (domain new_rel)) 
>               then loop ps
>               else False
>    in loop rel 

> isLinearOrder :: (Eq a, Show a) => Digraph a -> Bool
> isLinearOrder digraph
>      = if not (isDigraph digraph)
>           then errfun "isLinearOrder" digraph "digraph"
>        else if not (isPartialOrder digraph)
>        then errfun "isLinearOrder" digraph "partial order"
>        else
>        let (set,relation) = digraph
>        in
>        isChain (remReflexTransArcs relation)

> removeFromRelation :: (Eq a, Show a) => a -> Set (a,a) -> Set (a,a)
> removeFromRelation elt relation
>      = loop relation
>        where   loop [] = []   
>                loop ((a,b):relation) = if ((elt == a) || (elt == b))        
>                                           then loop relation
>                                           else (a,b) : loop relation

> removeElt :: (Eq a, Show a) => a -> Digraph a -> Digraph a
> removeElt elt (set, relation) 
>      = (set ~~~ [elt],    
>         removeFromRelation elt relation)

> topsort :: (Eq a, Show a) => Digraph a -> Set a
> topsort digraph
>  = if not (isPartialOrder digraph)
>       then errfun "topsort" digraph "partial order"
>    else
>    let topsortLoop ([], relation) = []
>        topsortLoop (set, []) = []
>        topsortLoop digraph
>         = min_elt : topsortLoop (removeElt min_elt digraph)   
>           where   
>           min_elt = head (weakestSet digraph)
>    in topsortLoop digraph

> isEquivalenceRelation :: (Eq a, Show a) => Digraph a -> Bool
> isEquivalenceRelation digraph
>    = if not (isDigraph digraph)
>         then errfun "isEquivalenceRelation" digraph "digraph"
>      else
>      let (set,relation) = digraph
>      in 
>      (isReflexive digraph /\
>        (isSymmetric digraph /\ isTransitive digraph))


-------------------------------------------------------------------------------
			Chapter 9.  Functions
-------------------------------------------------------------------------------

> isFun :: (Eq a, Eq b, Show a, Show b) => 
>              Set a -> Set b -> Set (a,FunVals b) -> Bool
> isFun f_domain f_codomain fun 
>       = let actual_domain = domain fun
>         in normalForm actual_domain /\
>            setEq actual_domain f_domain

> data FunVals a = Undefined | Value a
>                     deriving (Eq, Show)

> isPartialFunction :: (Eq a, Eq b, Show a, Show b) => Set a -> Set b
>                            -> Set (a,FunVals b) -> Bool
> isPartialFunction f_domain f_codomain fun
>      = isFun f_domain f_codomain fun /\
>           elem Undefined (codomain fun)

> imageValues :: (Eq a, Show a) => Set (FunVals a) -> Set a
> imageValues f_codomain
>      = [v | (Value v) <- f_codomain]

> isSurjective :: (Eq a, Eq b, Show a, Show b) => Set a -> 
>                      Set b -> Set (a,FunVals b) -> Bool
> isSurjective f_domain f_codomain fun
>       = isFun f_domain f_codomain fun /\ 
>         setEq f_codomain (normalizeSet (imageValues (codomain fun)))

> isInjective :: (Eq a, Eq b, Show a, Show b) => Set a -> 
>                   Set b -> Set (a,FunVals b) -> Bool
> isInjective f_domain f_codomain fun 
>       = let fun_image = imageValues (codomain fun)
>         in isFun f_domain f_codomain fun /\
>            normalForm fun_image

> functionalComposition :: (Eq a, Eq b, Eq c, Show a, Show b, Show c) => 
>                           Set (a,FunVals b) -> Set (b,FunVals c) -> 
>                              Set (a,FunVals c)
> functionalComposition f1 f2 
>  = normalizeSet [(a,c) | (a,Value b) <- f1, (b', c) <- f2, b == b']

> isBijective :: (Eq a, Eq b, Show a, Show b) => Set a -> Set b
>                     -> Set (a,FunVals b) -> Bool
> isBijective f_domain f_codomain fun 
>       = isSurjective f_domain f_codomain fun /\ 
>         isInjective f_domain f_codomain fun 

> isPermutation
>   :: (Eq a, Show a) => Set a -> Set a -> Set (a,FunVals a) -> Bool
> isPermutation f_domain f_codomain fun 
>       = isBijective f_domain f_codomain fun /\
>         setEq f_domain f_codomain

> diagonal :: Int -> [(Int,Int)] -> [(Int,Int)]
> diagonal stop rest = let interval = [1 .. stop]
>                          in zip interval (reverse interval) ++ rest

> rationals :: [(Int, Int)]
> rationals = foldr diagonal [] [1..]


-------------------------------------------------------------------------------
	 Chapter 10.  Discrete Mathematics in Circuit Design
-------------------------------------------------------------------------------

> class Signal a where
>   inv :: a -> a
>   and2, or2, xor :: a -> a -> a

> instance Signal Bool where
>   inv False = True
>   inv True = False
>   and2 = (&&)
>   or2 = (||)
>   xor False False = False
>   xor False True  = True
>   xor True  False = True
>   xor True  True  = False


> -- halfAdd :: Signal a => a -> a -> (a,a)
> halfAdd a b = (and2 a b, xor a b)

> fullAdd :: Signal a => (a,a) -> a -> (a,a)
> fullAdd (a,b) c = (or2 w y, z)
>   where (w,x) = halfAdd a b
>         (y,z) = halfAdd x c


halfAdd False False
halfAdd False True
halfAdd True  False
halfAdd True  True

fullAdd (False, False) False
fullAdd (False, False) True
fullAdd (False, True)  False
fullAdd (False, True)  True
fullAdd (True,  False) False
fullAdd (True,  False) True
fullAdd (True,  True)  False
fullAdd (True,  True)  True


> add4 :: Signal a => a -> [(a,a)] -> (a,[a])

> add4 c [(x0,y0),(x1,y1),(x2,y2),(x3,y3)] =
>        (c0, [s0,s1,s2,s3])
>   where (c0,s0) = fullAdd (x0,y0) c1
>         (c1,s1) = fullAdd (x1,y1) c2
>         (c2,s2) = fullAdd (x2,y2) c3
>         (c3,s3) = fullAdd (x3,y3) c


    Example: addition of 3 + 8
       3 + 8
       =   0011   (  2+1 =  3)
         + 1000   (    8 =  8)
       =   1011   (8+2+1 = 11)
    Calculate this by evaluating
       add4 False [(False,True),(False,False),(True,False),(True,False)]
    The expected result is
       (False, [True,False,True,True])

> mscanr :: (b->a->(a,c)) -> a -> [b] -> (a,[c])
> mscanr f a [] = (a,[])
> mscanr f a (x:xs) =
>   let (a',ys) = mscanr f a xs
>       (a'',y) = f x a'
>   in (a'', y:ys)

> rippleAdd :: Signal a => a -> [(a,a)] -> (a, [a])
> rippleAdd c zs = mscanr fullAdd c zs

    Example: addition of 23+11
       23 + 11
       =   010111   (16+4+2+1 = 23)
         + 001011   (   8+2+1 = 11) with carry input = 0
       =   100010   (    32+2 = 34) with carry output = 0
    Calculate with the circuit by evaluating
       rippleAdd False [(False,False),(True,False),(False,True),
                      (True,False),(True,True),(True,True)]
    The expected result is
       (False, [True,False,False,False,True,False])










