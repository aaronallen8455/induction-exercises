module InductionExercises

-- Solutions to the exercises from
-- https://jamesrwilcox.com/InductionExercises.html

import Data.List as L
import Data.Nat as N

%hide Data.List.reverse
%hide Prelude.sum
%hide Prelude.reverse
%hide Prelude.map

lamPlusAssoc : (x : Nat) -> (y : Nat)
            -> (\z => x + (y + z)) = (\z => (x + y) + z)
lamPlusAssoc 0 y = Refl
lamPlusAssoc (S k) y =
  cong (S .) $ lamPlusAssoc k y

sum : List Nat -> Nat
sum [] = 0
sum (x :: xs) = x + sum xs

--------------------------------------------------------------------------------
-- Tail-call recursive Sum
--------------------------------------------------------------------------------

sumTc : List Nat -> Nat -> Nat
sumTc [] acc = acc
sumTc (x :: xs) acc = sumTc xs (x + acc)

sum' : List Nat -> Nat
sum' l = sumTc l 0

tcSumLemma : (x : Nat) -> (xs : List Nat) -> sumTc xs x = plus x (sum xs)
tcSumLemma x [] = sym $ N.plusZeroRightNeutral x
tcSumLemma x (y :: xs) =
  rewrite N.plusAssociative x y (sum xs)
  in rewrite N.plusCommutative x y
  in tcSumLemma (y + x) xs

-- Proof that the tail recursive sum is equivalent to the naive one
total
tcSumProof : (l : List Nat) -> sum' l = sum l
tcSumProof [] = Refl
tcSumProof (x :: xs) =
  rewrite N.plusZeroRightNeutral x in tcSumLemma x xs

--------------------------------------------------------------------------------
-- CPS Sum
--------------------------------------------------------------------------------

sumCont : (l : List Nat) -> (Nat -> Nat) -> Nat
sumCont [] f = f 0
sumCont (x :: xs) f = sumCont xs (f . (x +))

sum'' : List Nat -> Nat
sum'' l = sumCont l id

contSumLemma : (z : Nat) -> (xs : List Nat)
            -> sumCont xs (\x => z + x) = plus z (sum xs)
contSumLemma z [] = Refl
contSumLemma z (y :: xs) =
  rewrite N.plusAssociative z y (sum xs)
  in rewrite lamPlusAssoc z y
  in contSumLemma (z + y) xs

total
contSumProof : (l : List Nat) -> sum'' l = sum l
contSumProof [] = Refl
contSumProof (z :: xs) = contSumLemma z xs

--------------------------------------------------------------------------------
-- Reverse
--------------------------------------------------------------------------------

reverse : List a -> List a
reverse [] = []
reverse (x :: xs) = reverse xs ++ [x]

reverseTc : List a -> List a -> List a
reverseTc [] ys = ys
reverseTc (x :: xs) ys = reverseTc xs (x :: ys)

reverse' : List a -> List a
reverse' xs = reverseTc xs []

reverseTcLemma : (acc : List a) -> (xs : List a)
              -> reverseTc xs acc = reverse xs ++ acc
reverseTcLemma x [] = Refl
reverseTcLemma x (y :: xs) =
  rewrite sym $ L.appendAssociative (reverse xs) [y] x
  in reverseTcLemma (y :: x) xs

total
reverseTcProof : (xs : List a) -> reverse' xs = reverse xs
reverseTcProof [] = Refl
reverseTcProof (x :: xs) = reverseTcLemma [x] xs

doubleRevLemma' : (xs : List a) -> (x : List a) -> (ys : List a)
               -> reverse' xs ++ (x ++ ys) = reverseTc xs x ++ ys
doubleRevLemma' [] x ys = Refl
doubleRevLemma' (y :: xs) x ys =
  let hyp = doubleRevLemma' xs (y :: x) ys
      hyp' = doubleRevLemma' xs [y] (x ++ ys)
  in sym hyp' `trans` hyp

doubleRevLemma : (x : List a) -> (xs : List a)
              -> reverse' (reverseTc xs x) = reverse' x ++ xs
doubleRevLemma x [] = rewrite L.appendNilRightNeutral (reverse' x) in Refl
doubleRevLemma x (y :: xs) =
  rewrite doubleRevLemma' x [y] xs
  in doubleRevLemma (y :: x) xs

doubleRev : (xs : List a) -> reverse' (reverse' xs) = xs
doubleRev [] = Refl
doubleRev (x :: xs) = doubleRevLemma [x] xs

--------------------------------------------------------------------------------
-- Map
--------------------------------------------------------------------------------

map : (a -> b) -> List a -> List b
map f [] = []
map f (x :: xs) = f x :: map f xs

mapTc : (a -> b) -> List a -> List b -> List b
mapTc f [] ys = reverse' ys
mapTc f (x :: xs) ys = mapTc f xs (f x :: ys)

map' : (a -> b) -> List a -> List b
map' f xs = mapTc f xs []

revLemma' : (x : List a) -> (xs : List a) -> (f : (a -> b))
         -> map f (reverseTc xs x) = reverseTc (map f xs) (map f x)
revLemma' x [] f = Refl
revLemma' x (y :: xs) f = revLemma' (y :: x) xs f

revLemma : (xs : List a) -> (f : a -> b)
        -> map f (reverse' xs) = reverse' (map f xs)
revLemma [] f = Refl
revLemma (x :: xs) f = revLemma' [x] xs f

revOut' : (y : List a) -> (z : List a)
       -> reverseTc y z = reverse' y ++ z
revOut' y [] = sym $ L.appendNilRightNeutral (reverse' y)
revOut' y (x :: xs) =
  rewrite reverseTcProof y
  in reverseTcLemma (x :: xs) y

revOut : (xs : List a) -> (y : List a) -> (z : List a)
      -> reverseTc (xs ++ y) z = reverse' y ++ reverseTc xs z
revOut [] y z = revOut' y z
revOut (x :: xs) y z = revOut xs y (x :: z)

distributeMap : (f : a -> b) -> (xs : List a) -> (ys : List a)
             -> map f (xs ++ ys) = map f xs ++ map f ys
distributeMap f [] ys = Refl
distributeMap f (x :: xs) ys = cong (f x ::) $ distributeMap f xs ys

mapTcLemma' : (f : a -> b) -> (y : a) -> (x : List a)
           -> f y :: map f (reverse' x) = map f (reverse' (x ++ [y]))
mapTcLemma' f y xs =
  cong (map f) (sym (revOut xs [y] []))

mapTcLemma : (x : List a) -> (xs : List a) -> (f : a -> b)
          -> mapTc f xs (map f (reverse' x)) = map f x ++ map f xs
mapTcLemma x [] f =
  rewrite revLemma x f
  in rewrite doubleRev (map f x)
  in rewrite L.appendNilRightNeutral $ map f x
  in Refl
mapTcLemma x (y :: xs) f =
  rewrite L.appendAssociative (map f x) [f y] (map f xs)
  in rewrite sym $ distributeMap f x [y]
  in rewrite mapTcLemma' f y x
  in mapTcLemma (x ++ [y]) xs f

total
mapTcProof : (f : a -> b) -> (xs : List a) -> map' f xs = map f xs
mapTcProof f [] = Refl
mapTcProof f (x :: xs) = mapTcLemma [x] xs f

--------------------------------------------------------------------------------
-- Arithmetic Expression Languages
--------------------------------------------------------------------------------

data Expr : Type where
  Const : Nat -> Expr
  Plus : Expr -> Expr -> Expr

eval : Expr -> Nat
eval (Const k) = k
eval (Plus x y) = eval x + eval y

evalTc : Expr -> Nat -> Nat
evalTc (Const j) k = j + k
evalTc (Plus x y) k = evalTc x (evalTc y k)

eval' : Expr -> Nat
eval' e = evalTc e 0

evalTcLemma' : (e : Expr) -> (x : Nat) -> (y : Nat)
            -> evalTc e y + x = evalTc e (y + x)
evalTcLemma' (Const k) x y = sym $ N.plusAssociative k y x
evalTcLemma' (Plus a b) x y =
  rewrite evalTcLemma' a x (evalTc b y)
  in rewrite evalTcLemma' b x y
  in Refl

evalTcLemma : (e : Expr) -> eval e = evalTc e 0
evalTcLemma (Const k) = sym $ N.plusZeroRightNeutral k
evalTcLemma (Plus x y) =
  rewrite evalTcLemma x
  in rewrite evalTcLemma y
  in rewrite evalTcLemma' x (eval' y) 0
  in Refl

total
evalTcProof : (e : Expr) -> eval e = eval' e
evalTcProof (Const k) = sym $ N.plusZeroRightNeutral k
evalTcProof (Plus x y) =
  rewrite evalTcLemma x
  in rewrite evalTcLemma y
  in rewrite evalTcLemma' x (eval' y) 0
  in Refl

--------------------------------------------------------------------------------
-- Expression CPS
--------------------------------------------------------------------------------

evalCont : Expr -> (Nat -> r) -> r
evalCont (Const k) f = f k
evalCont (Plus x y) f = evalCont y $ \n2 =>
                        evalCont x $ \n1 => f (n1 + n2)

eval'' : Expr -> Nat
eval'' x = evalCont x (\z => z)

evalContLemma : (x : Expr) -> (f : Nat -> Nat) -> evalCont x f = f (eval x)
evalContLemma (Const k) f = Refl
evalContLemma (Plus x y) f =
  let one = evalContLemma y (\n => evalCont x (\n1 => f (n1 + n)))
      two = evalContLemma x (\n => f (n + eval y))
  in one `trans` two

total
evalContProof : (e : Expr) -> eval'' e = eval e
evalContProof e = evalContLemma e id

--------------------------------------------------------------------------------
-- Compiling to Stack Language
--------------------------------------------------------------------------------

data Instr = Push Nat | Add

Prog : Type
Prog = List Instr

Stack : Type
Stack = List Nat

run : (p : Prog) -> (s : Stack) -> Stack
run [] s = s
run (x :: xs) s =
  let s' = case x of
                Push n => n :: s
                Add => case s of
                            a1 :: a2 :: rest => a1 + a2 :: rest
                            _ => s
  in run xs s'

compile : (e : Expr) -> Prog
compile (Const k) = [Push k]
compile (Plus x y) = compile x ++ compile y ++ [Add]

compileCorrectProof : (e : Expr) -> run (compile e) [] = [eval e]
compileCorrectProof (Const k) = Refl
compileCorrectProof (Plus x y) = ?compileCorrectProof_rhs_2
