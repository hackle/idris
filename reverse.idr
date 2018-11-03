import Data.Vect
import NatEq

reverse1 : Vect n a -> Vect n a
reverse1 [] = []
reverse1 {n=S k}(x :: xs) = rewrite plusCommutative 1 k in reverse1 xs ++ [x]

plusZeroNeutral : (n: Nat) -> n = n + 0
plusZeroNeutral Z = Refl
plusZeroNeutral (S k) = let prf1 = plusZeroNeutral k in cong prf1

myPlusCommute : (m: Nat) -> (n: Nat) -> m + n = n + m
myPlusCommute Z n = rewrite plusZeroNeutral n in Refl
myPlusCommute (S k) n = rewrite myPlusCommute k n in
                          rewrite plusSuccRightSucc n k in
                            Refl

myReserve : Vect n a -> Vect n a
myReserve xs = myReserveAccu [] xs where
  myReserveAccu : Vect n a -> Vect m a -> Vect (n + m) a
  myReserveAccu [] [] = []
  myReserveAccu [] (x :: ys) = myReserveAccu [x] ys
  myReserveAccu {n} xs [] = rewrite plusZeroRightNeutral n in xs
  myReserveAccu {n} {m=S len} xs (y :: ys) =
    let xs1 = myReserveAccu (y::xs) ys in
        rewrite sym $ plusSuccRightSucc n len in
          xs1
