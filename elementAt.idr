import Data.Vect

elementAt : (idx: Nat) -> Vect (S n) a -> { auto prf: n `GTE` idx } -> a
elementAt Z (x :: xs) = x
elementAt (S k) (x :: xs) {prf = (LTESucc y)} = elementAt k xs
