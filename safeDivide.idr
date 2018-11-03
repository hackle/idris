import Data.Vect

div : Double -> (n: Double) -> { auto prf: n > 0 = True } -> Double
div m n {prf} = m / n

index1 : (idx : Nat) -> (xs : Vect n a) -> { auto prf: idx < n = True } -> Maybe a
index1 idx {n} xs = ?index1_rhs
