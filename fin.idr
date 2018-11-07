import Data.Fin
import Data.Vect

indexFin : {n: Nat} -> Fin n -> Vect n a -> a
indexFin FZ (x :: xs) = x
indexFin (FS s) (x :: xs) = indexFin s xs
