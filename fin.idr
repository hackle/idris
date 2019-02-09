import Data.Fin
import Data.Vect

indexFin : {n: Nat} -> Fin n -> Vect n a -> a
indexFin FZ (x :: xs) = x
indexFin (FS s) (x :: xs) = indexFin s xs

data ValidPassword : (min: Nat) -> (max: Nat) -> Type where
  MkPass: (xs: String) ->
          { auto p: length xs >= min && length xs <= max = True } ->
          ValidPassword min max

validPassword : ValidPassword 4 8
validPassword = MkPass "abc"
