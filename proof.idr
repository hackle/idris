import Data.Vect

addNilAssoc : y = plus y 0
addNilAssoc {y = Z} = Refl
addNilAssoc {y = (S k)} = rewrite addNilAssoc {y=k} in Refl


addSuccAssoc : (y : Nat) -> (k : Nat) -> S (plus y k) = plus y (S k)
addSuccAssoc Z k = Refl
addSuccAssoc (S j) k = rewrite addSuccAssoc j k in Refl

natAddAssoc : (x: Nat) -> (y: Nat) -> x + y = y + x
natAddAssoc Z y = addNilAssoc
natAddAssoc (S k) y = rewrite natAddAssoc k y in (addSuccAssoc y k)

reverseV : Vect n a -> Vect n a
reverseV [] = []
reverseV {n=S m} (x :: xs) = let xs1 = reverseV xs in rewrite natAddAssoc 1 m in xs1 ++ [x]

isA : (s: String) -> (case s of
                      "a" => Bool
                      _ => List String)
isA "a" = False
isA x = (the (List String) [x])
