import Data.Vect

-- total
-- GT : Nat -> Nat -> Bool
-- GT k Z = True
-- GT Z (S j) = False
-- GT (S k) (S j) = GT k j

total
how_1 : (x : LTE n right) -> Vect (S right) String
how_1 LTEZero {right = Z} = ["foo"]
how_1 LTEZero {right = (S k)} = "foo" :: how_1 LTEZero {right=k}
how_1 (LTESucc x) = "foo" :: how_1 x

atLeast: {m: Nat} -> (n: Nat) -> { auto p: m `GT` n } -> Vect m String
atLeast n {p = (LTESucc x)} = how_1 x --replicate (S n) "foo"

takeV : (n: Nat) -> Vect m String -> { auto p: m `GTE` n } -> Vect n String
takeV Z xs {p = LTEZero} = []
takeV (S k) (x::xs) {p = (LTESucc y)} = x :: takeV k xs

takeF : (n: Nat) -> Vect m String -> { default ItIsJust p: IsJust (natToFin m n) } -> Vect n String
takeF Z xs = []
takeF (S _) _ {p} = ?what
