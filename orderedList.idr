data OrderedList : List a -> Type where
  Nia: OrderedList []
  Hia: OrderedList (x::[])
  Thia: Ord a => { x: a }
              -> { y: a }
              -> { auto p : x >= y = True }
              -> OrderedList (y::xs)
              -> OrderedList (x::y::xs)

showOrdered: (xs : List Int) -> { p: OrderedList xs} -> String
showOrdered xs = "got it"

-- Uninhabited (OrderedList {a} (x::y::xs)) where
--   uninhabited (Thia {x} {y} {p = Void} _) impossible

isOrdered: Ord a => (xs : List a) -> Dec (OrderedList xs)
isOrdered [] = Yes Nia
isOrdered (x :: []) = Yes Hia
isOrdered (x :: (y :: xs)) with (decEq (x >= y) True)
  isOrdered (x :: (y :: xs)) | (Yes prf) = ?isOrdered_rhs_3_rhs_1
  isOrdered (x :: (y :: xs)) | (No contra) = No ?hlno

main : IO ()
main = do
  putStrLn "enter numbers in CSV"
  numbers <- getLine
  let ls = split (== ',') numbers
  let xs = map (cast {to=Int}) ls
  case isOrdered xs of
    (Yes prf) => putStrLn $ showOrdered xs {p = prf}
    (No contra) => putStrLn "list not in order"

t : 2 + 2 = 5 -> Void
t Refl impossible

-- = let (_ ** ol) = order (x::xs) in
--                               case y >= x of
--                                 False => ?hole1_1
--                                 True => ((y::x::xs) ** Thia ol)
