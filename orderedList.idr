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

restNotOrdered : (contra : OrderedList (y :: xs) -> Void) -> OrderedList (x :: (y :: xs)) -> Void
restNotOrdered contra (Thia x) = contra x

headsNotOrdered : Ord a => { x, y : a } -> (contra : ((x >= y) = True) -> Void) -> OrderedList (x :: (y :: xs)) -> Void
headsNotOrdered contra (Thia ys {a} {p}) = contra p

isOrdered: Ord a => (xs : List a) -> Dec (OrderedList xs)
isOrdered [] = Yes Nia
isOrdered (x :: []) = Yes Hia
isOrdered (x :: (y :: xs)) with (decEq (x >= y) True)
  isOrdered (x :: (y :: xs)) | (pat) with (isOrdered (y::xs))
    isOrdered (x :: (y :: xs)) | ((Yes prf)) | (Yes z) = Yes (Thia z)
    isOrdered (x :: (y :: xs)) | _ | (No contra) = No (restNotOrdered contra)
    isOrdered (x :: (y :: xs)) | ((No contra)) | _ = No (headsNotOrdered contra)

main : IO ()
main = do
  putStrLn "enter numbers in CSV"
  numbers <- getLine
  let ls = split (== ',') numbers
  let xs = map (cast {to=Int}) ls
  case isOrdered xs of
    (Yes prf) => putStrLn $ showOrdered xs {p = prf}
    (No contra) => putStrLn "list not in order"
