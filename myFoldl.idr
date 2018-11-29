myFoldr : (elem -> acc -> acc) -> acc -> List elem -> acc
myFoldr f acc [] = acc
myFoldr f acc (x :: xs) = f x (myFoldr f acc xs)

myFoldl : (acc -> elem -> acc) -> acc -> List elem -> acc
myFoldl f initial xs = let f1 = myFoldr (\elem, g => \pre => g (f pre elem)) id xs in f1 initial

-- (List elem -> List elem) -> elem -> (List elem -> List elem)
--
--
-- myFoldr (::) [] [1..3]
-- (1 :: (2 :: (3 :: [])))
--
-- f x1 (f x2 (f acc x3))
--
-- acc x3
-- \xs -> id x3 :: xs
--
-- acc x2 ->
-- \xs1 -> acc (x2 :: xs1)
--
-- acc x1
-- \xs3 -> acc (x1 :: xs3)
