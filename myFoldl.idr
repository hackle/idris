myFoldr : (elem -> acc -> acc) -> acc -> List elem -> acc
myFoldr f acc [] = acc
myFoldr f acc (x :: xs) = f x (myFoldr f acc xs)

foldOneElem : (g : acc -> elem -> acc) -> (elem: elem) -> (prev: acc -> acc) -> ((cur: acc) -> acc)
foldOneElem g elem prev cur = prev (g cur elem)

myFoldl : Foldable t => (acc -> elem -> acc) -> acc -> t elem -> acc
myFoldl g initial xs = let foldFunc = foldr (foldOneElem g) id xs in foldFunc initial


myFold1 : (f: elem -> acc -> acc) -> (init: acc) -> (xs: List elem) -> acc
myFold1 f init [] = init
myFold1 f init (x :: xs) = myFold1 f (f x init) xs

myFold2 : (f: elem -> acc -> acc) -> (init: acc) -> (xs: List elem) -> acc
myFold2 f init [] = init
myFold2 f init (x :: xs) = f x (myFold2 f init xs)

-- foldLeftCheat : Foldable t => (acc -> elem -> acc) -> acc -> t elem -> acc
-- foldLeftCheat f init xs = foldr (flip f) init (reverse xs)

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
