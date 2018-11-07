data SnocList : List a -> Type where
  Empty : SnocList []
  Snoc : (rest: SnocList xs) -> SnocList (xs ++ [x])

appendNilNeut : (xs: List a) -> xs ++ [] = xs
appendNilNeut [] = Refl
appendNilNeut (x :: xs) = let hypo = appendNilNeut xs in rewrite hypo in Refl

appendAssoc : (lefts: List a) -> (mid: List a) -> (rights: List a) -> lefts ++ (mid ++ rights) = (lefts ++ mid) ++ rights
appendAssoc [] mid rights = Refl
appendAssoc (x :: xs) mid rights = rewrite appendAssoc xs mid rights in Refl

snocListAccu : {lefts: List a} -> SnocList lefts -> (rights: List a) -> SnocList (lefts++rights)
snocListAccu {lefts = lefts} slst [] = rewrite appendNilNeut lefts in slst
snocListAccu {lefts = lefts} slst (x :: xs) =
  let lefts1 = snocListAccu (Snoc slst {x=x}) xs in
      rewrite appendAssoc lefts [x] xs in lefts1

snocList : (xs: List a) -> SnocList xs
snocList xs = snocListAccu Empty xs

myReverse : List a -> List a
myReverse xs with (snocList xs)
  myReverse [] | Empty = []
  myReverse (ys ++ [x]) | (Snoc rest) = let xs1 = myReverse ys | rest in x::xs1

main : IO ()
main = putStr $ foldl (++) "" $ map show $ myReverse [1..1000]
