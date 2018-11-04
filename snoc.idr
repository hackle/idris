data SnocList : List a -> Type where
  Empty : SnocList []
  Snoc : (rest: SnocList xs) -> SnocList (xs ++ [x])

reverseHelper : (input: List a) -> SnocList input -> List a
reverseHelper [] Empty = []
reverseHelper (xs ++ [x]) (Snoc rest) = x::reverseHelper xs rest

appendNilNeut : (xs: List a) -> xs ++ [] = xs
appendNilNeut [] = Refl
appendNilNeut (x :: xs) = rewrite appendNilNeut xs in Refl

appendAssoc : (lefts: List a) -> (mid: a) -> (rights: List a) -> lefts ++ mid::rights = (lefts ++ [mid]) ++ rights
appendAssoc [] mid rights = Refl
appendAssoc (x :: xs) mid rights = rewrite appendAssoc xs mid rights in Refl

snocListAccu : {lefts: List a} -> SnocList lefts -> (rights: List a) -> SnocList (lefts++rights)
snocListAccu {lefts = lefts} slst [] = rewrite appendNilNeut lefts in slst
snocListAccu {lefts = lefts} slst (x :: xs) =
  let lefts1 = snocListAccu (Snoc slst {x=x}) xs in
      rewrite appendAssoc lefts x xs in lefts1

snocList : (xs: List a) -> SnocList xs
snocList xs = snocListAccu Empty xs

myReverse : List a -> List a
myReverse xs = reverseHelper xs $ snocList xs
