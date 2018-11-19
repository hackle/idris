data ElemOfList : a -> List a -> Type where
  Here : ElemOfList x (x::xs)
  There : ElemOfList x (x::xs) -> ElemOfList x (y::x::xs)

isIn : ElemOfList 2 [1, 2, 3]
isIn = There Here

data Last : List a -> a -> Type where
  LastOne : Last [x] x
  LastCons : Last xs x -> Last (y::xs) x

noLastOne : (contra : (x = y) -> Void) -> Last [y] x -> Void
noLastOne contra LastOne = contra Refl
noLastOne _ (LastCons LastOne) impossible
noLastOne _ (LastCons (LastCons _)) impossible

Uninhabited (Last [] x) where
  uninhabited LastOne impossible
  uninhabited (LastCons _) impossible

Uninhabited (Last [x] y) where
  uninhabited (LastCons _) impossible

notEqual : (contra : (x = y) -> Void) -> Last [y] x -> Void
notEqual contra LastOne = contra Refl
notEqual _ (LastCons LastOne) impossible
notEqual _ (LastCons (LastCons _)) impossible

noSucc : (contra : Last (x :: xs) x1 -> Void) -> Last (y1 :: (x :: xs)) x1 -> Void
noSucc contra (LastCons prf) = contra prf

isLast : DecEq a => (x: a) -> (xs: List a) -> Dec (Last xs x)
isLast x [] = No absurd
isLast x [y] = case decEq x y of
                (Yes Refl) => Yes LastOne
                (No contra) => No (notEqual contra)
isLast x (y :: y1 :: ys) = case isLast x (y1 :: ys) of
                      (Yes prf) => Yes (LastCons prf)
                      (No contra) => No (noSucc contra)
