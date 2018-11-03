import Data.Vect

headUnequal : DecEq a => { xs: Vect n a} -> { ys: Vect n a } ->
  (contra: (x = y) -> Void) -> ((x::xs) = (y::ys)) -> Void
headUnequal contra Refl = contra Refl

tailUnequal : DecEq a => {xs: Vect n a} -> {ys: Vect n a} ->
  (contra: (xs=ys) -> Void) -> ((x::xs) = (y::ys)) -> Void
tailUnequal contra Refl = contra Refl

data MyVect : Nat -> Type -> Type where
  Nil : MyVect 0 a
  Cons : a -> MyVect n a -> MyVect (S n) a

hl3 : (contra : (x = z) -> Void) -> (Cons x y = Cons z w) -> Void
hl3 contra Refl = contra Refl

decEq_hls1_3 : (contra : (y = w) -> Void) -> (Cons x y = Cons x w) -> Void
decEq_hls1_3 contra Refl = contra Refl

implementation DecEq a => DecEq (MyVect n a) where
  decEq [] [] = Yes Refl
  decEq (Cons x y) (Cons z w) = case decEq x z of
                                     (Yes Refl) => case decEq y w of
                                                         (Yes Refl) => Yes Refl
                                                         (No contra) => No (decEq_hls1_3 contra)
                                     (No contra) => No (hl3 contra)
  -- decEq : (v1: MyVect n a) -> (v2: MyVect n a) -> Dec (v1 = v2)
