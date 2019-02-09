data InRange : Nat -> Nat -> Nat -> Type where
  MkInRange : { auto p: n `GTE` x } ->
              { auto q: n `LTE` y } ->
              InRange n x y

overMax : (contra : LTE n y -> Void) -> InRange n x y -> Void
overMax contra (MkInRange {q}) = contra q

notYetMin : (contra : LTE x n -> Void) -> InRange n x y -> Void
notYetMin contra (MkInRange {p}) = contra p

IsInRange : (n: Nat) -> (x: Nat) -> (y:  Nat) -> Dec (InRange n x y)
IsInRange n x y with (isLTE x n)
  IsInRange n x y | with_pat1 with (isLTE n y)
    IsInRange n x y | (Yes prf) | (Yes z) = Yes MkInRange
    IsInRange n x y | (No contra) | _ = No (notYetMin contra)
    IsInRange n x y | _ | (No contra) = No (overMax contra)

data ValidPassword : String -> Nat -> Nat -> Type where
  OfCourse: { auto p: InRange (length (unpack xs)) x y } ->
        ValidPassword xs x y

validPass : ValidPassword "abcde" 4 8
validPass = OfCourse

lengthOutOfRange : (xs: String) -> (contra : InRange (length (unpack xs)) 4 8 -> Void) ->
                  ValidPassword xs 4 8 -> Void
lengthOutOfRange xs contra (OfCourse {p}) = contra p

isValidPass : (xs: String) -> Dec (ValidPassword xs 4 8)
isValidPass xs with (IsInRange (length (unpack xs)) 4 8)
  isValidPass xs | (Yes prf) = Yes OfCourse
  isValidPass xs | (No contra) = No (lengthOutOfRange xs contra)

main : IO ()
main = do
  pass <- getLine
  case isValidPass pass of
    Yes _ => putStrLn "Valid"
    No _ => putStrLn "Not good"
