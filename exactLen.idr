import Data.Vect
--
-- areSame : (m: Nat) -> (n: Nat) -> Maybe (m = n)
-- areSame Z Z = Just Refl
-- areSame Z (S k) = Nothing
-- areSame (S k) Z = Nothing
-- areSame (S k) (S j) = case areSame k j of
--                            Nothing => Nothing
--                            (Just Refl) => Just Refl
--
-- exactLen : (m: Nat) -> Vect n a -> Maybe (Vect m a)
-- exactLen m xs {n} = case areSame m n of
--                          Nothing => Nothing
--                          (Just Refl) => Just xs
--
-- same_cons : {xs: List a} -> {ys: List a} -> xs = ys -> x::xs = x::ys
-- same_cons {x} prf = cong { f = \ls => x::ls } prf

same_lists : {xs: List a} -> {ys: List a} -> x = y -> xs = ys -> x::xs = y::ys
same_lists Refl Refl = Refl --cong { f=cin }  lsts_equal


greater: (a: Nat) -> (b: Nat) -> { auto p: a `GT` b } -> Nat
