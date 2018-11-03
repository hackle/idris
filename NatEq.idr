module NatEq

liftContra : (contra : (k = j) -> Void) -> (S k = S j) -> Void
liftContra contra Refl = contra Refl

zeroNotEqualToSucc : (0 = S k) -> Void
zeroNotEqualToSucc Refl impossible

succNotEqualToZero : (S k = 0) -> Void
succNotEqualToZero Refl impossible

DecEq1 : (m: Nat) -> (n: Nat) -> Dec (m = n)
DecEq1 Z Z = Yes Refl
DecEq1 Z (S k) = No zeroNotEqualToSucc
DecEq1 (S k) Z = No succNotEqualToZero
DecEq1 (S k) (S j) = case DecEq1 k j of
                          (Yes prf) => Yes (cong prf)
                          (No contra) => No (liftContra contra)

SuccPlusEqPlusSuc_rhs_1 : (k : Nat) -> S (S (plus k 0)) = S (plus k 1)
SuccPlusEqPlusSuc_rhs_1 Z = Refl
SuccPlusEqPlusSuc_rhs_1 (S k) = cong (SuccPlusEqPlusSuc_rhs_1 k)

export
SuccPlusEqPlusSuc : (m: Nat) -> (n: Nat) -> S (m + n) = m + S n
SuccPlusEqPlusSuc Z n = Refl
SuccPlusEqPlusSuc (S k) n = let succ1 = SuccPlusEqPlusSuc k n in cong succ1
