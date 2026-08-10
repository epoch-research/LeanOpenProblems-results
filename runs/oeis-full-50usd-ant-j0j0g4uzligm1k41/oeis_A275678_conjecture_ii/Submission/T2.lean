import FormalConjectures.Util.ProblemImports
open Nat
example (a b c p q r : ℤ)
    (hab : a ≤ b) (hbc : b ≤ c) (ha : 0 < a)
    (hp : 2*p ≤ a) (hp' : -a ≤ 2*p) (hq : 2*q ≤ a) (hq' : -a ≤ 2*q)
    (hr : 2*r ≤ b) (hr' : -b ≤ 2*r)
    (e1 : 0 ≤ a+b+2*p+2*q+2*r) (e2 : 0 ≤ a+b-2*p+2*q-2*r)
    (e3 : 0 ≤ a+b-2*p-2*q+2*r) (e4 : 0 ≤ a+b+2*p-2*q-2*r) :
    a^3 ≤ 7*(a*b*c - a*r^2 - c*p^2 + 2*p*q*r - b*q^2) := by
  have hba : 0 ≤ b - a := by omega
  have hcb : 0 ≤ c - b := by omega
  have hP1 : 0 ≤ a - 2*p := by omega
  have hP2 : 0 ≤ a + 2*p := by omega
  have hQ1 : 0 ≤ a - 2*q := by omega
  have hQ2 : 0 ≤ a + 2*q := by omega
  have hR1 : 0 ≤ b - 2*r := by omega
  have hR2 : 0 ≤ b + 2*r := by omega
  nlinarith [mul_nonneg hcb (mul_nonneg hQ1 hQ2), mul_nonneg hcb (mul_nonneg hP1 hP2),
    mul_nonneg hba (mul_nonneg hQ1 hQ2), mul_nonneg hba (mul_nonneg hP1 hP2),
    mul_nonneg ha.le (mul_nonneg hR1 hR2), mul_nonneg hba (mul_nonneg hR1 hR2),
    mul_nonneg (mul_nonneg hba hba) hcb, mul_nonneg (mul_nonneg hcb hcb) hba,
    mul_nonneg e1 (mul_nonneg hP1 hQ1), mul_nonneg e2 (mul_nonneg hP2 hQ1),
    mul_nonneg e3 (mul_nonneg hP2 hQ2), mul_nonneg e4 (mul_nonneg hP1 hQ2),
    mul_nonneg (mul_nonneg ha.le hba) hcb, mul_nonneg ha.le (mul_nonneg hba hcb)]
