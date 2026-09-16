import FormalConjectures.Util.ProblemImports
open Nat Finset

lemma algebra_ineq (p M x : ℕ) (hp5 : 5 ≤ p) (hx : M - p + 3 ≤ x) (hM : p ≤ M) :
  p * M - p * p + 2 * p + 2 ≤ p * x := by
  have h1 : p * (M - p + 3) ≤ p * x := Nat.mul_le_mul_left p hx
  have h2 : p * M - p * p + 3 * p ≤ p * (M - p + 3) := by
    -- we can use zify and ring
    zify [show p ≤ M by omega, show p * p ≤ p * M by nlinarith]
    push_cast
    -- wait, p*(M - p + 3) needs no sub condition if M >= p
    sorry
  have h3 : p * M - p * p + 2 * p + 2 ≤ p * M - p * p + 3 * p := by
    zify [show p * p ≤ p * M by nlinarith]
    push_cast
    linarith
  omega
