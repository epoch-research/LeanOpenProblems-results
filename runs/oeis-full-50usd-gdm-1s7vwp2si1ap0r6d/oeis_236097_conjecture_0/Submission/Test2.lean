import FormalConjectures.Util.ProblemImports

open Nat Finset
open scoped Nat.Prime

noncomputable def A236097 (n : ℕ) : ℕ :=
  (Icc 1 (n - 3)).sum fun k =>
    let p_val := k.totient + (n - k).totient / 2 + 1
    let p_prime := Nat.nth Nat.Prime (p_val - 1)
    if p_val.Prime ∧ (p_prime - p_val - 1).Prime ∧ (p_prime - p_val + 1).Prime then 1
    else 0

set_option google.answer "always_true"

theorem A236097_test : ∀ (n : ℕ), n > 31 → A236097 n > 0 :=
  answer(sorry)

def helper : (∀ (n : ℕ), n > 31 → A236097 n > 0) ↔ True := answer(sorry)

#print axioms helper
#print axioms A236097_test

