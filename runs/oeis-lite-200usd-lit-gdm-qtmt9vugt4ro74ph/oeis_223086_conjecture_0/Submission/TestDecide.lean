import FormalConjectures.Util.ProblemImports

open Nat

def A006368_map_inv (m : ℕ) : ℕ :=
  if m % 3 = 0 then
    2 * (m / 3)
  else if m % 3 = 1 then
    4 * (m / 3) + 1
  else
    4 * (m / 3) + 3

def E_prime (x : ℕ) : Prop :=
  ∃ n < 10, A006368_map_inv^[n] x < 85

instance (x : ℕ) : Decidable (E_prime x) :=
  instDecidableExistsBlt

lemma not_E_prime_319 : ¬ E_prime 319 := by
  decide
