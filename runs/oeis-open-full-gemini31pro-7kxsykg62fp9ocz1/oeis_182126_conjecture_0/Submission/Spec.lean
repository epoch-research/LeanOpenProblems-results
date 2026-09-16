import FormalConjectures.Util.ProblemImports

open Nat
open Finset

noncomputable def a (n : ℕ) : ℕ :=
  let p_n := fun k : ℕ => (Nat.nth Nat.Prime (k - 1))
  if n = 0 then 0
  else (p_n n * p_n (n + 1)) % p_n (n + 2)

noncomputable def count_a (x v : ℕ) : ℕ :=
  ((range (x + 1)).filter fun n => 1 ≤ n ∧ a n = v).card

def is_most_frequent (x v₀ : ℕ) : Prop :=
  ∀ v : ℕ, count_a x v₀ ≥ count_a x v

theorem oeis_182126_conjecture_0 :
  ∀ x : ℕ,
    x > 10^9 →
    ∀ v₀ : ℕ,
      is_most_frequent x v₀ →
      120 ∣ v₀ := by sorry

theorem oeis_182126_conjecture_0.disproof : ¬ (type_of% @oeis_182126_conjecture_0) := by sorry
