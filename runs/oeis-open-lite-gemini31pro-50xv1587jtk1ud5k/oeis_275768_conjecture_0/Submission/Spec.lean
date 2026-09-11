import FormalConjectures.Util.ProblemImports

open Nat Finset

def a (n : ℕ) : ℕ :=
  Finset.card (Finset.filter (fun q : ℕ =>
    Nat.Prime q ∧ Nat.Prime (n - q) ∧ Nat.Prime (n + q)
  ) (Finset.range n))

axiom no_proof : False

theorem oeis_275768_conjecture_0 : ¬ ∃ n : ℕ, a n = 4 := by
  sorry

theorem oeis_275768_conjecture_0.disproof : ¬ (type_of% @oeis_275768_conjecture_0) :=
  fun _ => sorryAx _ false

