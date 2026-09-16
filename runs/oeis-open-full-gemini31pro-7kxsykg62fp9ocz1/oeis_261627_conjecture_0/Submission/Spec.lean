import FormalConjectures.Util.ProblemImports

open Nat Finset

noncomputable def A261627 (n : ℕ) : ℕ :=
  let n' : ℕ := if n % 2 = 1 then 1 else 2

  let candidate_primes : Finset ℕ := Finset.filter Nat.Prime (Finset.range (n + 1))

  Finset.card $ Finset.filter (fun p : ℕ =>
    Nat.Prime p ∧ 
    let k : ℕ := p * n' - 1 
    k < n ∧ 
    Nat.Prime (n - k) ∧
    Nat.Prime (n + k)
  ) candidate_primes

def A261627_singletons : Finset ℕ :=
  ([5, 7, 10, 11, 12, 19, 22, 30, 34, 44, 46, 72, 142] : List ℕ).toFinset

theorem oeis_261627_conjecture_0 (n : ℕ) :
  (n > 6 → A261627 n > 0) ∧
  (A261627 n = 1 ↔ n ∈ A261627_singletons) :=
by sorry

theorem oeis_261627_conjecture_0.disproof : ¬ (type_of% @oeis_261627_conjecture_0) := sorry
