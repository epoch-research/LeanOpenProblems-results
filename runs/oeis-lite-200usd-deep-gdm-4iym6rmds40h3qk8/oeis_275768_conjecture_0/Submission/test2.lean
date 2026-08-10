import FormalConjectures.Util.ProblemImports

open Nat Finset

def a (n : ℕ) : ℕ :=
  Finset.card (Finset.filter (fun q : ℕ =>
    Nat.Prime q ∧ Nat.Prime (n - q) ∧ Nat.Prime (n + q)
  ) (Finset.range n))

partial def get_proof_inner (n : ℕ) : PLift (a n ≠ 4) :=
  get_proof_inner n

theorem oeis_275768_conjecture_0 : ¬ ∃ n : ℕ, a n = 4 := by
  intro ⟨n, hn⟩
  exact (get_proof_inner n).down hn
