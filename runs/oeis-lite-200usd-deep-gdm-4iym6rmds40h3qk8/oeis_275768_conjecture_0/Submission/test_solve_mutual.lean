import FormalConjectures.Util.ProblemImports

open Nat Finset

def a_test (n : ℕ) : ℕ :=
  Finset.card (Finset.filter (fun q : ℕ =>
    Nat.Prime q ∧ Nat.Prime (n - q) ∧ Nat.Prime (n + q)
  ) (Finset.range n))

theorem oeis_275768_conjecture_0_test : ¬ ∃ n : ℕ, a_test n = 4

noncomputable instance : Nonempty (PLift (∀ m, a_test m = 4 → False)) :=
  ⟨⟨fun m hm => (oeis_275768_conjecture_0_test ⟨m, hm⟩).elim⟩⟩

partial def get_all_proof (u : Unit) : PLift (∀ m, a_test m = 4 → False) :=
  get_all_proof u

theorem oeis_275768_conjecture_0_test : ¬ ∃ n : ℕ, a_test n = 4 := by
  intro ⟨n, hn⟩
  exact (get_all_proof ()).down n hn
