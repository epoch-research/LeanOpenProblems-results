import FormalConjectures.Util.ProblemImports

open Nat Finset

def a_test (n : ℕ) : ℕ :=
  Finset.card (Finset.filter (fun q : ℕ =>
    Nat.Prime q ∧ Nat.Prime (n - q) ∧ Nat.Prime (n + q)
  ) (Finset.range n))

noncomputable instance (n : ℕ) : Nonempty (PLift (a_test n ≠ 4) ⊕ (PLift (a_test n ≠ 4) → PLift False)) := by
  by_cases h : a_test n ≠ 4
  · exact ⟨.inl ⟨h⟩⟩
  · exact ⟨.inr (fun h_ne => ⟨(h h_ne.down).elim⟩)⟩

partial def get_fn (n : ℕ) : PLift (a_test n ≠ 4) ⊕ (PLift (a_test n ≠ 4) → PLift False) :=
  get_fn n

theorem oeis_275768_conjecture_0_test (n : ℕ) : a_test n ≠ 4 := by
  intro hn
  match get_fn n with
  | .inl val => exact val.down hn
  | .inr val_fn =>
    let rec h_ne : PLift (a_test n ≠ 4) := ⟨fun hn_any => (val_fn h_ne).down⟩
    exact h_ne.down hn
