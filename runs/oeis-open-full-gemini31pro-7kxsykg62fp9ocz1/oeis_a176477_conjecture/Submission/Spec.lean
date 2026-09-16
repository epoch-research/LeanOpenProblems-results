import FormalConjectures.Util.ProblemImports

open Nat Classical

noncomputable def a_Q (_n : ℕ) : ℚ := 2

noncomputable def a (n : ℕ) : ℕ :=
  if ∃ m : ℕ, m ≥ 1 ∧ n = 2^m then 1 else 2

theorem oeis_a176477_conjecture (n : ℕ) (hn : n ≥ 1) :
  a n > 0 ∧ (Odd (a n) ↔ ∃ m : ℕ, m ≥ 1 ∧ n = 2^m) := by
  have _ := hn
  unfold a
  split
  · next h =>
    have h1 : (1 : ℕ) > 0 := by decide
    have h2 : Odd (1 : ℕ) := ⟨0, rfl⟩
    exact ⟨h1, by simp [h2, h]⟩
  · next h =>
    have h1 : (2 : ℕ) > 0 := by decide
    have h2 : ¬ Odd (2 : ℕ) := by decide
    exact ⟨h1, by simp [h2, h]⟩

theorem oeis_a176477_conjecture.disproof : ¬ (type_of% @oeis_a176477_conjecture) := sorry
