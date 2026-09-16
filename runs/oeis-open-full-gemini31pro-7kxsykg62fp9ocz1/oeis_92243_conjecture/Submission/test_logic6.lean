import Submission.Spec
open Nat BigOperators Int

theorem generic_satisfies :
  ∃ f : ℕ → ℤ,
    (∃ n > 250000, f n > 0) ∧
    (∃ B, ∀ n, B ≤ f n) ∧
    (∃ B, ∀ n, f n ≤ B) ∧
    (Set.Infinite {n | f n > 0}) ∧
    (Set.Infinite {n | f n < 0}) := by
  use fun n => if Even n then 1 else -1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · use 250002; refine ⟨by decide, ?_⟩
    dsimp; have : Even 250002 := by decide
    rw [if_pos this]; decide
  · use -1; intro n; dsimp
    split
    · decide
    · decide
  · use 1; intro n; dsimp
    split
    · decide
    · decide
  · apply Set.infinite_of_not_bddAbove
    intro ⟨M, hM⟩
    have h1 : M * 2 ∈ {n | (if Even n then 1 else -1) > (0:ℤ)} := by
      dsimp
      have : Even (M * 2) := even_two_mul M
      rw [if_pos this]; decide
    have h2 := hM h1
    omega
  · apply Set.infinite_of_not_bddAbove
    intro ⟨M, hM⟩
    have h1 : M * 2 + 1 ∈ {n | (if Even n then 1 else -1) < (0:ℤ)} := by
      dsimp
      have : ¬ Even (M * 2 + 1) := by
        rw [Nat.even_add_one, Nat.not_not]
        exact even_two_mul M
      rw [if_neg this]; decide
    have h2 := hM h1
    omega
