import Mathlib

open Nat Filter Topology

def M (n : ℕ) : ℕ := (Finset.range (n + 1)).sup (fun k => min (n.choose k) (2 ^ k))

lemma M_ge_one (n : ℕ) : 1 ≤ M n := by
  have : 0 ∈ Finset.range (n + 1) := Finset.mem_range.mpr (succ_pos n)
  have H := @Finset.le_sup _ ℕ _ _ (Finset.range (n + 1)) (fun k => min (n.choose k) (2 ^ k)) 0 this
  simp only [choose_zero_right, pow_zero, min_self] at H
  exact H

lemma M_pos (n : ℕ) : 0 < (M n : ℝ) := Nat.cast_pos.mpr (M_ge_one n)

lemma M_super (n m : ℕ) : M n * M m ≤ M (n + m) := sorry

noncomputable def u (n : ℕ) : ℝ := - Real.log (M n)

lemma u_subadditive : Subadditive u := by
  intro n m
  dsimp [u]
  have p1 := M_pos n
  have p2 := M_pos m
  rw [← neg_add, neg_le_neg_iff, ← Real.log_mul p1.ne' p2.ne']
  apply Real.log_le_log (mul_pos p1 p2)
  norm_cast
  exact M_super n m
