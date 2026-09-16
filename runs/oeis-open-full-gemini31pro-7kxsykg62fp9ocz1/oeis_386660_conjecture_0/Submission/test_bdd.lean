import Mathlib
open Nat Filter Topology

def M (n : ℕ) : ℕ := (Finset.range (n + 1)).sup (fun k => min (n.choose k) (2 ^ k))
lemma M_ge_one (n : ℕ) : 1 ≤ M n := by
  have : 0 ∈ Finset.range (n + 1) := Finset.mem_range.mpr (succ_pos n)
  have H := @Finset.le_sup _ ℕ _ _ (Finset.range (n + 1)) (fun k => min (n.choose k) (2 ^ k)) 0 this
  simp only [choose_zero_right, pow_zero, min_self] at H
  exact H
lemma M_pos (n : ℕ) : 0 < (M n : ℝ) := Nat.cast_pos.mpr (M_ge_one n)
lemma M_le_two_pow (n : ℕ) : M n ≤ 2 ^ n := by
  apply Finset.sup_le
  intro k hk
  have h_min : min (n.choose k) (2 ^ k) ≤ 2 ^ k := min_le_right _ _
  have h_pow : 2 ^ k ≤ 2 ^ n := by
    apply Nat.pow_le_pow_right (by decide)
    exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  exact le_trans h_min h_pow

noncomputable def u (n : ℕ) : ℝ := - Real.log (M n)

lemma u_div_bdd : BddBelow (Set.range fun n => u n / n) := by
  use - Real.log 2
  rintro _ ⟨n, rfl⟩
  dsimp [u]
  by_cases hn : n = 0
  · simp only [hn, Nat.cast_zero, div_zero]
    have : 0 ≤ Real.log 2 := by positivity
    linarith
  have p1 := M_pos n
  have p2 : (M n : ℝ) ≤ (2 : ℝ) ^ n := by
    calc (M n : ℝ) ≤ ((2 ^ n : ℕ) : ℝ) := by exact_mod_cast M_le_two_pow n
         _ = (2 : ℝ) ^ n := by norm_cast
  have p3 : Real.log (M n) ≤ Real.log ((2 : ℝ) ^ n) := Real.log_le_log p1 p2
  have p4 : Real.log (M n) ≤ n * Real.log 2 := by
    calc Real.log (M n) ≤ Real.log ((2 : ℝ) ^ n) := p3
         _ = n * Real.log 2 := by simp [Real.log_pow]
  have p5 : - Real.log (M n) ≥ - (n * Real.log 2) := neg_le_neg p4
  have p6 : (- Real.log (M n)) / n ≥ - Real.log 2 := by
    calc (- Real.log (M n)) / n ≥ (- (n * Real.log 2)) / n := div_le_div_of_nonneg_right p5 (Nat.cast_nonneg n)
         _ = - Real.log 2 := by
           rw [neg_div, mul_comm, mul_div_cancel_right₀ _ (Nat.cast_ne_zero.mpr hn)]
  exact p6
