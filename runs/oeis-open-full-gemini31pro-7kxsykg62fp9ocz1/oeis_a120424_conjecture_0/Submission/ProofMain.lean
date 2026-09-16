import Mathlib
import Submission.Spec
import Submission.Recurrence2

lemma natAbs_eq (x : ℤ) : (x.natAbs : ℤ) = if x ≥ 0 then x else -x := by
  cases x <;> simp

lemma natAbs_le_1_iff (x : ℤ) : x.natAbs ≤ 1 ↔ -1 ≤ x ∧ x ≤ 1 := by omega

theorem A_diff_val_check (n : ℕ) (hn : n ≥ 1) : 
  (A120424 (n + 2) : ℤ) - (A120424 (n + 1) : ℤ) = 
  if (2 * F n - C n) % 2 = 0 then C n / 2 else F n := by
  have : (A120424 (n + 2) : ℤ) - (A120424 (n + 1) : ℤ) = C (n + 1) + C n := A_diff n hn
  rw [this]
  have hc : C (n + 1) = if (2 * F n - C n) % 2 = 0 then - C n / 2 else F n - C n := by
    have h : n + 1 = (n - 1) + 2 := by omega
    rw [h, C_next (n - 1)]
    have h1 : n - 1 + 1 = n := by omega
    simp_rw [h1]
  rw [hc]
  split
  · rename_i h_even
    have hC_even : C n % 2 = 0 := by omega
    omega
  · rename_i h_odd
    omega

lemma C_bound (C : ℤ) (h5 : (C / 2).natAbs ≤ 1) (hC_even : C % 2 = 0) :
  C ∈ ([-2, 0, 2] : List ℤ) := by
  rw [natAbs_le_1_iff] at h5
  have : C = -2 ∨ C = 0 ∨ C = 2 := by omega
  rcases this with rfl | rfl | rfl <;> simp

lemma V_nondec (F C : ℤ) (hpos : 3 * F ≥ 5 * C) (hneg : 3 * F ≥ -7 * C) :
  let F1 := if (2 * F - C) % 2 = 0 then (2 * F - C) / 2 else 2 * F - C
  let C1 := if (2 * F - C) % 2 = 0 then - C / 2 else F - C
  F1 - C1.natAbs ≥ F - C.natAbs := by
  intro F1 C1
  rw [natAbs_eq C, natAbs_eq C1]
  have h_cases : (2 * F - C) % 2 = 0 ∨ (2 * F - C) % 2 ≠ 0 := by omega
  rcases h_cases with h_even | h_odd
  · have hC_even : C % 2 = 0 := by omega
    have hF1 : F1 = F - C / 2 := by omega
    have hC1 : C1 = - C / 2 := by omega
    rw [hF1, hC1]; omega
  · have hF1 : F1 = 2 * F - C := by omega
    have hC1 : C1 = F - C := by omega
    rw [hF1, hC1]; omega

lemma F_bounds_step (n : ℕ) : 3 * F n ≥ 5 * C n ∧ 3 * F n ≥ -7 * C n := by sorry

lemma V_seq_nondec (n : ℕ) (hn : n ≥ 1) : F (n + 1) - (C (n + 1)).natAbs ≥ F n - (C n).natAbs := by
  have ⟨hpos, hneg⟩ := F_bounds_step n
  have := V_nondec (F n) (C n) hpos hneg
  have hn1 : n - 1 + 2 = n + 1 := by omega
  have F_r := F_next (n - 1)
  have C_r := C_next (n - 1)
  rw [hn1] at F_r C_r
  have h1 : n - 1 + 1 = n := by omega
  rw [h1] at F_r C_r
  change (if (2 * F n - C n) % 2 = 0 then (2 * F n - C n) / 2 else 2 * F n - C n) -
    (if (2 * F n - C n) % 2 = 0 then -C n / 2 else F n - C n).natAbs ≥
    F n - ↑(C n).natAbs at this
  rw [← F_r, ← C_r] at this
  exact this

lemma V_seq_nondec_k (n k : ℕ) (hn : n ≥ 1) : F (n + k) - (C (n + k)).natAbs ≥ F n - (C n).natAbs := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h1 := V_seq_nondec (n + k) (by omega)
    have h2 : n + (k + 1) = n + k + 1 := by omega
    rw [h2]
    omega

lemma V_18 : F 18 - (C 18).natAbs = 114 := by sorry

lemma V_ge_114 (n : ℕ) (hn : n ≥ 18) : F n - (C n).natAbs ≥ 114 := by
  have h : n = 18 + (n - 18) := by omega
  have := V_seq_nondec_k 18 (n - 18) (by omega)
  rw [V_18] at this
  have h2 : 18 + (n - 18) = n := by omega
  rw [h2] at this
  exact this

