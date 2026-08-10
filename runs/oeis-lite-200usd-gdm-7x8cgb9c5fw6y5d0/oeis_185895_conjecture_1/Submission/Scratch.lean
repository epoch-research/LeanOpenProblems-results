import FormalConjectures.Util.ProblemImports
import Submission.Spec

open Polynomial Nat Finset Classical

lemma H_def_le_factorial_three_pow (m K : ℕ) (hm : m ≥ 1) :
  (H_def m K).natAbs * 3^K + m.factorial * 3^m ≤ m.factorial * 3^m * 3^K := by
  induction m using Nat.strong_induction_on generalizing K with
  | h m ih =>
    induction K with
    | zero =>
      simp [H_def]
    | succ K ih_K =>
      by_cases h_choose : m < K + 1
      · -- choose m (K + 1) = 0
        have h_c : Nat.choose m (K + 1) = 0 := Nat.choose_eq_zero_of_lt h_choose
        have h_rec : H_def m (K + 1) = H_def m K := by
          rcases m with _|m
          · simp [H_def]
          · rw [H_def]
            have h_zero : ((Nat.choose (m + 1) (K + 1)) : ℤ) = 0 := by exact_mod_cast h_c
            rw [h_zero, zero_mul, sub_zero]
        rw [h_rec]
        have h_alg : (H_def m K).natAbs * 3^(K + 1) + m.factorial * 3^m ≤ 3 * ((H_def m K).natAbs * 3^K + m.factorial * 3^m) := by
          calc
            (H_def m K).natAbs * 3^(K + 1) + m.factorial * 3^m
              _ = 3 * ((H_def m K).natAbs * 3^K) + m.factorial * 3^m := by ring
            _ ≤ 3 * ((H_def m K).natAbs * 3^K) + 3 * (m.factorial * 3^m) := by omega
            _ = 3 * ((H_def m K).natAbs * 3^K + m.factorial * 3^m) := by ring
        have h_ih_K_3 : 3 * ((H_def m K).natAbs * 3^K + m.factorial * 3^m) ≤ 3 * (m.factorial * 3^m * 3^K) := by
          gcongr
        have h_alg2 : 3 * (m.factorial * 3^m * 3^K) = m.factorial * 3^m * 3^(K + 1) := by ring
        rw [h_alg2] at h_ih_K_3
        exact h_alg.trans h_ih_K_3
      · -- choose m (K + 1) != 0, so m >= K + 1
        have hm_geK : m ≥ K + 1 := by omega
        obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
        -- Now m = m' + 1
        have h_rec : H_def (m' + 1) (K + 1) = H_def (m' + 1) K - (Nat.choose (m' + 1) (K + 1)) * H_def (m' + 1 - (K + 1)) K := rfl
        let y := m' + 1 - (K + 1)
        have h_rec_y : H_def (m' + 1) (K + 1) = H_def (m' + 1) K - (Nat.choose (m' + 1) (K + 1)) * H_def y K := h_rec
        have h_abs_le : (H_def (m' + 1) (K + 1)).natAbs ≤ (H_def (m' + 1) K).natAbs + Nat.choose (m' + 1) (K + 1) * (H_def y K).natAbs := by
          rw [h_rec_y]
          have h_sub_le := Int.natAbs_sub_le (H_def (m' + 1) K) (Nat.choose (m' + 1) (K + 1) * H_def y K)
          have h_mul_abs : (Nat.choose (m' + 1) (K + 1) * H_def y K).natAbs = Nat.choose (m' + 1) (K + 1) * (H_def y K).natAbs := by
            rw [Int.natAbs_mul]
            congr
          omega
        have h_bound_term : 3 * Nat.choose (m' + 1) (K + 1) * ((H_def y K).natAbs * 3^K) ≤ (m' + 1).factorial * 3^(m' + 1) := by
          by_cases hy : y = 0
          · subst hy
            have h_eq_y0 : m' + 1 = K + 1 := by omega
            have h_c_eq : Nat.choose (m' + 1) (K + 1) = 1 := by
              rw [h_eq_y0, Nat.choose_self]
            simp [h_c_eq, H_def]
            have h_pow_le : 3^(K + 1) ≤ (K + 1).factorial * 3^(K + 1) := by
              have h_fac_ge : (K + 1).factorial ≥ 1 := Nat.factorial_pos (K + 1)
              gcongr
            exact h_pow_le
          · have hy_ge1 : y ≥ 1 := by omega
            have hy_lt : y < m' + 1 := by omega
            have h_ih_y := ih y hy_lt K hy_ge1
            have h_y_bound : (H_def y K).natAbs * 3^K ≤ y.factorial * 3^y * 3^K := by
              omega
            have h_lhs_le : 3 * Nat.choose (m' + 1) (K + 1) * ((H_def y K).natAbs * 3^K) ≤ 3 * Nat.choose (m' + 1) (K + 1) * (y.factorial * 3^y * 3^K) := by
              gcongr
            have h_y_K_eq : y + K = m' := by omega
            have h_pow_eq : 3^y * 3^K = 3^m' := by
              rw [← Nat.pow_add, h_y_K_eq]
            have h_alg_lhs : 3 * Nat.choose (m' + 1) (K + 1) * (y.factorial * 3^y * 3^K) = Nat.choose (m' + 1) (K + 1) * y.factorial * 3^(m' + 1) := by
              rw [h_pow_eq]
              ring
            rw [h_alg_lhs] at h_lhs_le
            have h_choose_le := choose_mul_factorial_le (m' + 1) (K + 1)
            -- Note y = m' + 1 - (K + 1)
            have h_final_le : Nat.choose (m' + 1) (K + 1) * y.factorial * 3^(m' + 1) ≤ (m' + 1).factorial * 3^(m' + 1) := by
              gcongr
            exact h_lhs_le.trans h_final_le
        have h_abs_le_mul3 : (H_def (m' + 1) (K + 1)).natAbs * 3^(K + 1) ≤ 3 * (H_def (m' + 1) K).natAbs * 3^K + 3 * Nat.choose (m' + 1) (K + 1) * ((H_def y K).natAbs * 3^K) := by
          calc
            (H_def (m' + 1) (K + 1)).natAbs * 3^(K + 1)
              _ ≤ ((H_def (m' + 1) K).natAbs + Nat.choose (m' + 1) (K + 1) * (H_def y K).natAbs) * 3^(K + 1) := by gcongr
            _ = 3 * (H_def (m' + 1) K).natAbs * 3^K + 3 * Nat.choose (m' + 1) (K + 1) * ((H_def y K).natAbs * 3^K) := by ring
        have h_combined : (H_def (m' + 1) (K + 1)).natAbs * 3^(K + 1) + (m' + 1).factorial * 3^(m' + 1) + (m' + 1).factorial * 3^(m' + 1) ≤
          3 * ((H_def (m' + 1) K).natAbs * 3^K + (m' + 1).factorial * 3^(m' + 1)) + 3 * Nat.choose (m' + 1) (K + 1) * ((H_def y K).natAbs * 3^K) := by
          calc
            (H_def (m' + 1) (K + 1)).natAbs * 3^(K + 1) + (m' + 1).factorial * 3^(m' + 1) + (m' + 1).factorial * 3^(m' + 1)
              _ ≤ 3 * (H_def (m' + 1) K).natAbs * 3^K + 3 * Nat.choose (m' + 1) (K + 1) * ((H_def y K).natAbs * 3^K) + (m' + 1).factorial * 3^(m' + 1) + (m' + 1).factorial * 3^(m' + 1) := by gcongr
            _ = 3 * (H_def (m' + 1) K).natAbs * 3^K + 2 * ((m' + 1).factorial * 3^(m' + 1)) + 3 * Nat.choose (m' + 1) (K + 1) * ((H_def y K).natAbs * 3^K) := by ring
            _ ≤ 3 * (H_def (m' + 1) K).natAbs * 3^K + 3 * ((m' + 1).factorial * 3^(m' + 1)) + 3 * Nat.choose (m' + 1) (K + 1) * ((H_def y K).natAbs * 3^K) := by omega
            _ = 3 * ((H_def (m' + 1) K).natAbs * 3^K + (m' + 1).factorial * 3^(m' + 1)) + 3 * Nat.choose (m' + 1) (K + 1) * ((H_def y K).natAbs * 3^K) := by ring
        have h_ih_K_3 : 3 * ((H_def (m' + 1) K).natAbs * 3^K + (m' + 1).factorial * 3^(m' + 1)) ≤ 3 * ((m' + 1).factorial * 3^(m' + 1) * 3^K) := by
          gcongr
        have h_alg_K_3 : 3 * ((m' + 1).factorial * 3^(m' + 1) * 3^K) = (m' + 1).factorial * 3^(m' + 1) * 3^(K + 1) := by ring
        rw [h_alg_K_3] at h_ih_K_3
        have h_rhs_le : 3 * ((H_def (m' + 1) K).natAbs * 3^K + (m' + 1).factorial * 3^(m' + 1)) + 3 * Nat.choose (m' + 1) (K + 1) * ((H_def y K).natAbs * 3^K) ≤
          (m' + 1).factorial * 3^(m' + 1) * 3^(K + 1) + (m' + 1).factorial * 3^(m' + 1) := by
          gcongr
        omega


