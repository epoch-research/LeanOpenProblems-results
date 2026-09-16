import Mathlib
import Submission.SpecPell

def M_seq : ℕ → ℕ
| 0 => 0
| (j + 1) => M_seq j + (P (2*j+1)).toNat

lemma M_seq_bound (j : ℕ) : M_seq j ≤ (P (2*j+1)).toNat := by
  induction j with
  | zero => exact Nat.zero_le _
  | succ j ih =>
    have h_step : M_seq (j + 1) = M_seq j + (P (2*j+1)).toNat := rfl
    rw [h_step]
    have H_P_pos_1 : 0 ≤ P (2*j+1) := (PQ_pos (2*j+1)).1
    have H_P_pos_2 : 0 ≤ P (2*j+2) := (PQ_pos (2*j+2)).1
    have H_P_pos_3 : 0 ≤ P (2*j+3) := (PQ_pos (2*j+3)).1
    have H1 : P (2*j+2) = Q (2*j+1) + P (2*j+1) := by
      have : 2*j+1+1 = 2*j+2 := by omega
      have h := (PQ_step (2*j+1)).1
      rw [this] at h
      exact h
    have H2 : P (2*j+3) = Q (2*j+2) + P (2*j+2) := by
      have : 2*j+2+1 = 2*j+3 := by omega
      have h := (PQ_step (2*j+2)).1
      rw [this] at h
      exact h
    have H_Q_pos : 0 ≤ Q (2*j+1) := by linarith [(PQ_pos (2*j+1)).2]
    have H_Q2_pos : 0 ≤ Q (2*j+2) := by linarith [(PQ_pos (2*j+2)).2]
    
    have H_ineq : 2 * P (2*j+1) ≤ P (2*j+3) := by
      calc 2 * P (2*j+1) ≤ 2 * P (2*j+1) + Q (2*j+1) := by linarith
        _ = P (2*j+2) + P (2*j+1) := by linarith
        _ ≤ P (2*j+2) + Q (2*j+2) := by 
          have : P (2*j+1) ≤ Q (2*j+2) := by
            have hQ := (PQ_step (2*j+1)).2
            have h_idx : 2*j+1+1 = 2*j+2 := by omega
            rw [h_idx] at hQ
            linarith
          linarith
        _ = P (2*j+3) := by linarith
    
    have H_ineq_nat : 2 * (P (2*j+1)).toNat ≤ (P (2*j+3)).toNat := by
      zify
      rw [Int.toNat_of_nonneg H_P_pos_1, Int.toNat_of_nonneg H_P_pos_3]
      exact H_ineq
      
    have H_idx : 2 * (j + 1) + 1 = 2 * j + 3 := by omega
    rw [H_idx]
    omega
