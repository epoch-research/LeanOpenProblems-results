import Mathlib
import Submission.Spec

def f_nat (x : ℕ) : ℕ := if x % 2 = 0 then x / 2 else x

lemma f_nat_Z (x : ℕ) : (f_nat x : ℤ) = if (x : ℤ) % 2 = 0 then (x : ℤ) / 2 else (x : ℤ) := by
  unfold f_nat; split
  · have h : (x : ℤ) % 2 = 0 := by omega
    simp [h]
  · have h : (x : ℤ) % 2 ≠ 0 := by omega
    simp [h]

def F (n : ℕ) : ℤ := (f_nat (A120424 n) : ℤ)
def C (n : ℕ) : ℤ := F n - F (n - 1)

lemma A_step_nat (n : ℕ) : A120424 (n + 2) = f_nat (A120424 (n + 1)) + f_nat (A120424 n) := by rfl

lemma A_step_Z (n : ℕ) : (A120424 (n + 2) : ℤ) = F (n + 1) + F n := by rfl

lemma F_rel (n : ℕ) : F (n + 2) = if (F (n + 1) + F n) % 2 = 0 then (F (n + 1) + F n) / 2 else (F (n + 1) + F n) := by
  unfold F; rw [A_step_nat, f_nat_Z]; push_cast; rfl

lemma F_next (n : ℕ) : F (n + 2) = if (2 * F (n + 1) - C (n + 1)) % 2 = 0 then (2 * F (n + 1) - C (n + 1)) / 2 else 2 * F (n + 1) - C (n + 1) := by
  rw [F_rel n]
  have h_idx : n + 1 - 1 = n := by omega
  have h : F (n + 1) + F n = 2 * F (n + 1) - C (n + 1) := by
    have hc : C (n + 1) = F (n + 1) - F n := by unfold C; rw [h_idx]
    omega
  rw [h]

lemma C_next (n : ℕ) : C (n + 2) = if (2 * F (n + 1) - C (n + 1)) % 2 = 0 then - C (n + 1) / 2 else F (n + 1) - C (n + 1) := by
  have h_idx : n + 2 - 1 = n + 1 := by omega
  have hc : C (n + 2) = F (n + 2) - F (n + 1) := by unfold C; rw [h_idx]
  rw [hc, F_next n]
  split
  · omega
  · omega

lemma A_diff (n : ℕ) (hn : n ≥ 1) : (A120424 (n + 2) : ℤ) - (A120424 (n + 1) : ℤ) = C (n + 1) + C n := by
  have h_idx : n + 1 - 1 = n := by omega
  have h_idx2 : n - 1 + 1 = n := by omega
  have hc1 : C (n + 1) = F (n + 1) - F n := by unfold C; rw [h_idx]
  have hc0 : C n = F n - F (n - 1) := by unfold C; rfl
  rw [A_step_Z n]
  have hA1 : (A120424 (n + 1) : ℤ) = F n + F (n - 1) := by
    have h : n + 1 = (n - 1) + 2 := by omega
    rw [h, A_step_Z (n - 1)]
    have h2 : n - 1 + 1 = n := by omega
    rw [h2]
  rw [hA1]
  omega

lemma A_diff_val (n : ℕ) (hn : n ≥ 1) : 
  (A120424 (n + 2) : ℤ) - (A120424 (n + 1) : ℤ) = 
  if (2 * F n - C n) % 2 = 0 then - C (n + 1) else F n := by
  rw [A_diff n hn]
  have hc : C (n + 1) = if (2 * F n - C n) % 2 = 0 then - C n / 2 else F n - C n := by
    -- wait, C (n+1) is C_next (n-1)
    have h : n + 1 = (n - 1) + 2 := by omega
    rw [h, C_next (n - 1)]
    have h1 : n - 1 + 1 = n := by omega
    simp_rw [h1]
  rw [hc]
  split
  · omega
  · omega
