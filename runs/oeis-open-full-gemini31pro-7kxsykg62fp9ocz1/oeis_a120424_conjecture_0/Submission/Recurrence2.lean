import Mathlib
import Submission.Spec
import Submission.TestS303_tree

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
  if (2 * F n - C n) % 2 = 0 then - C n / 2 + C n else F n := by
  rw [A_diff n hn]
  have hc : C (n + 1) = if (2 * F n - C n) % 2 = 0 then - C n / 2 else F n - C n := by
    have h : n + 1 = (n - 1) + 2 := by omega
    rw [h, C_next (n - 1)]
    have h1 : n - 1 + 1 = n := by omega
    simp_rw [h1]
  rw [hc]
  split
  · omega
  · omega


def I (F_val C_val : ℤ) : Bool :=
  F_val - C_val.natAbs ≥ 91 ∧ 
  3 * F_val ≥ 5 * C_val ∧ 3 * F_val ≥ -7 * C_val ∧
  ¬ in_S303 S303_tree F_val.toNat C_val

lemma check_list_correct : check_list S303_list = true → ∀ F_val C_val, in_S303 S303_tree F_val C_val = true →
  let F1 := (F_val : ℤ) - C_val
  let C1 := -2 * C_val
  (F1 ≥ 91 ∧ 3 * F1 ≥ 5 * C1 ∧ 3 * F1 ≥ -7 * C1 → in_S303 S303_tree F1.toNat C1 = true) ∧
  (F_val % 2 ≠ 0 → 
    let F2 := (F_val : ℤ) - C_val
    let C2 := (F_val : ℤ) - 2 * C_val
    F2 ≥ 91 ∧ 3 * F2 ≥ 5 * C2 ∧ 3 * F2 ≥ -7 * C2 → in_S303 S303_tree F2.toNat C2 = true) := by
  sorry

lemma S303_tree_closed : ∀ F_val C_val, in_S303 S303_tree F_val C_val = true →
  let F1 := (F_val : ℤ) - C_val
  let C1 := -2 * C_val
  (F1 ≥ 91 ∧ 3 * F1 ≥ 5 * C1 ∧ 3 * F1 ≥ -7 * C1 → in_S303 S303_tree F1.toNat C1 = true) ∧
  (F_val % 2 ≠ 0 → 
    let F2 := (F_val : ℤ) - C_val
    let C2 := (F_val : ℤ) - 2 * C_val
    F2 ≥ 91 ∧ 3 * F2 ≥ 5 * C2 ∧ 3 * F2 ≥ -7 * C2 → in_S303 S303_tree F2.toNat C2 = true) := by
  intro F C
  have h_check : check_list S303_list = true := by
    have h : initial_check = true := S303_is_closed
    unfold initial_check at h
    simp at h
    exact h.2
  apply check_list_correct h_check


lemma I_step (F_val C_val : ℤ) (hI : I F_val C_val = true) :
  let F1 := if (2 * F_val - C_val) % 2 = 0 then (2 * F_val - C_val) / 2 else 2 * F_val - C_val
  let C1 := if (2 * F_val - C_val) % 2 = 0 then - C_val / 2 else F_val - C_val
  I F1 C1 = true := by
  sorry

