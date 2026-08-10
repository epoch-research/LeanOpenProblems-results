import FormalConjectures.Util.ProblemImports

open Finset Nat
open scoped BigOperators

lemma choose_succ_right_rat (n k : ℕ) (hk : k < n) :
    (n.choose (k + 1) : ℚ) = (n.choose k : ℚ) * (n - k : ℚ) / (k + 1 : ℚ) := by
  have h := congrArg (fun x : ℕ => (x : ℚ)) (Nat.choose_succ_right_eq n k)
  norm_num [Nat.cast_sub hk.le] at h
  have hk1 : (↑k + 1 : ℚ) ≠ 0 := by positivity
  field_simp [hk1]
  exact h

lemma choose_add_succ_rat (n k : ℕ) :
    ((n + k + 1).choose (k + 1) : ℚ) =
      ((n + k).choose k : ℚ) * (n + k + 1 : ℚ) / (k + 1 : ℚ) := by
  have h := congrArg (fun x : ℕ => (x : ℚ)) (Nat.add_one_mul_choose_eq (n + k) k)
  norm_num at h
  have hk1 : (↑k + 1 : ℚ) ≠ 0 := by positivity
  field_simp [hk1]
  rw [← h]
  ring

lemma central_choose_succ_rat (k : ℕ) :
    (((2 * (k + 1)).choose (k + 1) : ℕ) : ℚ) =
      (((2 * k).choose k : ℕ) : ℚ) * (2 * (2 * k + 1) : ℚ) / (k + 1 : ℚ) := by
  have h1 := congrArg (fun x : ℕ => (x : ℚ)) (Nat.choose_mul_succ_eq (2 * k) k)
  have h2 := congrArg (fun x : ℕ => (x : ℚ)) (Nat.add_one_mul_choose_eq (2 * k + 1) k)
  norm_num at h1 h2
  have hsub : 2 * k + 1 - k = k + 1 := by omega
  rw [hsub] at h1
  have hsuc : 2 * k + 1 + 1 = 2 * k + 2 := by omega
  rw [hsuc] at h2
  norm_num at h1 h2

  have hk1 : (↑k + 1 : ℚ) ≠ 0 := by positivity
  have hk2 : (↑k + 2 : ℚ) ≠ 0 := by positivity
  have h1' : (((2 * k + 1).choose k : ℕ) : ℚ) = (((2 * k).choose k : ℕ) : ℚ) * (2 * k + 1 : ℚ) / (k + 1 : ℚ) := by
    field_simp [hk1]
    exact h1.symm

  have h2norm : (2 * (↑k : ℚ) + 2) * (((2 * k + 1).choose k : ℕ) : ℚ) =
      (((2 * k + 2).choose (k + 1) : ℕ) : ℚ) * (↑k + 1) := by
    nlinarith [h2]
  have h2' : (((2 * k + 2).choose (k + 1) : ℕ) : ℚ) = (((2 * k + 1).choose k : ℕ) : ℚ) * (2 * k + 2 : ℚ) / (k + 1 : ℚ) := by
    field_simp [hk1]
    nlinarith [h2norm]
  rw [show 2 * (k + 1) = 2 * k + 2 by ring]
  rw [h2', h1']
  field_simp [hk1]
