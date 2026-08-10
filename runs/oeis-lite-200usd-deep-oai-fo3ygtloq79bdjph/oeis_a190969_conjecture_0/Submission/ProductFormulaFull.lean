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

lemma alg_step (n p q A B C P : ℚ) (m : ℕ)
    (hp : p = 2*n + 1)
    (h : (-1:ℚ)^m * A * B = C^2 / 16^m * P)
    (hq1 : q + 1 ≠ 0) (ho : 2*q+1 ≠ 0) :
    (-1:ℚ)^(m+1) * (A * (n-q)/(q+1)) * (B*(n+q+1)/(q+1)) =
      (C * (2*(2*q+1))/(q+1))^2 / 16^(m+1) * (P * (1 - p^2/(2*q+1)^2)) := by
  have h16 : (16:ℚ) ≠ 0 := by norm_num
  have h16m : (16:ℚ)^m ≠ 0 := pow_ne_zero _ h16
  have hq1sq : (q + 1)^2 ≠ 0 := pow_ne_zero 2 hq1
  have hosq : (2*q + 1)^2 ≠ 0 := pow_ne_zero 2 ho
  have hmain : - ((n - q) * (n + q + 1)) = ((2*q+1)^2 - p^2) / 4 := by
    rw [hp]
    ring
  calc
    (-1:ℚ)^(m+1) * (A * (n-q)/(q+1)) * (B*(n+q+1)/(q+1))
        = - (((-1:ℚ)^m * A * B) * ((n-q)*(n+q+1)) / (q+1)^2) := by
          rw [pow_succ]
          field_simp [hq1, hq1sq]

    _ = - ((C^2 / 16^m * P) * ((n-q)*(n+q+1)) / (q+1)^2) := by rw [h]
    _ = (C^2 / 16^m * P) * (((2*q+1)^2 - p^2) / 4) / (q+1)^2 := by
          rw [← hmain]
          ring
    _ = (C * (2*(2*q+1))/(q+1))^2 / 16^(m+1) * (P * (1 - p^2/(2*q+1)^2)) := by
          field_simp [hq1, hq1sq, ho, hosq, h16, h16m]
          ring

lemma shifted_coeff_product_rat_complete (n p k : ℕ) (hp : (p : ℚ) = 2 * (n : ℚ) + 1) (hk : k ≤ n) :
    ((-1 : ℚ) ^ k) * (n.choose k : ℚ) * ((n + k).choose n : ℚ) =
      ((Nat.choose (2 * k) k : ℚ) ^ 2) / (16 : ℚ) ^ k *
        ∏ j ∈ range k, (1 - (p : ℚ) ^ 2 / ((2 * j + 1 : ℕ) : ℚ) ^ 2) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hk' : k ≤ n := Nat.le_trans (Nat.le_succ k) hk
      have hks : k < n := Nat.lt_of_succ_le hk
      have ih' := ih hk'
      rw [prod_range_succ]
      have hn_choose := choose_succ_right_rat n k hks
      have hadd_choose : (((n + (k + 1)).choose n : ℕ) : ℚ) = (((n + k).choose n : ℕ) : ℚ) * (n + k + 1 : ℚ) / (k + 1 : ℚ) := by
        have h := choose_add_succ_rat n k
        have hL : (n + (k + 1)).choose n = (n + k + 1).choose (k + 1) := by
          rw [show n + (k + 1) = n + k + 1 by omega]
          exact Nat.choose_symm_of_eq_add (show n + (k + 1) = n + k + 1 by omega)
        have hR : (n + k).choose k = (n + k).choose n := by
          exact Nat.choose_symm_of_eq_add (show n + k = k + n by omega)
        rw [hR] at h
        rw [hL]
        simpa [add_assoc, add_comm, add_left_comm] using h
      have hcent := central_choose_succ_rat k
      rw [hn_choose, hadd_choose, hcent]
      have hk1 : ((k : ℚ) + 1) ≠ 0 := by positivity
      have ho : 2 * (k : ℚ) + 1 ≠ 0 := by positivity
      simpa [Nat.cast_add, Nat.cast_mul] using
        (alg_step (n : ℚ) (p : ℚ) (k : ℚ)
          (n.choose k : ℚ) ((n + k).choose n : ℚ) ((Nat.choose (2 * k) k : ℚ))
          (∏ j ∈ range k, (1 - (p : ℚ) ^ 2 / ((2 * j + 1 : ℕ) : ℚ) ^ 2))
          k hp ih' hk1 ho)
