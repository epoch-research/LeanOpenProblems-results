import FormalConjectures.Util.ProblemImports
open Nat

noncomputable def poch (a : ℚ) : ℕ → ℚ
  | 0 => 1
  | n+1 => poch a n * (a + n)
lemma poch_succ (a : ℚ) (n : ℕ) : poch a (n+1) = poch a n * (a+n) := rfl


lemma poch_ne_zero_of_pos (a : ℚ) (ha : 0 < a) (n : ℕ) : poch a n ≠ 0 := by
  induction n with
  | zero => simp [poch]
  | succ n ih =>
      rw [poch_succ]
      exact mul_ne_zero ih (ne_of_gt (by positivity : 0 < a + (n:ℚ)))

lemma catalan_cast_ne_zero (k : ℕ) : (catalan k : ℚ) ≠ 0 := by
  have h0 : (k+1) * catalan k = Nat.centralBinom k := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using succ_mul_catalan_eq_centralBinom k
  have hcpos : 0 < catalan k := by
    by_contra h
    have hz : catalan k = 0 := Nat.eq_zero_of_not_pos h
    rw [hz, mul_zero] at h0
    exact (Nat.centralBinom_ne_zero k) h0.symm
  exact_mod_cast (_root_.ne_of_gt hcpos)

lemma catalan_inv_poch (k : ℕ) :
    1 / (catalan k : ℚ) = ((4:ℚ)^k)⁻¹ * (poch 2 k / poch (1/2) k) := by
  induction k with
  | zero => simp [poch]
  | succ k ih =>
      have hcat : ((k+1:ℕ):ℚ) * ((k+2:ℕ):ℚ) * (catalan (k+1) : ℚ)
          = (2:ℚ) * ((2*k+1:ℕ):ℚ) * ((k+1:ℕ):ℚ) * (catalan k : ℚ) := by
        have h1 : ((k+2:ℕ) * catalan (k+1) : ℕ) = Nat.centralBinom (k+1) := by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using succ_mul_catalan_eq_centralBinom (k+1)
        have h2 : ((k+1:ℕ) * Nat.centralBinom (k+1) : ℕ) = 2 * (2*k+1) * Nat.centralBinom k := by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using Nat.succ_mul_centralBinom_succ k
        have h0 : ((k+1:ℕ) * catalan k : ℕ) = Nat.centralBinom k := by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using succ_mul_catalan_eq_centralBinom k
        calc
          ((k+1:ℕ):ℚ) * ((k+2:ℕ):ℚ) * (catalan (k+1) : ℚ)
              = (((k+1) * ((k+2) * catalan (k+1)) : ℕ) : ℚ) := by norm_num [Nat.cast_mul]; ring
          _ = (((k+1) * Nat.centralBinom (k+1) : ℕ) : ℚ) := by rw [h1]
          _ = ((2 * (2*k+1) * Nat.centralBinom k : ℕ) : ℚ) := by rw [h2]
          _ = ((2 * (2*k+1) * ((k+1) * catalan k) : ℕ) : ℚ) := by rw [h0]
          _ = (2:ℚ) * ((2*k+1:ℕ):ℚ) * ((k+1:ℕ):ℚ) * (catalan k : ℚ) := by norm_num [Nat.cast_mul]; ring
      have hk1 : (((k+1:ℕ):ℚ) ≠ 0) := by positivity
      have hk2 : (((k+2:ℕ):ℚ) ≠ 0) := by positivity
      have hc : (catalan k : ℚ) ≠ 0 := catalan_cast_ne_zero k
      have hden : (poch (1/2) k) ≠ 0 := poch_ne_zero_of_pos (1/2) (by norm_num) k
      have hcnext : (catalan (k+1) : ℚ) ≠ 0 := catalan_cast_ne_zero (k+1)
      have hcat2 : ((k+2:ℕ):ℚ) * (catalan (k+1) : ℚ)
          = (2:ℚ) * ((2*k+1:ℕ):ℚ) * (catalan k : ℚ) := by
        apply mul_left_cancel₀ hk1
        simpa [mul_assoc, mul_left_comm, mul_comm] using hcat
      have hratio : 1 / (catalan (k+1) : ℚ)
          = ((k+2:ℕ):ℚ) / ((2:ℚ) * ((2*k+1:ℕ):ℚ) * (catalan k : ℚ)) := by
        field_simp [hcnext, hc, hk2]
        nlinarith [hcat2]
      have hre : ((k+2:ℕ):ℚ) / ((2:ℚ) * ((2*k+1:ℕ):ℚ) * (catalan k : ℚ))
          = (((k+2:ℕ):ℚ) / ((2:ℚ) * ((2*k+1:ℕ):ℚ))) * (1 / (catalan k : ℚ)) := by
        field_simp [hc]
        try ring
      rw [poch_succ, poch_succ]
      rw [hratio, hre, ih]
      field_simp [hk1, hk2, hc, hden]
      norm_num [Nat.cast_add, Nat.cast_mul]
      ring_nf

open Matrix Finset

noncomputable def catbert_matrix' (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j => 1 / (catalan (i.val + j.val) : ℚ)

noncomputable def H' (n : ℕ) (a b : ℚ) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j => poch a (i.val + j.val) / poch b (i.val + j.val)

lemma catbert_eq_scaled_H (n : ℕ) :
    catbert_matrix' n = Matrix.of (fun i j : Fin n => ((4:ℚ)^i.val)⁻¹ * ((4:ℚ)^j.val)⁻¹ * H' n 2 (1/2) i j) := by
  ext i j
  simp [catbert_matrix', H']
  rw [← one_div (catalan (i.val + j.val) : ℚ)]
  rw [catalan_inv_poch (i.val+j.val)]
  rw [pow_add]
  field_simp
  try ring

lemma det_catbert_scaled (n : ℕ) :
    (catbert_matrix' n).det = (((4:ℚ) ^ (∑ i : Fin n, i.val))⁻¹)^2 * (H' n 2 (1/2)).det := by
  classical
  rw [catbert_eq_scaled_H]
  let v : Fin n → ℚ := fun i => ((4:ℚ)^i.val)⁻¹
  let M : Matrix (Fin n) (Fin n) ℚ := H' n 2 (1/2)
  have hscale : (Matrix.of fun i j : Fin n => v i * v j * M i j).det = (∏ i, v i) * (∏ j, v j) * M.det := by
    calc
      (Matrix.of fun i j : Fin n => v i * v j * M i j).det
          = (Matrix.of fun i j : Fin n => v i * (Matrix.of fun i j : Fin n => v j * M i j) i j).det := by
            congr; ext i j; simp; ring
      _ = (∏ i, v i) * (Matrix.of fun i j : Fin n => v j * M i j).det := by rw [Matrix.det_mul_column]
      _ = (∏ i, v i) * ((∏ j, v j) * M.det) := by rw [Matrix.det_mul_row]
      _ = (∏ i, v i) * (∏ j, v j) * M.det := by ring
  rw [hscale]
  have hprod : (∏ i : Fin n, v i) = ((4:ℚ) ^ (∑ i : Fin n, i.val))⁻¹ := by
    simp [v, Finset.prod_inv_distrib, ← Finset.prod_pow_eq_pow_sum]
  rw [hprod]
  ring

lemma fin_sum_val (n : ℕ) : (∑ i : Fin n, i.val) = n*(n-1)/2 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => i) n]
  exact Finset.sum_range_id n

lemma det_catbert_scaled_simple (n : ℕ) :
    (catbert_matrix' n).det = ((4:ℚ) ^ (n*(n-1)))⁻¹ * (H' n 2 (1/2)).det := by
  rw [det_catbert_scaled]
  rw [fin_sum_val]
  have hpow : (((4:ℚ) ^ (n * (n - 1) / 2))⁻¹) ^ 2 = ((4:ℚ) ^ (n*(n-1)))⁻¹ := by
    rw [inv_pow]
    rw [← pow_mul]
    have hEven : 2 ∣ n*(n-1) := by
      exact (even_iff_two_dvd.mp (Nat.even_mul_pred_self n))
    have hmul : (n*(n-1)/2)*2 = n*(n-1) := Nat.div_mul_cancel hEven
    rw [hmul]
  rw [hpow]

