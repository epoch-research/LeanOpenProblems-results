import Mathlib
import Submission.Spec2_part2
import Submission.Spec2_part3
import Submission.SpecPell
import Submission.Spec4
import Submission.SpecSum

lemma PQ_rel_even_2j (j : ℕ) : (Q (2*j))^2 = 2 * (P (2*j))^2 + 1 := by
  have h := PQ_rel (2*j)
  have h_even : (-1 : ℤ)^(2*j) = 1 := by
    calc (-1 : ℤ)^(2*j) = ((-1 : ℤ)^2)^j := by rw [pow_mul]
      _ = 1^j := by norm_num
      _ = 1 := by ring
  rw [h_even] at h
  linarith

lemma neg_one_pow_mod_anti (a b : ℕ) (h : a % 2 = (b + 1) % 2) : (-1 : ℤ)^a = - (-1 : ℤ)^b := by
  have H1 : a = 2 * (a / 2) + a % 2 := (Nat.div_add_mod a 2).symm
  have H2 : b = 2 * (b / 2) + b % 2 := (Nat.div_add_mod b 2).symm
  nth_rw 1 [H1]
  have H_pow (x r : ℕ) : (-1 : ℤ)^(2 * x + r) = (-1 : ℤ)^r := by
    rw [pow_add, pow_mul]
    have : (-1 : ℤ)^2 = 1 := by norm_num
    rw [this, one_pow, one_mul]
  rw [H_pow]
  rw [h]
  have H_cases : b % 2 = 0 ∨ b % 2 = 1 := by omega
  rcases H_cases with hb | hb
  · rw [hb]
    have : (0 + 1) % 2 = 1 := by decide
    rw [this]
    nth_rw 1 [H2]
    rw [hb, H_pow]
    norm_num
  · rw [hb]
    have : (1 + 1) % 2 = 0 := by decide
    rw [this]
    nth_rw 1 [H2]
    rw [hb, H_pow]
    norm_num

lemma b_jump_P_even (j : ℕ) (k : ℕ) (hj : 0 < j) (hk1 : 0 < k) (hk2 : k ≤ (P (2*j)).toNat) :
  b (k + (P (2*j)).toNat) = - b k := by
  have hk_int : 0 < (k:ℤ) := by exact_mod_cast hk1
  obtain ⟨x, hx_pos, hx1, hx2⟩ := exists_x (k:ℤ) hk_int
  have b_eval_k := b_eval k hk1 x hx_pos hx1 hx2
  
  have hP_pos : 0 < P (2*j) := P_strict_pos (2*j) (by omega)
  have hk_bound : (k:ℤ) ≤ P (2*j) := by
    have : (k:ℤ) ≤ ((P (2*j)).toNat : ℤ) := by exact_mod_cast hk2
    have h_toNat : ((P (2*j)).toNat : ℤ) = P (2*j) := Int.toNat_of_nonneg (by omega)
    rwa [h_toNat] at this
    
  have hQ_pos : 0 < Q (2*j) := (PQ_pos (2*j)).2
  have hQ_sq : (Q (2*j))^2 = 2 * (P (2*j))^2 + 1 := PQ_rel_even_2j j
  have h2k2_x2 : 1 ≤ 2*(k:ℤ)^2 - x^2 := by
    have H : 2*(k:ℤ)^2 ≠ x^2 := irrational_sqrt_2_int x k hk_int hx_pos
    omega
  have H_jump := jump_P_even (k:ℤ) (P (2*j)) (Q (2*j)) x hk_int hP_pos hx_pos hQ_pos hQ_sq hx1 (by linarith) h2k2_x2 hk_bound
  rcases H_jump with ⟨H_jump1, H_jump2⟩
  
  have hk_shift_pos : 0 < k + (P (2*j)).toNat := by omega
  have h_xQ_pos : 0 < x + Q (2*j) := by linarith
  
  have h_toNat : ((P (2*j)).toNat : ℤ) = P (2*j) := Int.toNat_of_nonneg (by omega)
  have H_jump1_cast : (x + Q (2*j))^2 ≤ 2 * (↑(k + (P (2*j)).toNat):ℤ)^2 := by
    push_cast
    rw [h_toNat]
    exact H_jump1
  have H_jump2_cast : 2 * (↑(k + (P (2*j)).toNat):ℤ)^2 < (x + Q (2*j) + 1)^2 := by
    push_cast
    rw [h_toNat]
    exact H_jump2
    
  have b_eval_shifted := b_eval (k + (P (2*j)).toNat) hk_shift_pos (x + Q (2*j)) h_xQ_pos H_jump1_cast H_jump2_cast
  rw [b_eval_k, b_eval_shifted]
  
  have h_diff1_pos : 0 ≤ x - (k:ℤ) := by
    have h_kx := k_le_x_lem x k hk_int hx_pos hx2
    omega
  have h_diff2_pos : 0 ≤ x + Q (2*j) - ↑(k + (P (2*j)).toNat) := by
    push_cast
    rw [h_toNat]
    have h_kx := k_le_x_lem x k hk_int hx_pos hx2
    have h_PQ : P (2*j) ≤ Q (2*j) := by
      have : (P (2*j))^2 ≤ (Q (2*j))^2 := by linarith
      exact my_sq_le_sq (P (2*j)) (Q (2*j)) (by linarith) (by linarith) this
    omega
    
  apply neg_one_pow_mod_anti
  have H_mod := PQ_mod_2 (2*j)
  rcases H_mod with ⟨H_mod_P, H_mod_Q⟩
  
  have h_zmod : ((x + Q (2*j) - ↑(k + (P (2*j)).toNat)).toNat : ℤ) % 2 = (((x - ↑k).toNat + 1) : ℤ) % 2 := by
    rw [Int.toNat_of_nonneg h_diff2_pos]
    push_cast
    rw [Int.toNat_of_nonneg h_diff1_pos]
    push_cast
    rw [h_toNat]
    have h1 : (P (2 * j)) % 2 = 0 := by
      calc (P (2 * j)) % 2 = (↑(2 * j) : ℤ) % 2 := H_mod_P
        _ = 0 := by omega
    have h2 : (Q (2 * j)) % 2 = 1 := H_mod_Q
    have h_odd : (Q (2*j) - P (2*j)) % 2 = 1 := by omega
    have : x + Q (2 * j) - (↑k + P (2 * j)) = (x - ↑k) + (Q (2 * j) - P (2 * j)) := by ring
    rw [this, Int.add_emod]
    rw [h_odd]
    omega
    
  exact_mod_cast h_zmod
