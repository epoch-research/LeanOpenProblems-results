import Mathlib
import Submission.Spec2_part2
import Submission.Spec2_part3
import Submission.SpecPell
import Submission.Spec4

lemma PQ_mod_2 (n : ℕ) : (P n) % 2 = (n : ℤ) % 2 ∧ (Q n) % 2 = 1 := by
  induction n with
  | zero => decide
  | succ n ih =>
    have hP := (PQ_step n).1
    have hQ := (PQ_step n).2
    rw [hP, hQ]
    rcases ih with ⟨ihP, ihQ⟩
    constructor
    · omega
    · omega

lemma neg_one_pow_mod (a b : ℕ) (h : a % 2 = b % 2) : (-1 : ℤ)^a = (-1 : ℤ)^b := by
  have H1 : a = 2 * (a / 2) + a % 2 := (Nat.div_add_mod a 2).symm
  have H2 : b = 2 * (b / 2) + b % 2 := (Nat.div_add_mod b 2).symm
  nth_rw 1 [H1]
  nth_rw 1 [H2]
  rw [h]
  have H_pow (x r : ℕ) : (-1 : ℤ)^(2 * x + r) = (-1 : ℤ)^r := by
    rw [pow_add, pow_mul]
    have : (-1 : ℤ)^2 = 1 := by norm_num
    rw [this, one_pow, one_mul]
  rw [H_pow, H_pow]

lemma exists_x (k : ℤ) (hk : 0 < k) : ∃ x : ℤ, 0 < x ∧ x^2 ≤ 2*k^2 ∧ 2*k^2 < (x+1)^2 := by
  have H0 : (0:ℝ) ≤ 2 * (k:ℝ)^2 := by positivity
  let x_real := Real.sqrt (2 * (k:ℝ)^2)
  let x := Int.floor x_real
  use x
  have hx : (x : ℝ) ≤ x_real := Int.floor_le x_real
  have hx1 : x_real < (x + 1 : ℝ) := Int.lt_floor_add_one x_real
  have h_x_pos_le : (0:ℝ) ≤ x_real := by positivity
  have hk2_le : (0:ℝ) < 2 * (k:ℝ)^2 := by
    have : (0:ℝ) < (k:ℝ) := by exact_mod_cast hk
    positivity
  have h_sq1_eval : x_real^2 = 2 * (k:ℝ)^2 := Real.sq_sqrt H0
  have hx_pos : 0 < x := by
    have h_not_r : (x : ℝ) < 1 ↔ x ≤ 0 := by exact_mod_cast (by omega : x < 1 ↔ x ≤ 0)
    by_contra h_not
    push_neg at h_not
    have : (x:ℝ) ≤ 0 := by exact_mod_cast h_not
    have : x_real < 1 := by linarith
    have : x_real^2 < 1^2 := by nlinarith
    have : 2 * (k:ℝ)^2 < 1 := by linarith
    have : 2 * k^2 < 1 := by exact_mod_cast this
    have : 2 ≤ 2 * k^2 := by nlinarith
    linarith
  have h_sq1 : (x : ℝ)^2 ≤ x_real^2 := by
    have hx_pos_r : (0:ℝ) ≤ x := by exact_mod_cast (by omega : 0 ≤ x)
    nlinarith
  rw [h_sq1_eval] at h_sq1
  have h_sq1_int : x^2 ≤ 2*k^2 := by exact_mod_cast h_sq1
  have h_sq2 : x_real^2 < (x + 1 : ℝ)^2 := by nlinarith
  rw [h_sq1_eval] at h_sq2
  have h_sq2_int : 2*k^2 < (x+1)^2 := by exact_mod_cast h_sq2
  exact ⟨hx_pos, h_sq1_int, h_sq2_int⟩

lemma PQ_rel_odd_2j1 (j : ℕ) : (Q (2*j+1))^2 = 2 * (P (2*j+1))^2 - 1 := by
  have h := PQ_rel (2*j+1)
  have h_odd : (-1 : ℤ)^(2*j+1) = -1 := by
    calc (-1 : ℤ)^(2*j+1) = (-1 : ℤ)^(2*j) * (-1) := by ring
      _ = ((-1 : ℤ)^2)^j * (-1) := by rw [pow_mul]
      _ = 1^j * (-1) := by norm_num
      _ = -1 := by ring
  rw [h_odd] at h
  linarith

lemma irrational_sqrt_2_int (x k : ℤ) (hk : 0 < k) (hx : 0 < x) : 2 * k^2 ≠ x^2 := by
  intro H
  have h_eq : (2 : ℝ) * (k : ℝ)^2 = (x : ℝ)^2 := by exact_mod_cast H
  have h_div : (2 : ℝ) = ((x : ℝ) / (k : ℝ))^2 := by
    rw [div_pow]
    have hk_ne : (k : ℝ)^2 ≠ 0 := pow_ne_zero 2 (by exact_mod_cast (ne_of_gt hk))
    calc (2 : ℝ) = (2 : ℝ) * (k : ℝ)^2 / (k : ℝ)^2 := by rw [mul_div_cancel_right₀ _ hk_ne]
      _ = (x : ℝ)^2 / (k : ℝ)^2 := by rw [h_eq]
  have h_sqrt : Real.sqrt 2 = (x : ℝ) / (k : ℝ) := by
    have h_pos : (0 : ℝ) ≤ (x : ℝ) / (k : ℝ) := by
      apply div_nonneg
      · exact_mod_cast (le_of_lt hx)
      · exact_mod_cast (le_of_lt hk)
    rw [h_div]
    exact Real.sqrt_sq h_pos
  have h_rat : Real.sqrt 2 = (((x : ℚ) / (k : ℚ) : ℚ) : ℝ) := by
    rw [h_sqrt]
    push_cast
    rfl
  have h_irr := irrational_sqrt_two
  exact h_irr ⟨(x : ℚ) / (k : ℚ), h_rat.symm⟩

lemma parity_lemma (A B : ℤ) (hA : A % 2 = 1) (hB : B % 2 = 1) : (B - A) % 2 = 0 := by omega

lemma k_le_x_lem (x k : ℤ) (hk : 0 < k) (hx_pos : 0 < x) (hx2 : 2*k^2 < (x+1)^2) : k ≤ x := by
  by_contra h_not
  push_neg at h_not
  have h_not' : x + 1 ≤ k := h_not
  have : (x+1)^2 ≤ k^2 := by nlinarith
  have : 0 ≤ k^2 := by nlinarith
  linarith

lemma P_le_Q_lem (P Q : ℤ) (hP : 0 < P) (hQ : 0 < Q) (hQ_sq : Q^2 = 2*P^2 - 1) : P ≤ Q := by
  by_contra h_not
  push_neg at h_not
  have h_not' : Q + 1 ≤ P := h_not
  have : (Q+1)^2 ≤ P^2 := by nlinarith
  have : 0 ≤ Q^2 := by nlinarith
  have : 1 ≤ P^2 := by nlinarith
  linarith

lemma P_le_Q_lem_even (P Q : ℤ) (hP : 0 < P) (hQ : 0 < Q) (hQ_sq : Q^2 = 2*P^2 + 1) : P ≤ Q := by
  by_contra h_not
  push_neg at h_not
  have h_not' : Q + 1 ≤ P := h_not
  have : (Q+1)^2 ≤ P^2 := by nlinarith
  have : 0 ≤ Q^2 := by nlinarith
  have : 1 ≤ P^2 := by nlinarith
  linarith

lemma b_jump_P_odd (j : ℕ) (k : ℕ) (hk1 : 0 < k) (hk2 : k ≤ (P (2*j+1)).toNat) :
  b (k + (P (2*j+1)).toNat) = b k := by
  have hk_int : 0 < (k:ℤ) := by exact_mod_cast hk1
  obtain ⟨x, hx_pos, hx1, hx2⟩ := exists_x (k:ℤ) hk_int
  have b_eval_k := b_eval k hk1 x hx_pos hx1 hx2
  
  have hP_pos : 0 < P (2*j+1) := P_strict_pos (2*j+1) (by omega)
  have hk_bound : (k:ℤ) ≤ P (2*j+1) := by
    have : (k:ℤ) ≤ ((P (2*j+1)).toNat : ℤ) := by exact_mod_cast hk2
    have h_toNat : ((P (2*j+1)).toNat : ℤ) = P (2*j+1) := Int.toNat_of_nonneg (by omega)
    rwa [h_toNat] at this
    
  have hQ_pos : 0 < Q (2*j+1) := (PQ_pos (2*j+1)).2
  have hQ_sq : (Q (2*j+1))^2 = 2 * (P (2*j+1))^2 - 1 := PQ_rel_odd_2j1 j
  have h2k2_x2 : 1 ≤ 2*(k:ℤ)^2 - x^2 := by
    have H : 2*(k:ℤ)^2 ≠ x^2 := irrational_sqrt_2_int x k hk_int hx_pos
    omega
  have H_jump := jump_P_odd (k:ℤ) (P (2*j+1)) (Q (2*j+1)) x hk_int hP_pos hx_pos hQ_pos hQ_sq hx1 (by linarith) h2k2_x2 hk_bound
  rcases H_jump with ⟨H_jump1, H_jump2⟩
  
  have hk_shift_pos : 0 < k + (P (2*j+1)).toNat := by omega
  have h_xQ_pos : 0 < x + Q (2*j+1) := by linarith
  
  have h_toNat : ((P (2*j+1)).toNat : ℤ) = P (2*j+1) := Int.toNat_of_nonneg (by omega)
  have H_jump1_cast : (x + Q (2 * j + 1))^2 ≤ 2 * (↑(k + (P (2 * j + 1)).toNat):ℤ)^2 := by
    push_cast
    rw [h_toNat]
    exact H_jump1
  have H_jump2_cast : 2 * (↑(k + (P (2 * j + 1)).toNat):ℤ)^2 < (x + Q (2 * j + 1) + 1)^2 := by
    push_cast
    rw [h_toNat]
    exact H_jump2
    
  have b_eval_shifted := b_eval (k + (P (2*j+1)).toNat) hk_shift_pos (x + Q (2*j+1)) h_xQ_pos H_jump1_cast H_jump2_cast
  rw [b_eval_k, b_eval_shifted]
  
  have h_diff1_pos : 0 ≤ x - (k:ℤ) := by
    have h_kx := k_le_x_lem x k hk_int hx_pos hx2
    omega
  have h_diff2_pos : 0 ≤ x + Q (2*j+1) - ↑(k + (P (2*j+1)).toNat) := by
    push_cast
    rw [h_toNat]
    have h_kx := k_le_x_lem x k hk_int hx_pos hx2
    have h_PQ := P_le_Q_lem (P (2*j+1)) (Q (2*j+1)) hP_pos hQ_pos hQ_sq
    omega
    
  apply neg_one_pow_mod
  have H_mod := PQ_mod_2 (2*j+1)
  rcases H_mod with ⟨H_mod_P, H_mod_Q⟩
  
  have h_zmod : ((x + Q (2*j+1) - ↑(k + (P (2*j+1)).toNat)).toNat : ℤ) % 2 = ((x - ↑k).toNat : ℤ) % 2 := by
    rw [Int.toNat_of_nonneg h_diff2_pos, Int.toNat_of_nonneg h_diff1_pos]
    push_cast
    rw [h_toNat]
    have h1 : (P (2 * j + 1)) % 2 = 1 := by
      calc (P (2 * j + 1)) % 2 = (↑(2 * j + 1) : ℤ) % 2 := H_mod_P
        _ = 1 := by omega
    have h2 : (Q (2 * j + 1)) % 2 = 1 := H_mod_Q
    have h_even := parity_lemma (P (2*j+1)) (Q (2*j+1)) h1 h2
    have : x + Q (2 * j + 1) - (↑k + P (2 * j + 1)) = (x - ↑k) + (Q (2 * j + 1) - P (2 * j + 1)) := by ring
    rw [this, Int.add_emod]
    rw [h_even]
    omega
    
  exact_mod_cast h_zmod

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
  · have h_b1 : (b + 1) % 2 = 1 := by omega
    rw [h_b1]
    nth_rw 1 [H2]
    rw [hb, H_pow]
    norm_num
  · have h_b1 : (b + 1) % 2 = 0 := by omega
    rw [h_b1]
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
    have h_PQ := P_le_Q_lem_even (P (2*j)) (Q (2*j)) hP_pos hQ_pos hQ_sq
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

lemma bound_2P (j k : ℕ) (hj : 0 < j) (hk2 : k ≤ (P (2*j-1)).toNat) :
  2 * (k : ℤ)^2 ≤ (P (2*j))^2 - 1 := by
  have H_P_pos_1 : 0 ≤ P (2*j-1) := (PQ_pos (2*j-1)).1
  have hk_bound : (k:ℤ) ≤ P (2*j-1) := by
    have : (k:ℤ) ≤ ((P (2*j-1)).toNat : ℤ) := by exact_mod_cast hk2
    have h_toNat : ((P (2*j-1)).toNat : ℤ) = P (2*j-1) := Int.toNat_of_nonneg H_P_pos_1
    rwa [h_toNat] at this
  have hP_pos : 0 < P (2*j-1) := P_strict_pos (2*j-1) (by omega)
  have hQ_pos : 0 < Q (2*j-1) := (PQ_pos (2*j-1)).2
  have hQ_sq : (Q (2*j-1))^2 = 2 * (P (2*j-1))^2 - 1 := by
    have H : 2*j-1 > 0 := by omega
    exact PQ_rel_odd (j) hj
  have h_PQ : P (2*j-1) ≤ Q (2*j-1) := P_le_Q_lem (P (2*j-1)) (Q (2*j-1)) hP_pos hQ_pos hQ_sq
  have H_P2j : P (2*j) = Q (2*j-1) + P (2*j-1) := by
    have H1 : 2*j-1+1 = 2*j := by omega
    have H2 := (PQ_step (2*j-1)).1
    rw [H1] at H2
    exact H2
  have H_ineq : 2 * P (2*j-1) ≤ P (2*j) := by linarith
  have H_sq : 4 * (P (2*j-1))^2 ≤ (P (2*j))^2 := by
    have H_pos : 0 ≤ 2 * P (2*j-1) := by linarith
    have H_P2j_pos : 0 ≤ P (2*j) := (PQ_pos (2*j)).1
    have H_mul : (2 * P (2*j-1))^2 ≤ (P (2*j))^2 := by nlinarith
    linarith
  have : 2 * (k:ℤ)^2 ≤ 2 * (P (2*j-1))^2 := by
    have : (k:ℤ)^2 ≤ (P (2*j-1))^2 := by nlinarith
    linarith
  have : 1 ≤ 2 * (P (2*j-1))^2 := by nlinarith
  linarith

lemma b_jump_2P_even (j : ℕ) (k : ℕ) (hj : 0 < j) (hk1 : 0 < k) (hk2 : k ≤ (P (2*j-1)).toNat) :
  b (k + (2 * P (2*j)).toNat) = b k := by
  have hk_int : 0 < (k:ℤ) := by exact_mod_cast hk1
  obtain ⟨x, hx_pos, hx1, hx2⟩ := exists_x (k:ℤ) hk_int
  have b_eval_k := b_eval k hk1 x hx_pos hx1 hx2
  
  have hP_pos : 0 < P (2*j) := P_strict_pos (2*j) (by omega)
  have hk_bound : 2*(k:ℤ)^2 ≤ (P (2*j))^2 - 1 := bound_2P j k hj hk2
    
  have hQ_pos : 0 < Q (2*j) := (PQ_pos (2*j)).2
  have hQ_sq : (Q (2*j))^2 = 2 * (P (2*j))^2 + 1 := PQ_rel_even_2j j
  have h2k2_x2 : 1 ≤ 2*(k:ℤ)^2 - x^2 := by
    have H : 2*(k:ℤ)^2 ≠ x^2 := irrational_sqrt_2_int x k hk_int hx_pos
    omega
  have H_jump := jump_2P_even (k:ℤ) (P (2*j)) (Q (2*j)) x hk_int hP_pos hx_pos hQ_pos hQ_sq hx1 (by linarith) h2k2_x2 hk_bound
  rcases H_jump with ⟨H_jump1, H_jump2⟩
  
  have hk_shift_pos : 0 < k + (2 * P (2*j)).toNat := by omega
  have h_xQ_pos : 0 < x + 2 * Q (2*j) := by linarith
  
  have h_toNat : ((2 * P (2*j)).toNat : ℤ) = 2 * P (2*j) := Int.toNat_of_nonneg (by omega)
  have H_jump1_cast : (x + 2 * Q (2*j))^2 ≤ 2 * (↑(k + (2 * P (2*j)).toNat):ℤ)^2 := by
    push_cast
    rw [h_toNat]
    exact H_jump1
  have H_jump2_cast : 2 * (↑(k + (2 * P (2*j)).toNat):ℤ)^2 < (x + 2 * Q (2*j) + 1)^2 := by
    push_cast
    rw [h_toNat]
    exact H_jump2
    
  have b_eval_shifted := b_eval (k + (2 * P (2*j)).toNat) hk_shift_pos (x + 2 * Q (2*j)) h_xQ_pos H_jump1_cast H_jump2_cast
  rw [b_eval_k, b_eval_shifted]
  
  have h_diff1_pos : 0 ≤ x - (k:ℤ) := by
    have h_kx := k_le_x_lem x k hk_int hx_pos hx2
    omega
  have h_diff2_pos : 0 ≤ x + 2 * Q (2*j) - ↑(k + (2 * P (2*j)).toNat) := by
    push_cast
    rw [h_toNat]
    have h_kx := k_le_x_lem x k hk_int hx_pos hx2
    have h_PQ := P_le_Q_lem_even (P (2*j)) (Q (2*j)) hP_pos hQ_pos hQ_sq
    omega
    
  apply neg_one_pow_mod
  have H_mod := PQ_mod_2 (2*j)
  rcases H_mod with ⟨H_mod_P, H_mod_Q⟩
  
  have h_zmod : ((x + 2 * Q (2*j) - ↑(k + (2 * P (2*j)).toNat)).toNat : ℤ) % 2 = ((x - ↑k).toNat : ℤ) % 2 := by
    rw [Int.toNat_of_nonneg h_diff2_pos, Int.toNat_of_nonneg h_diff1_pos]
    push_cast
    rw [h_toNat]
    have h1 : (P (2 * j)) % 2 = 0 := by
      calc (P (2 * j)) % 2 = (↑(2 * j) : ℤ) % 2 := H_mod_P
        _ = 0 := by omega
    have h2 : (Q (2 * j)) % 2 = 1 := H_mod_Q
    have h_even : (2 * Q (2*j) - 2 * P (2*j)) % 2 = 0 := by omega
    have : x + 2 * Q (2 * j) - (↑k + 2 * P (2 * j)) = (x - ↑k) + (2 * Q (2 * j) - 2 * P (2 * j)) := by ring
    rw [this, Int.add_emod]
    rw [h_even]
    omega
    
  exact_mod_cast h_zmod
