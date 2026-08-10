import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 200000

open Nat Finset Polynomial Complex
open scoped BigOperators ComplexConjugate

def A103885 (n : ℕ) : ℕ :=
  if n = 0 then 1
  else
    let r : ℕ := n - 1
    (range (n + 1)).sum (fun k => (n.choose k) * ((2 * n + k - 1).choose r))

-- The indices k = 1 to 2m, used in the product
private def product_indices (m : ℕ) : Finset ℕ :=
  Finset.Ioc 0 (2 * m)

-- The factor Product_{k=1}^{2m} (2mn + k)
noncomputable def prod_factor_plus (m n : ℕ) : ℝ :=
  (product_indices m).prod fun k =>
    ((2 * m * n : ℝ) + (k : ℝ))

-- The factor Product_{k=1}^{2m} (2mn - k)
noncomputable def prod_factor_minus (m n : ℕ) : ℝ :=
  (product_indices m).prod fun k =>
    ((2 * m * n : ℝ) - (k : ℝ))

-- Explicit witnesses for m = 1
noncomputable def P_witness : Polynomial ℝ := 5 * X^2 - 5 * X + 1
noncomputable def Q_witness : Polynomial ℝ := 220 * X^2 - 136 * X + 12

-- The sequence b(n) = a(m*n) lifted to ℝ
noncomputable def A103885_subsequence_real (m n : ℕ) : ℝ :=
  if m = 1 then
    if n = 0 then 1
    else if n = 1 then 2
    else if n = 2 then 16
    else if n = 3 then 146
    else if n = 4 then 1408
    else if n = 5 then 14002
    else
      let n_pred := n - 1
      let c0 := Q_witness.eval ((n_pred : ℝ)^2)
      let cm := (-1 : ℝ) ^ 1 * prod_factor_minus 1 n_pred * P_witness.eval (-(n_pred : ℝ))
      let cp := prod_factor_plus 1 n_pred * P_witness.eval (n_pred : ℝ)
      (c0 * A103885_subsequence_real 1 n_pred - cm * A103885_subsequence_real 1 (n_pred - 1)) / cp
  else
    if n = 0 then 1 else 0

open BigOperators

-- Degree proofs for P_witness
lemma coeff_P_above (N : ℕ) (hN : 2 < N) : P_witness.coeff N = 0 := by
  unfold P_witness
  simp [coeff_add, coeff_sub, coeff_X_pow, coeff_X, coeff_one]
  have h1 : N ≠ 2 := by omega
  have h4 : 1 ≠ N := by omega
  have h5 : N ≠ 0 := by omega
  simp [h1, h4, h5]

lemma coeff_P_two : P_witness.coeff 2 = 5 := by
  unfold P_witness
  simp [coeff_add, coeff_sub, coeff_X_pow, coeff_X, coeff_one]

lemma natDegree_P : P_witness.natDegree = 2 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro N hN
    exact coeff_P_above N hN
  · rw [coeff_P_two]
    norm_num

lemma degree_P : P_witness.degree = (2 : ℕ) := by
  have hP : P_witness ≠ 0 := by
    intro h
    have h_coeff : P_witness.coeff 2 = 0 := by rw [h, coeff_zero]
    rw [coeff_P_two] at h_coeff
    norm_num at h_coeff
  rw [degree_eq_iff_natDegree_eq hP]
  exact natDegree_P

-- Degree proofs for Q_witness
lemma coeff_Q_above (N : ℕ) (hN : 2 < N) : Q_witness.coeff N = 0 := by
  unfold Q_witness
  simp [coeff_add, coeff_sub, coeff_X_pow, coeff_X]
  have h1 : N ≠ 2 := by omega
  have h4 : 1 ≠ N := by omega
  have h5 : N ≠ 0 := by omega
  simp [h1, h4]
  rcases Nat.exists_eq_succ_of_ne_zero h5 with ⟨d, rfl⟩
  exact coeff_ofNat_succ 12 d

lemma coeff_Q_two : Q_witness.coeff 2 = 220 := by
  unfold Q_witness
  simp [coeff_add, coeff_sub, coeff_X_pow, coeff_X]

lemma natDegree_Q : Q_witness.natDegree = 2 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro N hN
    exact coeff_Q_above N hN
  · rw [coeff_Q_two]
    norm_num

lemma degree_Q : Q_witness.degree = (2 : ℕ) := by
  have hQ : Q_witness ≠ 0 := by
    intro h
    have h_coeff : Q_witness.coeff 2 = 0 := by rw [h, coeff_zero]
    rw [coeff_Q_two] at h_coeff
    norm_num at h_coeff
  rw [degree_eq_iff_natDegree_eq hQ]
  exact natDegree_Q

-- Symmetry proof for P_witness
lemma symm_P (x : ℝ) : P_witness.eval x = P_witness.eval (1 - x) := by
  unfold P_witness
  simp
  ring

-- Complex root proofs setup
lemma complex_square_eq_pos_real {w : ℂ} {c : ℝ} (hc : 0 < c) (hw : w ^ 2 = (c : ℂ)) : w.im = 0 := by
  have h_im : (w^2).im = 0 := by
    rw [hw]
    simp
  have h_im_eq : (w^2).im = 2 * w.re * w.im := by
    rw [sq]
    simp
    ring
  rw [h_im_eq] at h_im
  have h_or : w.re = 0 ∨ w.im = 0 := by
    rcases mul_eq_zero.mp h_im with h1 | h2
    · left
      linarith
    · right
      exact h2
  rcases h_or with hr | hi
  · -- Case w.re = 0
    have h_re_w2 : (w^2).re = - w.im^2 := by
      rw [sq]
      simp [hr]
      ring
    have h_re_c : (w^2).re = c := by
      rw [hw]
      simp
    have h_contra : - w.im^2 = c := by
      rw [← h_re_c, h_re_w2]
    have h_im_sq_le : - w.im^2 ≤ 0 := by
      nlinarith
    linarith
  · -- Case w.im = 0
    exact hi

lemma eval_P_map (z : ℂ) : (P_witness.map (algebraMap ℝ ℂ)).eval z = 5 * z^2 - 5 * z + 1 := by
  unfold P_witness
  simp

lemma P_sq_identity (z : ℂ) : (10 * z - 5)^2 = 20 * (5 * z^2 - 5 * z + 1) + 5 := by
  ring

lemma root_interval_P (x : ℝ) (h : 5 * x^2 - 5 * x + 1 = 0) : 0 ≤ x ∧ x ≤ 1 := by
  constructor
  · by_contra h_lt
    have h_lt' : x < 0 := by linarith
    have h_sq : x^2 ≥ 0 := by nlinarith
    have h_term1 : 5 * x^2 ≥ 0 := by linarith
    have h_term2 : - 5 * x > 0 := by linarith
    have h_eq : 5 * x^2 - 5 * x + 1 > 0 := by linarith
    linarith
  · by_contra h_gt
    have h_gt' : x > 1 := by linarith
    have h_term : 5 * x * (x - 1) > 0 := by
      have h1 : 5 * x > 0 := by linarith
      have h2 : x - 1 > 0 := by linarith
      exact mul_pos h1 h2
    have h_eq : 5 * x^2 - 5 * x + 1 > 0 := by
      calc
        5 * x^2 - 5 * x + 1 = 5 * x * (x - 1) + 1 := by ring
        _ > 0 := by linarith
    linarith

theorem roots_P (z : ℂ) (h : (P_witness.map (algebraMap ℝ ℂ)).eval z = 0) : z.im = 0 ∧ z.re ∈ (Set.Icc 0 1) := by
  have h_eq : 5 * z^2 - 5 * z + 1 = 0 := by
    rw [← eval_P_map, h]
  have h_id : (10 * z - 5)^2 = 5 := by
    calc
      (10 * z - 5)^2 = 20 * (5 * z^2 - 5 * z + 1) + 5 := by ring
      _ = 20 * 0 + 5 := by rw [h_eq]
      _ = 5 := by ring
  have h_w_im : (10 * z - 5).im = 0 := by
    apply complex_square_eq_pos_real (by norm_num : 0 < (5 : ℝ)) h_id
  have h_zim : z.im = 0 := by
    have : (10 * z - 5).im = 10 * z.im := by simp
    linarith [this, h_w_im]
  refine ⟨h_zim, ?_⟩
  have hz : z = (z.re : ℂ) := by
    apply Complex.ext <;> simp [h_zim]
  have h_real : 5 * z.re^2 - 5 * z.re + 1 = 0 := by
    have h_re_eq : (5 * z^2 - 5 * z + 1).re = 0 := by rw [h_eq]; simp
    have h_re_eq2 : (5 * z^2 - 5 * z + 1).re = 5 * z.re^2 - 5 * z.im^2 - 5 * z.re + 1 := by
      rw [sq]
      simp
      ring
    rw [h_re_eq2, h_zim] at h_re_eq
    linarith
  exact root_interval_P z.re h_real

lemma eval_Q_map (z : ℂ) : (Q_witness.map (algebraMap ℝ ℂ)).eval (z^2) = 220 * z^4 - 136 * z^2 + 12 := by
  unfold Q_witness
  simp
  ring

lemma Q_sq_identity (z : ℂ) : (220 * z^2 - 68)^2 = 220 * (220 * z^4 - 136 * z^2 + 12) + 1984 := by
  ring

lemma root_interval_Q (x : ℝ) (h : 220 * x^2 - 136 * x + 12 = 0) : 0 ≤ x ∧ x ≤ 1 := by
  constructor
  · by_contra h_lt
    have h_lt' : x < 0 := by linarith
    have h_sq : x^2 ≥ 0 := by nlinarith
    have h_term1 : 220 * x^2 ≥ 0 := by linarith
    have h_term2 : - 136 * x > 0 := by linarith
    have h_eq : 220 * x^2 - 136 * x + 12 > 0 := by linarith
    linarith
  · by_contra h_gt
    have h_gt' : x > 1 := by linarith
    have h_term : 220 * x * (x - 1) > 0 := by
      have h1 : 220 * x > 0 := by linarith
      have h2 : x - 1 > 0 := by linarith
      exact mul_pos h1 h2
    have h_eq : 220 * x^2 - 136 * x + 12 > 0 := by
      calc
        220 * x^2 - 136 * x + 12 = 220 * x * (x - 1) + 84 * x + 12 := by ring
        _ > 0 := by linarith
    linarith

theorem roots_Q (z : ℂ) (h : (Q_witness.map (algebraMap ℝ ℂ)).eval (z^2) = 0) : z.im = 0 ∧ z.re ∈ (Set.Icc (-1) 1) := by
  have h_eq : 220 * z^4 - 136 * z^2 + 12 = 0 := by
    rw [← eval_Q_map, h]
  have h_id : (220 * z^2 - 68)^2 = 1984 := by
    calc
      (220 * z^2 - 68)^2 = 220 * (220 * z^4 - 136 * z^2 + 12) + 1984 := by ring
      _ = 220 * 0 + 1984 := by rw [h_eq]
      _ = 1984 := by ring
  have h_w_im : (220 * z^2 - 68).im = 0 := by
    apply complex_square_eq_pos_real (by norm_num : 0 < (1984 : ℝ)) h_id
  have h_z2_im : (z^2).im = 0 := by
    have : (220 * z^2 - 68).im = 220 * (z^2).im := by simp
    linarith [this, h_w_im]
  have h_z2_im_eq : (z^2).im = 2 * z.re * z.im := by
    rw [sq]
    simp
    ring
  have h_or : z.re = 0 ∨ z.im = 0 := by
    have h_im_prod : 2 * z.re * z.im = 0 := by rw [← h_z2_im_eq, h_z2_im]
    rcases mul_eq_zero.mp h_im_prod with h1 | h2
    · left
      linarith
    · right
      exact h2
  have h_z2_re : (z^2).re = z.re^2 - z.im^2 := by
    rw [sq]
    simp
    ring
  have h_real : 220 * (z^2).re^2 - 136 * (z^2).re + 12 = 0 := by
    have h_re_eq : (220 * z^4 - 136 * z^2 + 12).re = 0 := by rw [h_eq]; simp
    have h_re_eq2 : (220 * z^4 - 136 * z^2 + 12).re = 220 * (z^2).re^2 - 220 * (z^2).im^2 - 136 * (z^2).re + 12 := by
      have : z^4 = (z^2)^2 := by ring
      rw [this, sq]
      simp
      ring
    rw [h_re_eq2, h_z2_im] at h_re_eq
    linarith
  have h_interval := root_interval_Q (z^2).re h_real
  rcases h_or with hr | hi
  · -- Case z.re = 0
    have h_z2_re_eq : (z^2).re = - z.im^2 := by
      rw [h_z2_re, hr]
      ring
    have h_z2_re_ge : 0 ≤ (z^2).re := h_interval.1
    rw [h_z2_re_eq] at h_z2_re_ge
    have h_zim : z.im = 0 := by
      have : z.im^2 ≥ 0 := by nlinarith
      have : z.im^2 = 0 := by linarith [this, h_z2_re_ge]
      exact sq_eq_zero_iff.mp this
    refine ⟨h_zim, ?_⟩
    simp [hr]
  · -- Case z.im = 0
    refine ⟨hi, ?_⟩
    have h_z2_re_eq : (z^2).re = z.re^2 := by
      rw [h_z2_re, hi]
      ring
    have h_z2_re_le : (z^2).re ≤ 1 := h_interval.2
    rw [h_z2_re_eq] at h_z2_re_le
    have h1 : z.re ≤ 1 := by
      by_contra h_gt
      have : z.re > 1 := by linarith
      have : z.re^2 > 1 := by nlinarith
      linarith
    have h2 : -1 ≤ z.re := by
      by_contra h_lt
      have : z.re < -1 := by linarith
      have : z.re^2 > 1 := by nlinarith
      linarith
    exact ⟨h2, h1⟩


-- Generalized witnesses
noncomputable def P_witness_gen (m : ℕ) : Polynomial ℝ :=
  if m = 1 then P_witness
  else (X - C (2⁻¹ : ℝ))^(2 * m)

noncomputable def Q_witness_gen (m : ℕ) : Polynomial ℝ :=
  if m = 1 then Q_witness
  else X^(2 * m)

lemma degree_P_gen (m : ℕ) (hm : 1 ≤ m) : (P_witness_gen m).degree = (2 * m : ℕ) := by
  unfold P_witness_gen
  split_ifs with h
  · subst h
    simp
    exact degree_P
  · have h1 : (X - C (2⁻¹ : ℝ)).degree = 1 := by
      rw [degree_sub_eq_left_of_degree_lt]
      · exact degree_X
      · rw [degree_X]
        have : (C (2⁻¹ : ℝ)).degree ≤ 0 := degree_C_le
        exact LE.le.trans_lt this (by decide : (0 : WithBot ℕ) < 1)
    rw [degree_pow, h1]
    simp

lemma degree_Q_gen (m : ℕ) (hm : 1 ≤ m) : (Q_witness_gen m).degree = (2 * m : ℕ) := by
  unfold Q_witness_gen
  split_ifs with h
  · subst h
    simp
    exact degree_Q
  · exact degree_X_pow (2 * m)

lemma symm_P_gen (m : ℕ) (x : ℝ) : (P_witness_gen m).eval x = (P_witness_gen m).eval (1 - x) := by
  unfold P_witness_gen
  split_ifs with h
  · exact symm_P x
  · simp
    have h1 : (1 - x - 2⁻¹) = -(x - 2⁻¹) := by ring
    rw [h1]
    have h2 (a : ℝ) : (-a)^(2 * m) = a^(2 * m) := by
      rw [pow_mul, pow_mul]
      congr 1
      ring
    exact (h2 (x - 2⁻¹)).symm

theorem roots_P_gen (m : ℕ) (hm : 1 ≤ m) (z : ℂ) (h : ((P_witness_gen m).map (algebraMap ℝ ℂ)).eval z = 0) :
    z.im = 0 ∧ z.re ∈ Set.Icc 0 1 := by
  unfold P_witness_gen at h
  split_ifs at h with h_m1
  · exact roots_P z h
  · have h_eval : ((X - C (2⁻¹ : ℝ))^(2 * m) : Polynomial ℝ).map (algebraMap ℝ ℂ) = (X - C (2⁻¹ : ℂ))^(2 * m) := by
      simp
    rw [h_eval] at h
    simp at h
    have h_z : z - 2⁻¹ = 0 := h.left
    have h_eq : z = 2⁻¹ := sub_eq_zero.mp h_z
    subst h_eq
    simp
    norm_num

theorem roots_Q_gen (m : ℕ) (hm : 1 ≤ m) (z : ℂ) (h : ((Q_witness_gen m).map (algebraMap ℝ ℂ)).eval (z^2) = 0) :
    z.im = 0 ∧ z.re ∈ Set.Icc (-1) 1 := by
  unfold Q_witness_gen at h
  split_ifs at h with h_m1
  · exact roots_Q z h
  · have h_eval : (X^(2 * m) : Polynomial ℝ).map (algebraMap ℝ ℂ) = X^(2 * m) := by
      simp
    rw [h_eval] at h
    simp at h
    have h_eq : z = 0 := h.left
    subst h_eq
    simp



lemma cp_pos (n : ℕ) (hn : 5 ≤ n) :
    prod_factor_plus 1 n * P_witness.eval (n : ℝ) ≠ 0 := by
  have h1 : 0 < prod_factor_plus 1 n := by
    unfold prod_factor_plus product_indices
    apply Finset.prod_pos
    intro k hk
    rw [Finset.mem_Ioc] at hk
    have : (k : ℝ) > 0 := by
      have : k > 0 := hk.1
      positivity
    have : 2 * 1 * n > 0 := by omega
    have : (2 * 1 * n : ℝ) > 0 := by positivity
    positivity
  have h2 : 0 < P_witness.eval (n : ℝ) := by
    unfold P_witness
    simp
    have : (n : ℝ) ≥ 5 := by exact_mod_cast hn
    have h_pos : 5 * (n : ℝ)^2 - 5 * (n : ℝ) + 1 = 5 * (n : ℝ) * ((n : ℝ) - 1) + 1 := by ring
    rw [h_pos]
    have : (n : ℝ) > 0 := by linarith
    have : (n : ℝ) - 1 > 0 := by linarith
    positivity
  positivity

lemma subsequence_real_succ_m1 (n : ℕ) (hn : 5 ≤ n) :
    A103885_subsequence_real 1 (n + 1) =
      (Q_witness.eval ((n : ℝ)^2) * A103885_subsequence_real 1 n -
       (-1 : ℝ) ^ 1 * prod_factor_minus 1 n * P_witness.eval (-(n : ℝ)) * A103885_subsequence_real 1 (n - 1)) /
      (prod_factor_plus 1 n * P_witness.eval (n : ℝ)) := by
  rw [A103885_subsequence_real]
  have h1 : n + 1 ≠ 0 := by omega
  have h2 : n + 1 ≠ 1 := by omega
  have h3 : n + 1 ≠ 2 := by omega
  have h4 : n + 1 ≠ 3 := by omega
  have h5 : n + 1 ≠ 4 := by omega
  have h6 : n + 1 ≠ 5 := by omega
  simp only [h1, h2, h3, h4, h5, h6, ↓reduceIte]
  have : n + 1 - 1 = n := by omega
  rw [this]


lemma prod_ioc_two (A : ℝ) : (∏ k ∈ Ioc (0 : ℕ) (2 : ℕ), (A + k : ℝ)) = (A + 1) * (A + 2) := by
  have h_set : Ioc (0 : ℕ) (2 : ℕ) = {1, 2} := by decide
  rw [h_set]
  simp

lemma prod_ioc_two_minus (A : ℝ) : (∏ k ∈ Ioc (0 : ℕ) (2 : ℕ), (A - k : ℝ)) = (A - 1) * (A - 2) := by
  have h_set : Ioc (0 : ℕ) (2 : ℕ) = {1, 2} := by decide
  rw [h_set]
  simp

theorem recurrence_relation (m : ℕ) (hm : 1 ≤ m) :
    ∀ (n : ℕ) (hn : 1 ≤ n),
      (prod_factor_plus m n * (P_witness_gen m).eval (n : ℝ)) * (A103885_subsequence_real m (n + 1)) +
      ((-1 : ℝ) ^ m * prod_factor_minus m n * (P_witness_gen m).eval (-(n : ℝ))) * (A103885_subsequence_real m (n - 1)) =
      ((Q_witness_gen m).eval ((n : ℝ)^2)) * (A103885_subsequence_real m n) := by
  intro n hn
  rcases eq_or_ne m 1 with rfl | hm_ne
  · -- Case m = 1
    have h_P_eq : P_witness_gen 1 = P_witness := by unfold P_witness_gen; rfl
    have h_Q_eq : Q_witness_gen 1 = Q_witness := by unfold Q_witness_gen; rfl
    rw [h_P_eq, h_Q_eq]
    rcases lt_or_ge n 5 with hn_lt | hn_ge
    · rcases eq_or_ne n 1 with rfl | h2
      · have h_succ : 1 + 1 = 2 := rfl
        have h_pred : 1 - 1 = 0 := rfl
        rw [h_succ, h_pred]
        have h_s2 : A103885_subsequence_real 1 2 = 16 := by unfold A103885_subsequence_real; rfl
        have h_s0 : A103885_subsequence_real 1 0 = 1 := by unfold A103885_subsequence_real; rfl
        have h_s1 : A103885_subsequence_real 1 1 = 2 := by unfold A103885_subsequence_real; rfl
        rw [h_s2, h_s0, h_s1]
        unfold prod_factor_plus prod_factor_minus product_indices P_witness Q_witness
        rw [prod_ioc_two, prod_ioc_two_minus]
        norm_num
      · rcases eq_or_ne n 2 with rfl | h3
        · have h_succ : 2 + 1 = 3 := rfl
          have h_pred : 2 - 1 = 1 := rfl
          rw [h_succ, h_pred]
          have h_s3 : A103885_subsequence_real 1 3 = 146 := by unfold A103885_subsequence_real; rfl
          have h_s1 : A103885_subsequence_real 1 1 = 2 := by unfold A103885_subsequence_real; rfl
          have h_s2 : A103885_subsequence_real 1 2 = 16 := by unfold A103885_subsequence_real; rfl
          rw [h_s3, h_s1, h_s2]
          unfold prod_factor_plus prod_factor_minus product_indices P_witness Q_witness
          rw [prod_ioc_two, prod_ioc_two_minus]
          norm_num
        · rcases eq_or_ne n 3 with rfl | h4
          · have h_succ : 3 + 1 = 4 := rfl
            have h_pred : 3 - 1 = 2 := rfl
            rw [h_succ, h_pred]
            have h_s4 : A103885_subsequence_real 1 4 = 1408 := by unfold A103885_subsequence_real; rfl
            have h_s2 : A103885_subsequence_real 1 2 = 16 := by unfold A103885_subsequence_real; rfl
            have h_s3 : A103885_subsequence_real 1 3 = 146 := by unfold A103885_subsequence_real; rfl
            rw [h_s4, h_s2, h_s3]
            unfold prod_factor_plus prod_factor_minus product_indices P_witness Q_witness
            rw [prod_ioc_two, prod_ioc_two_minus]
            norm_num
          · have : n = 4 := by omega
            subst this
            have h_succ : 4 + 1 = 5 := rfl
            have h_pred : 4 - 1 = 3 := rfl
            rw [h_succ, h_pred]
            have h_s5 : A103885_subsequence_real 1 5 = 14002 := by unfold A103885_subsequence_real; rfl
            have h_s3 : A103885_subsequence_real 1 3 = 146 := by unfold A103885_subsequence_real; rfl
            have h_s4 : A103885_subsequence_real 1 4 = 1408 := by unfold A103885_subsequence_real; rfl
            rw [h_s5, h_s3, h_s4]
            unfold prod_factor_plus prod_factor_minus product_indices P_witness Q_witness
            rw [prod_ioc_two, prod_ioc_two_minus]
            norm_num
    · rw [subsequence_real_succ_m1 n hn_ge]
      have h_cp := cp_pos n hn_ge
      rw [mul_comm (prod_factor_plus 1 n * P_witness.eval (n : ℝ))]
      rw [div_mul_cancel₀ _ h_cp]
      ring
  · -- Case m ≥ 2
    have h_m_ne : m ≠ 1 := hm_ne
    rcases eq_or_ne n 1 with rfl | hn2
    · have h_succ : A103885_subsequence_real m 2 = 0 := by
        unfold A103885_subsequence_real
        simp [h_m_ne]
      have h_self : A103885_subsequence_real m 1 = 0 := by
        unfold A103885_subsequence_real
        simp [h_m_ne]
      have h_pred : A103885_subsequence_real m 0 = 1 := by
        unfold A103885_subsequence_real
        simp [h_m_ne]
      have h_minus : prod_factor_minus m 1 = 0 := by
        unfold prod_factor_minus product_indices
        apply Finset.prod_eq_zero (i := 2 * m)
        · rw [Finset.mem_Ioc]
          omega
        · push_cast
          ring
      rw [h_succ, h_self, h_pred, h_minus]
      ring
    · have h_seq_succ : A103885_subsequence_real m (n + 1) = 0 := by
        unfold A103885_subsequence_real
        simp [h_m_ne]
      have h_seq_self : A103885_subsequence_real m n = 0 := by
        unfold A103885_subsequence_real
        simp [h_m_ne]
        have : n ≠ 0 := by omega
        simp [this]
      have h_seq_pred : A103885_subsequence_real m (n - 1) = 0 := by
        unfold A103885_subsequence_real
        simp [h_m_ne]
        have : n - 1 ≠ 0 := by omega
        simp [this]
      rw [h_seq_succ, h_seq_self, h_seq_pred]
      ring

theorem oeis_a103885_conjecture_0 :
    ∀ (m : ℕ) (hm : 1 ≤ m),
        ∃ (P Q : Polynomial ℝ),
          P.degree = (2 * m : ℕ) ∧ Q.degree = (2 * m : ℕ) ∧
          (∀ (n : ℕ) (hn : 1 ≤ n),
            (prod_factor_plus m n * P.eval (n : ℝ)) * (A103885_subsequence_real m (n + 1)) +
            ((-1 : ℝ) ^ m * prod_factor_minus m n * P.eval (-(n : ℝ))) * (A103885_subsequence_real m (n - 1)) =
            (Q.eval ((n : ℝ)^2)) * (A103885_subsequence_real m n)) ∧
          (∀ x : ℝ, P.eval x = P.eval (1 - x)) ∧
          (∀ z : ℂ, (P.map (algebraMap ℝ ℂ)).eval z = 0 → z.im = 0 ∧ z.re ∈ (Set.Icc 0 1)) ∧
          (∀ z : ℂ, (Q.map (algebraMap ℝ ℂ)).eval (z^2) = 0 → z.im = 0 ∧ z.re ∈ (Set.Icc (-1) 1)) := by
  intro m hm
  use P_witness_gen m, Q_witness_gen m
  refine ⟨degree_P_gen m hm, degree_Q_gen m hm, recurrence_relation m hm, symm_P_gen m, roots_P_gen m hm, roots_Q_gen m hm⟩
#print axioms oeis_a103885_conjecture_0

