import FormalConjectures.Util.ProblemImports
import Mathlib.Analysis.Complex.Polynomial.Basic

set_option maxRecDepth 200000
set_option maxHeartbeats 500000

open Nat Finset Polynomial
open scoped BigOperators ComplexConjugate

/--
A103885: $a(n) = [x^{2n}] \left(\frac{1 + x}{1 - x}\right)^n$.
The sequence is given by the combinatorial identity:
$$a(n) = \sum_{k = 0}^n \binom{n}{k} \binom{2n+k-1}{n-1}$$
with $a(0) = 1$.
-/
def A103885 (n : ℕ) : ℕ :=
  if n = 0 then 1
  else
    let r : ℕ := n - 1
    (range (n + 1)).sum (fun k => (n.choose k) * ((2 * n + k - 1).choose r))

-- The sequence b(n) = a(m*n) lifted to ℝ
noncomputable def A103885_subsequence_real (m n : ℕ) : ℝ :=
  (A103885 (m * n) : ℝ)

open BigOperators

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

def prod_factor_plus_nat (m n : ℕ) : ℕ :=
  (product_indices m).prod fun k => (2 * m * n + k)

theorem prod_factor_plus_eq_nat (m n : ℕ) :
    prod_factor_plus m n = (prod_factor_plus_nat m n : ℝ) := by
  dsimp [prod_factor_plus, prod_factor_plus_nat]
  push_cast
  rfl

def prod_factor_minus_nat (m n : ℕ) : ℕ :=
  (product_indices m).prod fun k => (2 * m * n - k)

theorem prod_factor_minus_eq_nat (m n : ℕ) (hn : 1 ≤ n) :
    prod_factor_minus m n = (prod_factor_minus_nat m n : ℝ) := by
  dsimp [prod_factor_minus, prod_factor_minus_nat]
  have h_le (k : ℕ) (hk : k ∈ product_indices m) : k ≤ 2 * m * n := by
    dsimp [product_indices] at hk
    rw [Finset.mem_Ioc] at hk
    have : k ≤ 2 * m := hk.2
    have : 2 * m ≤ 2 * m * n := by
      calc 2 * m = 2 * m * 1 := by ring
      _ ≤ 2 * m * n := Nat.mul_le_mul_left (2 * m) hn
    omega
  push_cast
  apply Finset.prod_congr rfl
  intro k hk
  have h_le_k := h_le k hk
  rw [Nat.cast_sub h_le_k]
  push_cast
  rfl


theorem prod_factor_minus_one_eq_zero (m : ℕ) (hm : 1 ≤ m) :
    prod_factor_minus m 1 = 0 := by
  dsimp [prod_factor_minus, product_indices]
  apply Finset.prod_eq_zero (i := 2 * m)
  · rw [Finset.mem_Ioc]
    constructor
    · omega
    · rfl
  · dsimp
    push_cast
    ring

theorem a_17_eq : A103885 17 = 26482855453375042 := by decide
theorem a_34_eq : A103885 34 = 10891851220333857991142430584176400 := by decide
theorem a_51_eq : A103885 51 = 5167034848034424838861818110038040096006601508898002 := by decide
theorem prod_factor_plus_17_1_eq : prod_factor_plus_nat 17 1 = 8400271075925222931453057050264530446863370603724800000000 := by decide
theorem prod_factor_plus_17_2_eq : prod_factor_plus_nat 17 2 = 387674553469832713100928742272490483261500306226956730368000000000 := by decide
theorem prod_factor_minus_17_2_eq : prod_factor_minus_nat 17 2 = 4200135537962611465726528525132265223431685301862400000000 := by decide

theorem prod_factor_plus_17_3_eq : prod_factor_plus_nat 17 3 = 38057679020621377079502785912570129414217262072160593461116928000000000 := by decide
theorem prod_factor_minus_17_3_eq : prod_factor_minus_nat 17 3 = 258449702313221808733952494848326988841000204151304486912000000000 := by decide
theorem a_68_eq : A103885 68 = 2599200093830976389575137274817233400171336491307633017336968343653760 := by decide

theorem prod_factor_plus_17_4_eq : prod_factor_plus_nat 17 4 = 198341912064044371782658384500745058286115444697322547288745390899200000000 := by decide
theorem prod_factor_minus_17_4_eq : prod_factor_minus_nat 17 4 = 28543259265466032809627089434427597060662946554120445095837696000000000 := by decide
theorem a_85_eq : A103885 85 = 1350222041062738218977395668323419357573796948752753111078654145647571081953058528909042 := by decide




lemma exists_root_of_signs' {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ} (hab : a ≤ b)
    (h1 : f a > 0) (h2 : f b < 0) : ∃ x ∈ Set.Icc a b, f x = 0 := by
  have h_subset : Set.Icc (f b) (f a) ⊆ f '' Set.Icc a b :=
    intermediate_value_Icc' hab hf.continuousOn
  have h_zero : (0 : ℝ) ∈ Set.Icc (f b) (f a) := ⟨by linarith, by linarith⟩
  have h_mem := h_subset h_zero
  rcases h_mem with ⟨x, hx_in, hx_eq⟩
  exact ⟨x, hx_in, hx_eq⟩

lemma exists_root_of_signs_neg {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ} (hab : a ≤ b)
    (h1 : f a < 0) (h2 : f b > 0) : ∃ x ∈ Set.Icc a b, f x = 0 := by
  have h_subset : Set.Icc (f a) (f b) ⊆ f '' Set.Icc a b :=
    intermediate_value_Icc hab hf.continuousOn
  have h_zero : (0 : ℝ) ∈ Set.Icc (f a) (f b) := ⟨by linarith, by linarith⟩
  have h_mem := h_subset h_zero
  rcases h_mem with ⟨x, hx_in, hx_eq⟩
  exact ⟨x, hx_in, hx_eq⟩

lemma no_roots_same_sign {f : ℝ → ℝ} (hf : Continuous f) {a : ℝ} (h_no_roots : ∀ x > a, f x ≠ 0)
    {b : ℝ} (hb : b > a) (hb_pos : f b > 0) {c : ℝ} (hc : c > a) : f c > 0 := by
  by_contra! h_le
  have h_ne : f c ≠ 0 := h_no_roots c hc
  have h_lt : f c < 0 := lt_of_le_of_ne h_le h_ne
  rcases lt_trichotomy b c with h_bc | rfl | h_cb
  · have ⟨y, hy_in, hy_zero⟩ := exists_root_of_signs' hf (le_of_lt h_bc) hb_pos h_lt
    have hy_gt : y > a := by linarith [hy_in.1]
    exact h_no_roots y hy_gt hy_zero
  · linarith [hb_pos, h_lt]
  · have ⟨y, hy_in, hy_zero⟩ := exists_root_of_signs_neg hf (le_of_lt h_cb) h_lt hb_pos
    have hy_gt : y > a := by linarith [hy_in.1]
    exact h_no_roots y hy_gt hy_zero


lemma sign_P0_of_P2_pos (P : Polynomial ℝ) (hsymm : ∀ x : ℝ, P.eval x = P.eval (1 - x))
    (h_ne_zero : ∀ x : ℝ, x < 0 ∨ 1 < x → P.eval x ≠ 0)
    (hP2 : P.eval 2 > 0) : P.eval 0 ≥ 0 := by
  by_contra! hP0
  have h_symm : P.eval (-1) = P.eval 2 := by
    have := hsymm (-1)
    ring_nf at this
    exact this
  have hP_minus_1 : P.eval (-1) > 0 := by rw [h_symm]; exact hP2
  have h_cont : Continuous (fun x => P.eval x) := P.continuous
  have ⟨y, hy_in, hy_zero⟩ := exists_root_of_signs' h_cont (by linarith : (-1 : ℝ) ≤ 0) hP_minus_1 hP0
  have hy_ne_zero : y ≠ 0 := by
    intro h_eq
    rw [h_eq] at hy_zero
    linarith
  have hy_lt_zero : y < 0 := by
    rcases hy_in with ⟨h_ge, h_le⟩
    exact lt_of_le_of_ne h_le hy_ne_zero
  have h_root_ne_zero := h_ne_zero y (Or.inl hy_lt_zero)
  exact h_root_ne_zero hy_zero

lemma sign_P3_of_P2_pos (P : Polynomial ℝ)
    (h_ne_zero : ∀ x : ℝ, x < 0 ∨ 1 < x → P.eval x ≠ 0)
    (hP2 : P.eval 2 > 0) : P.eval 3 > 0 := by
  by_contra! hP3
  have hP3_lt : P.eval 3 < 0 := lt_of_le_of_ne hP3 (h_ne_zero 3 (by norm_num))
  have h_cont : Continuous (fun x => P.eval x) := P.continuous
  have ⟨y, hy_in, hy_zero⟩ := exists_root_of_signs' h_cont (by linarith : (2 : ℝ) ≤ 3) hP2 hP3_lt
  have hy_gt_one : 1 < y := by
    rcases hy_in with ⟨h_ge, h_le⟩
    linarith
  have h_root_ne_zero := h_ne_zero y (Or.inr hy_gt_one)
  exact h_root_ne_zero hy_zero

lemma sign_Q1_of_Q4_pos (Q : Polynomial ℝ)
    (h_q_le_one : ∀ y : ℝ, y > 1 → Q.eval y ≠ 0)
    (hQ4 : Q.eval 4 > 0) : Q.eval 1 ≥ 0 := by
  by_contra! hQ1
  have h_cont : Continuous (fun y => - Q.eval y) := Q.continuous.neg
  have h1 : - Q.eval 1 > 0 := by linarith
  have h2 : - Q.eval 4 < 0 := by linarith
  have ⟨y, hy_in, hy_zero⟩ := exists_root_of_signs' h_cont (by linarith : (1 : ℝ) ≤ 4) h1 h2
  have hy_ne_one : y ≠ 1 := by
    intro h_eq
    rw [h_eq] at hy_zero
    simp at hy_zero
    linarith
  have hy_gt_one : y > 1 := by
    rcases hy_in with ⟨h_ge, h_le⟩
    exact lt_of_le_of_ne h_ge hy_ne_one.symm
  have h_root_ne_zero := h_q_le_one y hy_gt_one
  apply h_root_ne_zero
  simp at hy_zero
  exact hy_zero

lemma sign_Q9_of_Q4_pos (Q : Polynomial ℝ)
    (h_q_le_one : ∀ y : ℝ, y > 1 → Q.eval y ≠ 0)
    (hQ4 : Q.eval 4 > 0) : Q.eval 9 > 0 := by
  by_contra! hQ9
  have hQ9_lt : Q.eval 9 < 0 := lt_of_le_of_ne hQ9 (h_q_le_one 9 (by norm_num))
  have h_cont : Continuous (fun y => Q.eval y) := Q.continuous
  have ⟨y, hy_in, hy_zero⟩ := exists_root_of_signs' h_cont (by linarith : (4 : ℝ) ≤ 9) hQ4 hQ9_lt
  have hy_gt_one : y > 1 := by
    rcases hy_in with ⟨h_ge, h_le⟩
    linarith
  have h_root_ne_zero := h_q_le_one y hy_gt_one
  exact h_root_ne_zero hy_zero


lemma complex_poly_roots_ge_of_degree (n : ℕ) :
    ∀ (P : Polynomial ℂ) (hdeg : P.natDegree = n)
      (hroots : ∀ z : ℂ, eval z P = 0 → z.im = 0 ∧ z.re ∈ Set.Icc 0 1)
      (hP4 : (eval 4 P).re > 0),
      (eval 3 P).re ≥ (2 / 3) ^ P.natDegree * (eval 4 P).re := by
  induction' n with n ih
  · intro P hdeg _ _
    have hp0 : P.natDegree = 0 := hdeg
    have h_eq : P = C (coeff P 0) := eq_C_of_natDegree_eq_zero hp0
    rw [h_eq]
    simp
  · intro P hdeg hroots hP4
    have hp_pos : P.degree ≠ 0 := by
      intro h_zero
      have h_nat : P.natDegree = 0 := natDegree_eq_zero_iff_degree_le_zero.mpr (le_of_eq h_zero)
      omega
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_root P hp_pos
    have h_root_P : eval z P = 0 := hz
    have h_z_prop := hroots z h_root_P
    have h_z_im : z.im = 0 := h_z_prop.1
    have h_z_re : z.re ∈ Set.Icc 0 1 := h_z_prop.2
    have h_eq_z : z = (z.re : ℂ) := by
      apply Complex.ext
      · rfl
      · exact h_z_im
    -- P = (X - C z) * Q
    have h_div : X - C z ∣ P := dvd_iff_isRoot.mpr hz
    obtain ⟨Q, hQ⟩ := h_div
    have hQ_ne : Q ≠ 0 := by
      intro h_zero
      rw [h_zero, mul_zero] at hQ
      rw [hQ] at hdeg
      simp only [natDegree_zero] at hdeg
      omega
    have h_X_cz_ne : X - C z ≠ 0 := by
      intro h_zero
      have h_deg : (X - C z).natDegree = 1 := natDegree_X_sub_C z
      rw [h_zero] at h_deg
      simp only [natDegree_zero] at h_deg
      omega
    have h_nat_mul : P.natDegree = (X - C z).natDegree + Q.natDegree := by
      rw [hQ]
      exact natDegree_mul h_X_cz_ne hQ_ne
    have h_deg_Q : Q.natDegree = n := by
      rw [natDegree_X_sub_C] at h_nat_mul
      omega
    have hroots_Q : ∀ w : ℂ, eval w Q = 0 → w.im = 0 ∧ w.re ∈ Set.Icc 0 1 := by
      intro w hw
      have h_eval : eval w P = 0 := by
        rw [hQ]
        simp only [eval_mul, hw, mul_zero]
      exact hroots w h_eval
    have h_eval4_X_cz : eval 4 (X - C z) = 4 - z := by simp only [eval_sub, eval_X, eval_C]
    have h_eval3_X_cz : eval 3 (X - C z) = 3 - z := by simp only [eval_sub, eval_X, eval_C]
    have h_factor4_pos : 4 - z.re > 0 := by
      rcases h_z_re with ⟨h1, h2⟩
      linarith
    have h_factor3_pos : 3 - z.re > 0 := by
      rcases h_z_re with ⟨h1, h2⟩
      linarith
    have h_eval4_P : eval 4 P = eval 4 (X - C z) * eval 4 Q := by rw [hQ, eval_mul]
    have h_eval4_P_re : (eval 4 P).re = (4 - z.re) * (eval 4 Q).re := by
      rw [h_eval4_P, h_eval4_X_cz, h_eq_z]
      simp [Complex.mul_re]
    have hQ4 : (eval 4 Q).re > 0 := by
      have : (eval 4 P).re > 0 := hP4
      rw [h_eval4_P_re] at this
      exact pos_of_mul_pos_right this (by linarith)
    have ih_Q := ih Q h_deg_Q hroots_Q hQ4
    have h_eval3_P : eval 3 P = eval 3 (X - C z) * eval 3 Q := by rw [hQ, eval_mul]
    have h_eval3_P_re : (eval 3 P).re = (3 - z.re) * (eval 3 Q).re := by
      rw [h_eval3_P, h_eval3_X_cz, h_eq_z]
      simp [Complex.mul_re]
    have h_mul_le : (3 - z.re) * ((2 / 3) ^ Q.natDegree * (eval 4 Q).re) ≤ (3 - z.re) * (eval 3 Q).re := by
      have h_factor3_nonneg : 3 - z.re ≥ 0 := by linarith
      nlinarith
    have h_ineq_z : (2 / 3) * (4 - z.re) ≤ 3 - z.re := by
      rcases h_z_re with ⟨h1, h2⟩
      linarith
    have h_factor_le : ((2 / 3) * (4 - z.re)) * ((2 / 3) ^ Q.natDegree * (eval 4 Q).re) ≤ (3 - z.re) * ((2 / 3) ^ Q.natDegree * (eval 4 Q).re) := by
      have h_nonneg : (2 / 3) ^ Q.natDegree * (eval 4 Q).re ≥ 0 := by
        have h_pow : (2 / 3 : ℝ) ^ Q.natDegree ≥ 0 := by positivity
        have hQ4_ge : (eval 4 Q).re ≥ 0 := by linarith
        positivity
      nlinarith
    have h_trans : ((2 / 3) * (4 - z.re)) * ((2 / 3) ^ Q.natDegree * (eval 4 Q).re) ≤ (eval 3 P).re := by
      rw [h_eval3_P_re]
      linarith
    have h_simpl : ((2 / 3) * (4 - z.re)) * ((2 / 3) ^ Q.natDegree * (eval 4 Q).re) = (2 / 3) ^ P.natDegree * (eval 4 P).re := by
      rw [hdeg]
      rw [h_eval4_P_re]
      rw [h_deg_Q]
      ring
    rw [h_simpl] at h_trans
    exact h_trans

lemma real_poly_roots_ge (P : Polynomial ℝ)
    (hroots : ∀ z : ℂ, (P.map (algebraMap ℝ ℂ)).eval z = 0 → z.im = 0 ∧ z.re ∈ Set.Icc 0 1)
    (hP4 : P.eval 4 > 0) :
    P.eval 3 ≥ (2 / 3) ^ P.natDegree * P.eval 4 := by
  have h_comp : (P.map (algebraMap ℝ ℂ)).natDegree = P.natDegree := natDegree_map (algebraMap ℝ ℂ)
  have hP4_re : (eval 4 (P.map (algebraMap ℝ ℂ))).re > 0 := by
    have h_eval_map : (P.map (algebraMap ℝ ℂ)).eval (algebraMap ℝ ℂ 4) = algebraMap ℝ ℂ (P.eval 4) := Polynomial.eval_map_apply (algebraMap ℝ ℂ) 4
    have h_four : algebraMap ℝ ℂ 4 = 4 := rfl
    rw [← h_four, h_eval_map]
    simp [hP4]
  have h_res := complex_poly_roots_ge_of_degree (P.map (algebraMap ℝ ℂ)).natDegree (P.map (algebraMap ℝ ℂ)) rfl hroots hP4_re
  rw [h_comp] at h_res
  have h_eval_map_3 : (P.map (algebraMap ℝ ℂ)).eval (algebraMap ℝ ℂ 3) = algebraMap ℝ ℂ (P.eval 3) := Polynomial.eval_map_apply (algebraMap ℝ ℂ) 3
  have h_eval_map_4 : (P.map (algebraMap ℝ ℂ)).eval (algebraMap ℝ ℂ 4) = algebraMap ℝ ℂ (P.eval 4) := Polynomial.eval_map_apply (algebraMap ℝ ℂ) 4
  have h_three : algebraMap ℝ ℂ 3 = 3 := rfl
  have h_four : algebraMap ℝ ℂ 4 = 4 := rfl
  rw [← h_three, h_eval_map_3] at h_res
  rw [← h_four, h_eval_map_4] at h_res
  simp at h_res
  exact h_res

lemma complex_poly_roots_eval_2_ge_zero (n : ℕ) :
    ∀ (P : Polynomial ℂ) (hdeg : P.natDegree = n)
      (hroots : ∀ z : ℂ, eval z P = 0 → z.im = 0 ∧ z.re ∈ Set.Icc 0 1)
      (hP3 : (eval 3 P).re > 0),
      (eval 2 P).re ≥ 0 := by
  induction' n with n ih
  · intro P hdeg _ hP3
    have hp0 : P.natDegree = 0 := hdeg
    have h_eq : P = C (coeff P 0) := eq_C_of_natDegree_eq_zero hp0
    rw [h_eq] at hP3 ⊢
    simp at hP3 ⊢
    linarith
  · intro P hdeg hroots hP3
    have hp_pos : P.degree ≠ 0 := by
      intro h_zero
      have h_nat : P.natDegree = 0 := natDegree_eq_zero_iff_degree_le_zero.mpr (le_of_eq h_zero)
      omega
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_root P hp_pos
    have h_root_P : eval z P = 0 := hz
    have h_z_prop := hroots z h_root_P
    have h_z_im : z.im = 0 := h_z_prop.1
    have h_z_re : z.re ∈ Set.Icc 0 1 := h_z_prop.2
    have h_eq_z : z = (z.re : ℂ) := by
      apply Complex.ext
      · rfl
      · exact h_z_im
    have h_div : X - C z ∣ P := dvd_iff_isRoot.mpr hz
    obtain ⟨Q, hQ⟩ := h_div
    have hQ_ne : Q ≠ 0 := by
      intro h_zero
      rw [h_zero, mul_zero] at hQ
      rw [hQ] at hdeg
      simp only [natDegree_zero] at hdeg
      omega
    have h_X_cz_ne : X - C z ≠ 0 := by
      intro h_zero
      have h_deg : (X - C z).natDegree = 1 := natDegree_X_sub_C z
      rw [h_zero] at h_deg
      simp only [natDegree_zero] at h_deg
      omega
    have h_nat_mul : P.natDegree = (X - C z).natDegree + Q.natDegree := by
      rw [hQ]
      exact natDegree_mul h_X_cz_ne hQ_ne
    have h_deg_Q : Q.natDegree = n := by
      rw [natDegree_X_sub_C] at h_nat_mul
      omega
    have hroots_Q : ∀ w : ℂ, eval w Q = 0 → w.im = 0 ∧ w.re ∈ Set.Icc 0 1 := by
      intro w hw
      have h_eval : eval w P = 0 := by
        rw [hQ]
        simp only [eval_mul, hw, mul_zero]
      exact hroots w h_eval
    have h_eval3_X_cz : eval 3 (X - C z) = 3 - z := by simp only [eval_sub, eval_X, eval_C]
    have h_eval2_X_cz : eval 2 (X - C z) = 2 - z := by simp only [eval_sub, eval_X, eval_C]
    have h_factor3_pos : 3 - z.re > 0 := by
      rcases h_z_re with ⟨h1, h2⟩
      linarith
    have h_factor2_pos : 2 - z.re > 0 := by
      rcases h_z_re with ⟨h1, h2⟩
      linarith
    have h_eval3_P : eval 3 P = eval 3 (X - C z) * eval 3 Q := by rw [hQ, eval_mul]
    have h_eval3_P_re : (eval 3 P).re = (3 - z.re) * (eval 3 Q).re := by
      rw [h_eval3_P, h_eval3_X_cz, h_eq_z]
      simp [Complex.mul_re]
    have hQ3 : (eval 3 Q).re > 0 := by
      have : (eval 3 P).re > 0 := hP3
      rw [h_eval3_P_re] at this
      exact pos_of_mul_pos_right this (by linarith)
    have ih_Q := ih Q h_deg_Q hroots_Q hQ3
    have h_eval2_P : eval 2 P = eval 2 (X - C z) * eval 2 Q := by rw [hQ, eval_mul]
    have h_eval2_P_re : (eval 2 P).re = (2 - z.re) * (eval 2 Q).re := by
      rw [h_eval2_P, h_eval2_X_cz, h_eq_z]
      simp [Complex.mul_re]
    rw [h_eval2_P_re]
    nlinarith

lemma complex_poly_roots_ge_2_3 (n : ℕ) :
    ∀ (P : Polynomial ℂ) (hdeg : P.natDegree = n)
      (hroots : ∀ z : ℂ, eval z P = 0 → z.im = 0 ∧ z.re ∈ Set.Icc 0 1)
      (hP3 : (eval 3 P).re > 0),
      (eval 3 P).re ≥ (2 / 3) ^ P.natDegree * (eval 2 P).re := by
  induction' n with n ih
  · intro P hdeg _ _
    have hp0 : P.natDegree = 0 := hdeg
    have h_eq : P = C (coeff P 0) := eq_C_of_natDegree_eq_zero hp0
    rw [h_eq]
    simp
  · intro P hdeg hroots hP3
    have hp_pos : P.degree ≠ 0 := by
      intro h_zero
      have h_nat : P.natDegree = 0 := natDegree_eq_zero_iff_degree_le_zero.mpr (le_of_eq h_zero)
      omega
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_root P hp_pos
    have h_root_P : eval z P = 0 := hz
    have h_z_prop := hroots z h_root_P
    have h_z_im : z.im = 0 := h_z_prop.1
    have h_z_re : z.re ∈ Set.Icc 0 1 := h_z_prop.2
    have h_eq_z : z = (z.re : ℂ) := by
      apply Complex.ext
      · rfl
      · exact h_z_im
    have h_div : X - C z ∣ P := dvd_iff_isRoot.mpr hz
    obtain ⟨Q, hQ⟩ := h_div
    have hQ_ne : Q ≠ 0 := by
      intro h_zero
      rw [h_zero, mul_zero] at hQ
      rw [hQ] at hdeg
      simp only [natDegree_zero] at hdeg
      omega
    have h_X_cz_ne : X - C z ≠ 0 := by
      intro h_zero
      have h_deg : (X - C z).natDegree = 1 := natDegree_X_sub_C z
      rw [h_zero] at h_deg
      simp only [natDegree_zero] at h_deg
      omega
    have h_nat_mul : P.natDegree = (X - C z).natDegree + Q.natDegree := by
      rw [hQ]
      exact natDegree_mul h_X_cz_ne hQ_ne
    have h_deg_Q : Q.natDegree = n := by
      rw [natDegree_X_sub_C] at h_nat_mul
      omega
    have hroots_Q : ∀ w : ℂ, eval w Q = 0 → w.im = 0 ∧ w.re ∈ Set.Icc 0 1 := by
      intro w hw
      have h_eval : eval w P = 0 := by
        rw [hQ]
        simp only [eval_mul, hw, mul_zero]
      exact hroots w h_eval
    have h_eval3_X_cz : eval 3 (X - C z) = 3 - z := by simp only [eval_sub, eval_X, eval_C]
    have h_eval2_X_cz : eval 2 (X - C z) = 2 - z := by simp only [eval_sub, eval_X, eval_C]
    have h_factor3_pos : 3 - z.re > 0 := by
      rcases h_z_re with ⟨h1, h2⟩
      linarith
    have h_factor2_pos : 2 - z.re > 0 := by
      rcases h_z_re with ⟨h1, h2⟩
      linarith
    have h_eval3_P : eval 3 P = eval 3 (X - C z) * eval 3 Q := by rw [hQ, eval_mul]
    have h_eval3_P_re : (eval 3 P).re = (3 - z.re) * (eval 3 Q).re := by
      rw [h_eval3_P, h_eval3_X_cz, h_eq_z]
      simp [Complex.mul_re]
    have hQ3 : (eval 3 Q).re > 0 := by
      have : (eval 3 P).re > 0 := hP3
      rw [h_eval3_P_re] at this
      exact pos_of_mul_pos_right this (by linarith)
    have ih_Q := ih Q h_deg_Q hroots_Q hQ3
    have h_eval2_P : eval 2 P = eval 2 (X - C z) * eval 2 Q := by rw [hQ, eval_mul]
    have h_eval2_P_re : (eval 2 P).re = (2 - z.re) * (eval 2 Q).re := by
      rw [h_eval2_P, h_eval2_X_cz, h_eq_z]
      simp [Complex.mul_re]
    have h_mul_le : (3 - z.re) * ((2 / 3) ^ Q.natDegree * (eval 2 Q).re) ≤ (3 - z.re) * (eval 3 Q).re := by
      have h_factor3_nonneg : 3 - z.re ≥ 0 := by linarith
      nlinarith
    have h_ineq_z : (2 / 3) * (2 - z.re) ≤ 3 - z.re := by
      rcases h_z_re with ⟨h1, h2⟩
      linarith
    have h_factor_le : ((2 / 3) * (2 - z.re)) * ((2 / 3) ^ Q.natDegree * (eval 2 Q).re) ≤ (3 - z.re) * ((2 / 3) ^ Q.natDegree * (eval 2 Q).re) := by
      have h_nonneg : (2 / 3 : ℝ) ^ Q.natDegree * (eval 2 Q).re ≥ 0 := by
        have h_pow : (2 / 3 : ℝ) ^ Q.natDegree ≥ 0 := by positivity
        have hQ2_ge : (eval 2 Q).re ≥ 0 := complex_poly_roots_eval_2_ge_zero Q.natDegree Q rfl hroots_Q hQ3
        positivity
      nlinarith
    have h_trans : ((2 / 3) * (2 - z.re)) * ((2 / 3) ^ Q.natDegree * (eval 2 Q).re) ≤ (eval 3 P).re := by
      rw [h_eval3_P_re]
      linarith
    have h_simpl : ((2 / 3) * (2 - z.re)) * ((2 / 3) ^ Q.natDegree * (eval 2 Q).re) = (2 / 3) ^ P.natDegree * (eval 2 P).re := by
      rw [hdeg]
      rw [h_eval2_P_re]
      rw [h_deg_Q]
      ring
    rw [h_simpl] at h_trans
    exact h_trans

lemma real_poly_roots_ge_2_3 (P : Polynomial ℝ)
    (hroots : ∀ z : ℂ, (P.map (algebraMap ℝ ℂ)).eval z = 0 → z.im = 0 ∧ z.re ∈ Set.Icc 0 1)
    (hP3 : P.eval 3 > 0) :
    P.eval 3 ≥ (2 / 3) ^ P.natDegree * P.eval 2 := by
  have h_comp : (P.map (algebraMap ℝ ℂ)).natDegree = P.natDegree := natDegree_map (algebraMap ℝ ℂ)
  have hP3_re : (eval 3 (P.map (algebraMap ℝ ℂ))).re > 0 := by
    have h_eval_map : (P.map (algebraMap ℝ ℂ)).eval (algebraMap ℝ ℂ 3) = algebraMap ℝ ℂ (P.eval 3) := Polynomial.eval_map_apply (algebraMap ℝ ℂ) 3
    have h_three : algebraMap ℝ ℂ 3 = 3 := rfl
    rw [← h_three, h_eval_map]
    simp [hP3]
  have h_res := complex_poly_roots_ge_2_3 (P.map (algebraMap ℝ ℂ)).natDegree (P.map (algebraMap ℝ ℂ)) rfl hroots hP3_re
  rw [h_comp] at h_res
  have h_eval_map_2 : (P.map (algebraMap ℝ ℂ)).eval (algebraMap ℝ ℂ 2) = algebraMap ℝ ℂ (P.eval 2) := Polynomial.eval_map_apply (algebraMap ℝ ℂ) 2
  have h_eval_map_3 : (P.map (algebraMap ℝ ℂ)).eval (algebraMap ℝ ℂ 3) = algebraMap ℝ ℂ (P.eval 3) := Polynomial.eval_map_apply (algebraMap ℝ ℂ) 3
  have h_two : algebraMap ℝ ℂ 2 = 2 := rfl
  have h_three : algebraMap ℝ ℂ 3 = 3 := rfl
  rw [← h_two, h_eval_map_2] at h_res
  rw [← h_three, h_eval_map_3] at h_res
  simp at h_res
  exact h_res

lemma complex_poly_roots_ge_2_3_half (n : ℕ) :
    ∀ (P : Polynomial ℂ) (hdeg : P.natDegree = n)
      (hroots : ∀ z : ℂ, eval z P = 0 → z.im = 0 ∧ z.re ∈ Set.Icc 0 1)
      (hP3 : (eval 3 P).re > 0),
      (eval 2 P).re ≥ (1 / 2) ^ P.natDegree * (eval 3 P).re := by
  induction' n with n ih
  · intro P hdeg _ _
    have hp0 : P.natDegree = 0 := hdeg
    have h_eq : P = C (coeff P 0) := eq_C_of_natDegree_eq_zero hp0
    rw [h_eq]
    simp
  · intro P hdeg hroots hP3
    have hp_pos : P.degree ≠ 0 := by
      intro h_zero
      have h_nat : P.natDegree = 0 := natDegree_eq_zero_iff_degree_le_zero.mpr (le_of_eq h_zero)
      omega
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_root P hp_pos
    have h_root_P : eval z P = 0 := hz
    have h_z_prop := hroots z h_root_P
    have h_z_im : z.im = 0 := h_z_prop.1
    have h_z_re : z.re ∈ Set.Icc 0 1 := h_z_prop.2
    have h_eq_z : z = (z.re : ℂ) := by
      apply Complex.ext
      · rfl
      · exact h_z_im
    have h_div : X - C z ∣ P := dvd_iff_isRoot.mpr hz
    obtain ⟨Q, hQ⟩ := h_div
    have hQ_ne : Q ≠ 0 := by
      intro h_zero
      rw [h_zero, mul_zero] at hQ
      rw [hQ] at hdeg
      simp only [natDegree_zero] at hdeg
      omega
    have h_X_cz_ne : X - C z ≠ 0 := by
      intro h_zero
      have h_deg : (X - C z).natDegree = 1 := natDegree_X_sub_C z
      rw [h_zero] at h_deg
      simp only [natDegree_zero] at h_deg
      omega
    have h_nat_mul : P.natDegree = (X - C z).natDegree + Q.natDegree := by
      rw [hQ]
      exact natDegree_mul h_X_cz_ne hQ_ne
    have h_deg_Q : Q.natDegree = n := by
      rw [natDegree_X_sub_C] at h_nat_mul
      omega
    have hroots_Q : ∀ w : ℂ, eval w Q = 0 → w.im = 0 ∧ w.re ∈ Set.Icc 0 1 := by
      intro w hw
      have h_eval : eval w P = 0 := by
        rw [hQ]
        simp only [eval_mul, hw, mul_zero]
      exact hroots w h_eval
    have h_eval3_X_cz : eval 3 (X - C z) = 3 - z := by simp only [eval_sub, eval_X, eval_C]
    have h_eval2_X_cz : eval 2 (X - C z) = 2 - z := by simp only [eval_sub, eval_X, eval_C]
    have h_factor3_pos : 3 - z.re > 0 := by
      rcases h_z_re with ⟨h1, h2⟩
      linarith
    have h_factor2_pos : 2 - z.re > 0 := by
      rcases h_z_re with ⟨h1, h2⟩
      linarith
    have h_eval3_P : eval 3 P = eval 3 (X - C z) * eval 3 Q := by rw [hQ, eval_mul]
    have h_eval3_P_re : (eval 3 P).re = (3 - z.re) * (eval 3 Q).re := by
      rw [h_eval3_P, h_eval3_X_cz, h_eq_z]
      simp [Complex.mul_re]
    have hQ3 : (eval 3 Q).re > 0 := by
      have : (eval 3 P).re > 0 := hP3
      rw [h_eval3_P_re] at this
      exact pos_of_mul_pos_right this (by linarith)
    have ih_Q := ih Q h_deg_Q hroots_Q hQ3
    have h_eval2_P : eval 2 P = eval 2 (X - C z) * eval 2 Q := by rw [hQ, eval_mul]
    have h_eval2_P_re : (eval 2 P).re = (2 - z.re) * (eval 2 Q).re := by
      rw [h_eval2_P, h_eval2_X_cz, h_eq_z]
      simp [Complex.mul_re]
    have h_mul_le : (2 - z.re) * ((1 / 2) ^ Q.natDegree * (eval 3 Q).re) ≤ (2 - z.re) * (eval 2 Q).re := by
      have h_factor2_nonneg : 2 - z.re ≥ 0 := by linarith
      nlinarith
    have h_ineq_z : (1 / 2) * (3 - z.re) ≤ 2 - z.re := by
      rcases h_z_re with ⟨h1, h2⟩
      linarith
    have h_factor_le : ((1 / 2) * (3 - z.re)) * ((1 / 2) ^ Q.natDegree * (eval 3 Q).re) ≤ (2 - z.re) * ((1 / 2) ^ Q.natDegree * (eval 3 Q).re) := by
      have h_nonneg : (1 / 2 : ℝ) ^ Q.natDegree * (eval 3 Q).re ≥ 0 := by
        have h_pow : (1 / 2 : ℝ) ^ Q.natDegree ≥ 0 := by positivity
        have hQ3_ge : (eval 3 Q).re ≥ 0 := by linarith
        positivity
      nlinarith
    have h_trans : ((1 / 2) * (3 - z.re)) * ((1 / 2) ^ Q.natDegree * (eval 3 Q).re) ≤ (eval 2 P).re := by
      rw [h_eval2_P_re]
      linarith
    have h_simpl : ((1 / 2) * (3 - z.re)) * ((1 / 2) ^ Q.natDegree * (eval 3 Q).re) = (1 / 2) ^ P.natDegree * (eval 3 P).re := by
      rw [hdeg]
      rw [h_eval3_P_re]
      rw [h_deg_Q]
      ring
    rw [h_simpl] at h_trans
    exact h_trans

lemma real_poly_roots_ge_2_3_half (P : Polynomial ℝ)
    (hroots : ∀ z : ℂ, (P.map (algebraMap ℝ ℂ)).eval z = 0 → z.im = 0 ∧ z.re ∈ Set.Icc 0 1)
    (hP3 : P.eval 3 > 0) :
    P.eval 2 ≥ (1 / 2) ^ P.natDegree * P.eval 3 := by
  have h_comp : (P.map (algebraMap ℝ ℂ)).natDegree = P.natDegree := natDegree_map (algebraMap ℝ ℂ)
  have hP3_re : (eval 3 (P.map (algebraMap ℝ ℂ))).re > 0 := by
    have h_eval_map : (P.map (algebraMap ℝ ℂ)).eval (algebraMap ℝ ℂ 3) = algebraMap ℝ ℂ (P.eval 3) := Polynomial.eval_map_apply (algebraMap ℝ ℂ) 3
    have h_three : algebraMap ℝ ℂ 3 = 3 := rfl
    rw [← h_three, h_eval_map]
    simp [hP3]
  have h_res := complex_poly_roots_ge_2_3_half (P.map (algebraMap ℝ ℂ)).natDegree (P.map (algebraMap ℝ ℂ)) rfl hroots hP3_re
  rw [h_comp] at h_res
  have h_eval_map_2 : (P.map (algebraMap ℝ ℂ)).eval (algebraMap ℝ ℂ 2) = algebraMap ℝ ℂ (P.eval 2) := Polynomial.eval_map_apply (algebraMap ℝ ℂ) 2
  have h_eval_map_3 : (P.map (algebraMap ℝ ℂ)).eval (algebraMap ℝ ℂ 3) = algebraMap ℝ ℂ (P.eval 3) := Polynomial.eval_map_apply (algebraMap ℝ ℂ) 3
  have h_two : algebraMap ℝ ℂ 2 = 2 := rfl
  have h_three : algebraMap ℝ ℂ 3 = 3 := rfl
  rw [← h_two, h_eval_map_2] at h_res
  rw [← h_three, h_eval_map_3] at h_res
  simp at h_res ⊢
  exact h_res



lemma complex_poly_roots_le_3_4 (n : ℕ) :
    ∀ (P : Polynomial ℂ) (hdeg : P.natDegree = n)
      (hroots : ∀ z : ℂ, eval z P = 0 → z.im = 0 ∧ z.re ∈ Set.Icc 0 1)
      (hP4 : (eval 4 P).re > 0),
      (eval 3 P).re ≤ (3 / 4) ^ P.natDegree * (eval 4 P).re := by
  induction' n with n ih
  · intro P hdeg _ _
    have hp0 : P.natDegree = 0 := hdeg
    have h_eq : P = C (coeff P 0) := eq_C_of_natDegree_eq_zero hp0
    rw [h_eq]
    simp
  · intro P hdeg hroots hP4
    have hp_pos : P.degree ≠ 0 := by
      intro h_zero
      have h_nat : P.natDegree = 0 := natDegree_eq_zero_iff_degree_le_zero.mpr (le_of_eq h_zero)
      omega
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_root P hp_pos
    have h_root_P : eval z P = 0 := hz
    have h_z_prop := hroots z h_root_P
    have h_z_im : z.im = 0 := h_z_prop.1
    have h_z_re : z.re ∈ Set.Icc 0 1 := h_z_prop.2
    have h_eq_z : z = (z.re : ℂ) := by
      apply Complex.ext
      · rfl
      · exact h_z_im
    have h_div : X - C z ∣ P := dvd_iff_isRoot.mpr hz
    obtain ⟨Q, hQ⟩ := h_div
    have hQ_ne : Q ≠ 0 := by
      intro h_zero
      rw [h_zero, mul_zero] at hQ
      rw [hQ] at hdeg
      simp only [natDegree_zero] at hdeg
      omega
    have h_X_cz_ne : X - C z ≠ 0 := by
      intro h_zero
      have h_deg : (X - C z).natDegree = 1 := natDegree_X_sub_C z
      rw [h_zero] at h_deg
      simp only [natDegree_zero] at h_deg
      omega
    have h_nat_mul : P.natDegree = (X - C z).natDegree + Q.natDegree := by
      rw [hQ]
      exact natDegree_mul h_X_cz_ne hQ_ne
    have h_deg_Q : Q.natDegree = n := by
      rw [natDegree_X_sub_C] at h_nat_mul
      omega
    have hroots_Q : ∀ w : ℂ, eval w Q = 0 → w.im = 0 ∧ w.re ∈ Set.Icc 0 1 := by
      intro w hw
      have h_eval : eval w P = 0 := by
        rw [hQ]
        simp only [eval_mul, hw, mul_zero]
      exact hroots w h_eval
    have h_eval4_X_cz : eval 4 (X - C z) = 4 - z := by simp only [eval_sub, eval_X, eval_C]
    have h_eval3_X_cz : eval 3 (X - C z) = 3 - z := by simp only [eval_sub, eval_X, eval_C]
    have h_factor4_pos : 4 - z.re > 0 := by
      rcases h_z_re with ⟨h1, h2⟩
      linarith
    have h_factor3_pos : 3 - z.re > 0 := by
      rcases h_z_re with ⟨h1, h2⟩
      linarith
    have h_eval4_P : eval 4 P = eval 4 (X - C z) * eval 4 Q := by rw [hQ, eval_mul]
    have h_eval4_P_re : (eval 4 P).re = (4 - z.re) * (eval 4 Q).re := by
      rw [h_eval4_P, h_eval4_X_cz, h_eq_z]
      simp [Complex.mul_re]
    have hQ4 : (eval 4 Q).re > 0 := by
      have : (eval 4 P).re > 0 := hP4
      rw [h_eval4_P_re] at this
      exact pos_of_mul_pos_right this (by linarith)
    have ih_Q := ih Q h_deg_Q hroots_Q hQ4
    have h_eval3_P : eval 3 P = eval 3 (X - C z) * eval 3 Q := by rw [hQ, eval_mul]
    have h_eval3_P_re : (eval 3 P).re = (3 - z.re) * (eval 3 Q).re := by
      rw [h_eval3_P, h_eval3_X_cz, h_eq_z]
      simp [Complex.mul_re]
    have h_mul_le : (3 - z.re) * (eval 3 Q).re ≤ (3 - z.re) * ((3 / 4) ^ Q.natDegree * (eval 4 Q).re) := by
      have h_factor3_nonneg : 3 - z.re ≥ 0 := by linarith
      nlinarith
    have h_ineq_z : 3 - z.re ≤ (3 / 4) * (4 - z.re) := by
      rcases h_z_re with ⟨h1, h2⟩
      linarith
    have h_factor_le : (3 - z.re) * ((3 / 4) ^ Q.natDegree * (eval 4 Q).re) ≤ ((3 / 4) * (4 - z.re)) * ((3 / 4) ^ Q.natDegree * (eval 4 Q).re) := by
      have h_nonneg : (3 / 4 : ℝ) ^ Q.natDegree * (eval 4 Q).re ≥ 0 := by
        have h_pow : (3 / 4 : ℝ) ^ Q.natDegree ≥ 0 := by positivity
        have hQ4_ge : (eval 4 Q).re ≥ 0 := by linarith
        positivity
      nlinarith
    have h_trans : (eval 3 P).re ≤ ((3 / 4) * (4 - z.re)) * ((3 / 4) ^ Q.natDegree * (eval 4 Q).re) := by
      rw [h_eval3_P_re]
      linarith
    have h_simpl : ((3 / 4) * (4 - z.re)) * ((3 / 4) ^ Q.natDegree * (eval 4 Q).re) = (3 / 4) ^ P.natDegree * (eval 4 P).re := by
      rw [hdeg]
      rw [h_eval4_P_re]
      rw [h_deg_Q]
      ring
    rw [h_simpl] at h_trans
    exact h_trans

lemma real_poly_roots_le_3_4 (P : Polynomial ℝ)
    (hroots : ∀ z : ℂ, (P.map (algebraMap ℝ ℂ)).eval z = 0 → z.im = 0 ∧ z.re ∈ Set.Icc 0 1)
    (hP4 : P.eval 4 > 0) :
    P.eval 3 ≤ (3 / 4) ^ P.natDegree * P.eval 4 := by
  have h_comp : (P.map (algebraMap ℝ ℂ)).natDegree = P.natDegree := natDegree_map (algebraMap ℝ ℂ)
  have hP4_re : (eval 4 (P.map (algebraMap ℝ ℂ))).re > 0 := by
    have h_eval_map : (P.map (algebraMap ℝ ℂ)).eval (algebraMap ℝ ℂ 4) = algebraMap ℝ ℂ (P.eval 4) := Polynomial.eval_map_apply (algebraMap ℝ ℂ) 4
    have h_four : algebraMap ℝ ℂ 4 = 4 := rfl
    rw [← h_four, h_eval_map]
    simp [hP4]
  have h_res := complex_poly_roots_le_3_4 (P.map (algebraMap ℝ ℂ)).natDegree (P.map (algebraMap ℝ ℂ)) rfl hroots hP4_re
  rw [h_comp] at h_res
  have h_eval_map_3 : (P.map (algebraMap ℝ ℂ)).eval (algebraMap ℝ ℂ 3) = algebraMap ℝ ℂ (P.eval 3) := Polynomial.eval_map_apply (algebraMap ℝ ℂ) 3
  have h_eval_map_4 : (P.map (algebraMap ℝ ℂ)).eval (algebraMap ℝ ℂ 4) = algebraMap ℝ ℂ (P.eval 4) := Polynomial.eval_map_apply (algebraMap ℝ ℂ) 4
  have h_three : algebraMap ℝ ℂ 3 = 3 := rfl
  have h_four : algebraMap ℝ ℂ 4 = 4 := rfl
  rw [← h_three, h_eval_map_3] at h_res
  rw [← h_four, h_eval_map_4] at h_res
  simp at h_res
  exact h_res

lemma complex_poly_roots_le_2_4 (n : ℕ) :
    ∀ (P : Polynomial ℂ) (hdeg : P.natDegree = n)
      (hroots : ∀ z : ℂ, eval z P = 0 → z.im = 0 ∧ z.re ∈ Set.Icc 0 1)
      (hP4 : (eval 4 P).re > 0),
      (eval 2 P).re ≤ (1 / 2) ^ P.natDegree * (eval 4 P).re := by
  induction' n with n ih
  · intro P hdeg _ _
    have hp0 : P.natDegree = 0 := hdeg
    have h_eq : P = C (coeff P 0) := eq_C_of_natDegree_eq_zero hp0
    rw [h_eq]
    simp
  · intro P hdeg hroots hP4
    have hp_pos : P.degree ≠ 0 := by
      intro h_zero
      have h_nat : P.natDegree = 0 := natDegree_eq_zero_iff_degree_le_zero.mpr (le_of_eq h_zero)
      omega
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_root P hp_pos
    have h_root_P : eval z P = 0 := hz
    have h_z_prop := hroots z h_root_P
    have h_z_im : z.im = 0 := h_z_prop.1
    have h_z_re : z.re ∈ Set.Icc 0 1 := h_z_prop.2
    have h_eq_z : z = (z.re : ℂ) := by
      apply Complex.ext
      · rfl
      · exact h_z_im
    have h_div : X - C z ∣ P := dvd_iff_isRoot.mpr hz
    obtain ⟨Q, hQ⟩ := h_div
    have hQ_ne : Q ≠ 0 := by
      intro h_zero
      rw [h_zero, mul_zero] at hQ
      rw [hQ] at hdeg
      simp only [natDegree_zero] at hdeg
      omega
    have h_X_cz_ne : X - C z ≠ 0 := by
      intro h_zero
      have h_deg : (X - C z).natDegree = 1 := natDegree_X_sub_C z
      rw [h_zero] at h_deg
      simp only [natDegree_zero] at h_deg
      omega
    have h_nat_mul : P.natDegree = (X - C z).natDegree + Q.natDegree := by
      rw [hQ]
      exact natDegree_mul h_X_cz_ne hQ_ne
    have h_deg_Q : Q.natDegree = n := by
      rw [natDegree_X_sub_C] at h_nat_mul
      omega
    have hroots_Q : ∀ w : ℂ, eval w Q = 0 → w.im = 0 ∧ w.re ∈ Set.Icc 0 1 := by
      intro w hw
      have h_eval : eval w P = 0 := by
        rw [hQ]
        simp only [eval_mul, hw, mul_zero]
      exact hroots w h_eval
    have h_eval4_X_cz : eval 4 (X - C z) = 4 - z := by simp only [eval_sub, eval_X, eval_C]
    have h_eval2_X_cz : eval 2 (X - C z) = 2 - z := by simp only [eval_sub, eval_X, eval_C]
    have h_factor4_pos : 4 - z.re > 0 := by
      rcases h_z_re with ⟨h1, h2⟩
      linarith
    have h_factor2_pos : 2 - z.re > 0 := by
      rcases h_z_re with ⟨h1, h2⟩
      linarith
    have h_eval4_P : eval 4 P = eval 4 (X - C z) * eval 4 Q := by rw [hQ, eval_mul]
    have h_eval4_P_re : (eval 4 P).re = (4 - z.re) * (eval 4 Q).re := by
      rw [h_eval4_P, h_eval4_X_cz, h_eq_z]
      simp [Complex.mul_re]
    have hQ4 : (eval 4 Q).re > 0 := by
      have : (eval 4 P).re > 0 := hP4
      rw [h_eval4_P_re] at this
      exact pos_of_mul_pos_right this (by linarith)
    have ih_Q := ih Q h_deg_Q hroots_Q hQ4
    have h_eval2_P : eval 2 P = eval 2 (X - C z) * eval 2 Q := by rw [hQ, eval_mul]
    have h_eval2_P_re : (eval 2 P).re = (2 - z.re) * (eval 2 Q).re := by
      rw [h_eval2_P, h_eval2_X_cz, h_eq_z]
      simp [Complex.mul_re]
    have h_mul_le : (2 - z.re) * (eval 2 Q).re ≤ (2 - z.re) * ((1 / 2) ^ Q.natDegree * (eval 4 Q).re) := by
      have h_factor2_nonneg : 2 - z.re ≥ 0 := by linarith
      nlinarith
    have h_ineq_z : 2 - z.re ≤ (1 / 2) * (4 - z.re) := by
      rcases h_z_re with ⟨h1, h2⟩
      linarith
    have h_factor_le : (2 - z.re) * ((1 / 2) ^ Q.natDegree * (eval 4 Q).re) ≤ ((1 / 2) * (4 - z.re)) * ((1 / 2) ^ Q.natDegree * (eval 4 Q).re) := by
      have h_nonneg : (1 / 2 : ℝ) ^ Q.natDegree * (eval 4 Q).re ≥ 0 := by
        have h_pow : (1 / 2 : ℝ) ^ Q.natDegree ≥ 0 := by positivity
        have hQ4_ge : (eval 4 Q).re ≥ 0 := by linarith
        positivity
      nlinarith
    have h_trans : (eval 2 P).re ≤ ((1 / 2) * (4 - z.re)) * ((1 / 2) ^ Q.natDegree * (eval 4 Q).re) := by
      rw [h_eval2_P_re]
      linarith
    have h_simpl : ((1 / 2) * (4 - z.re)) * ((1 / 2) ^ Q.natDegree * (eval 4 Q).re) = (1 / 2) ^ P.natDegree * (eval 4 P).re := by
      rw [hdeg]
      rw [h_eval4_P_re]
      rw [h_deg_Q]
      ring
    rw [h_simpl] at h_trans
    exact h_trans

lemma real_poly_roots_le_2_4 (P : Polynomial ℝ)
    (hroots : ∀ z : ℂ, (P.map (algebraMap ℝ ℂ)).eval z = 0 → z.im = 0 ∧ z.re ∈ Set.Icc 0 1)
    (hP4 : P.eval 4 > 0) :
    P.eval 2 ≤ (1 / 2) ^ P.natDegree * P.eval 4 := by
  have h_comp : (P.map (algebraMap ℝ ℂ)).natDegree = P.natDegree := natDegree_map (algebraMap ℝ ℂ)
  have hP4_re : (eval 4 (P.map (algebraMap ℝ ℂ))).re > 0 := by
    have h_eval_map : (P.map (algebraMap ℝ ℂ)).eval (algebraMap ℝ ℂ 4) = algebraMap ℝ ℂ (P.eval 4) := Polynomial.eval_map_apply (algebraMap ℝ ℂ) 4
    have h_four : algebraMap ℝ ℂ 4 = 4 := rfl
    rw [← h_four, h_eval_map]
    simp [hP4]
  have h_res := complex_poly_roots_le_2_4 (P.map (algebraMap ℝ ℂ)).natDegree (P.map (algebraMap ℝ ℂ)) rfl hroots hP4_re
  rw [h_comp] at h_res
  have h_eval_map_2 : (P.map (algebraMap ℝ ℂ)).eval (algebraMap ℝ ℂ 2) = algebraMap ℝ ℂ (P.eval 2) := Polynomial.eval_map_apply (algebraMap ℝ ℂ) 2
  have h_eval_map_4 : (P.map (algebraMap ℝ ℂ)).eval (algebraMap ℝ ℂ 4) = algebraMap ℝ ℂ (P.eval 4) := Polynomial.eval_map_apply (algebraMap ℝ ℂ) 4
  have h_two : algebraMap ℝ ℂ 2 = 2 := rfl
  have h_four : algebraMap ℝ ℂ 4 = 4 := rfl
  rw [← h_two, h_eval_map_2] at h_res
  rw [← h_four, h_eval_map_4] at h_res
  simp at h_res
  simp
  exact h_res


lemma complex_poly_roots_eval_1_ge_zero_of_eval_2_gt_zero (n : ℕ) :
    ∀ (P : Polynomial ℂ) (hdeg : P.natDegree = n)
      (hroots : ∀ z : ℂ, eval z P = 0 → z.im = 0 ∧ z.re ∈ Set.Icc 0 1)
      (hP2 : (eval 2 P).re > 0),
      (eval 1 P).re ≥ 0 := by
  induction' n with n ih
  · intro P hdeg _ hP2
    have hp0 : P.natDegree = 0 := hdeg
    have h_eq : P = C (coeff P 0) := eq_C_of_natDegree_eq_zero hp0
    rw [h_eq] at hP2 ⊢
    simp at hP2 ⊢
    linarith
  · intro P hdeg hroots hP2
    have hp_pos : P.degree ≠ 0 := by
      intro h_zero
      have h_nat : P.natDegree = 0 := natDegree_eq_zero_iff_degree_le_zero.mpr (le_of_eq h_zero)
      omega
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_root P hp_pos
    have h_root_P : eval z P = 0 := hz
    have h_z_prop := hroots z h_root_P
    have h_z_im : z.im = 0 := h_z_prop.1
    have h_z_re : z.re ∈ Set.Icc 0 1 := h_z_prop.2
    have h_eq_z : z = (z.re : ℂ) := by
      apply Complex.ext
      · rfl
      · exact h_z_im
    have h_div : X - C z ∣ P := dvd_iff_isRoot.mpr hz
    obtain ⟨Q, hQ⟩ := h_div
    have hQ_ne : Q ≠ 0 := by
      intro h_zero
      rw [h_zero, mul_zero] at hQ
      rw [hQ] at hdeg
      simp only [natDegree_zero] at hdeg
      omega
    have h_X_cz_ne : X - C z ≠ 0 := by
      intro h_zero
      have h_deg : (X - C z).natDegree = 1 := natDegree_X_sub_C z
      rw [h_zero] at h_deg
      simp only [natDegree_zero] at h_deg
      omega
    have h_nat_mul : P.natDegree = (X - C z).natDegree + Q.natDegree := by
      rw [hQ]
      exact natDegree_mul h_X_cz_ne hQ_ne
    have h_deg_Q : Q.natDegree = n := by
      rw [natDegree_X_sub_C] at h_nat_mul
      omega
    have hroots_Q : ∀ w : ℂ, eval w Q = 0 → w.im = 0 ∧ w.re ∈ Set.Icc 0 1 := by
      intro w hw
      have h_eval : eval w P = 0 := by
        rw [hQ]
        simp only [eval_mul, hw, mul_zero]
      exact hroots w h_eval
    have h_eval2_X_cz : eval 2 (X - C z) = 2 - z := by simp only [eval_sub, eval_X, eval_C]
    have h_eval1_X_cz : eval 1 (X - C z) = 1 - z := by simp only [eval_sub, eval_X, eval_C]
    have h_factor2_pos : 2 - z.re > 0 := by
      rcases h_z_re with ⟨h1, h2⟩
      linarith
    have h_factor1_pos : 1 - z.re ≥ 0 := by
      rcases h_z_re with ⟨h1, h2⟩
      linarith
    have h_eval2_P : eval 2 P = eval 2 (X - C z) * eval 2 Q := by rw [hQ, eval_mul]
    have h_eval2_P_re : (eval 2 P).re = (2 - z.re) * (eval 2 Q).re := by
      rw [h_eval2_P, h_eval2_X_cz, h_eq_z]
      simp [Complex.mul_re]
    have hQ2 : (eval 2 Q).re > 0 := by
      have : (eval 2 P).re > 0 := hP2
      rw [h_eval2_P_re] at this
      exact pos_of_mul_pos_right this (by linarith)
    have ih_Q := ih Q h_deg_Q hroots_Q hQ2
    have h_eval1_P : eval 1 P = eval 1 (X - C z) * eval 1 Q := by rw [hQ, eval_mul]
    have h_eval1_P_re : (eval 1 P).re = (1 - z.re) * (eval 1 Q).re := by
      rw [h_eval1_P, h_eval1_X_cz, h_eq_z]
      simp [Complex.mul_re]
    rw [h_eval1_P_re]
    nlinarith

lemma complex_poly_roots_eval_1_ge_zero_of_eval_4_gt_zero (n : ℕ) :
    ∀ (P : Polynomial ℂ) (hdeg : P.natDegree = n)
      (hroots : ∀ z : ℂ, eval z P = 0 → z.im = 0 ∧ z.re ∈ Set.Icc 0 1)
      (hP4 : (eval 4 P).re > 0),
      (eval 1 P).re ≥ 0 := by
  induction' n with n ih
  · intro P hdeg _ hP4
    have hp0 : P.natDegree = 0 := hdeg
    have h_eq : P = C (coeff P 0) := eq_C_of_natDegree_eq_zero hp0
    rw [h_eq] at hP4 ⊢
    simp at hP4 ⊢
    linarith
  · intro P hdeg hroots hP4
    have hp_pos : P.degree ≠ 0 := by
      intro h_zero
      have h_nat : P.natDegree = 0 := natDegree_eq_zero_iff_degree_le_zero.mpr (le_of_eq h_zero)
      omega
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_root P hp_pos
    have h_root_P : eval z P = 0 := hz
    have h_z_prop := hroots z h_root_P
    have h_z_im : z.im = 0 := h_z_prop.1
    have h_z_re : z.re ∈ Set.Icc 0 1 := h_z_prop.2
    have h_eq_z : z = (z.re : ℂ) := by
      apply Complex.ext
      · rfl
      · exact h_z_im
    have h_div : X - C z ∣ P := dvd_iff_isRoot.mpr hz
    obtain ⟨Q, hQ⟩ := h_div
    have hQ_ne : Q ≠ 0 := by
      intro h_zero
      rw [h_zero, mul_zero] at hQ
      rw [hQ] at hdeg
      simp only [natDegree_zero] at hdeg
      omega
    have h_X_cz_ne : X - C z ≠ 0 := by
      intro h_zero
      have h_deg : (X - C z).natDegree = 1 := natDegree_X_sub_C z
      rw [h_zero] at h_deg
      simp only [natDegree_zero] at h_deg
      omega
    have h_nat_mul : P.natDegree = (X - C z).natDegree + Q.natDegree := by
      rw [hQ]
      exact natDegree_mul h_X_cz_ne hQ_ne
    have h_deg_Q : Q.natDegree = n := by
      rw [natDegree_X_sub_C] at h_nat_mul
      omega
    have hroots_Q : ∀ w : ℂ, eval w Q = 0 → w.im = 0 ∧ w.re ∈ Set.Icc 0 1 := by
      intro w hw
      have h_eval : eval w P = 0 := by
        rw [hQ]
        simp only [eval_mul, hw, mul_zero]
      exact hroots w h_eval
    have h_eval4_X_cz : eval 4 (X - C z) = 4 - z := by simp only [eval_sub, eval_X, eval_C]
    have h_eval1_X_cz : eval 1 (X - C z) = 1 - z := by simp only [eval_sub, eval_X, eval_C]
    have h_factor4_pos : 4 - z.re > 0 := by
      rcases h_z_re with ⟨h1, h2⟩
      linarith
    have h_factor1_pos : 1 - z.re ≥ 0 := by
      rcases h_z_re with ⟨h1, h2⟩
      linarith
    have h_eval4_P : eval 4 P = eval 4 (X - C z) * eval 4 Q := by rw [hQ, eval_mul]
    have h_eval4_P_re : (eval 4 P).re = (4 - z.re) * (eval 4 Q).re := by
      rw [h_eval4_P, h_eval4_X_cz, h_eq_z]
      simp [Complex.mul_re]
    have hQ4 : (eval 4 Q).re > 0 := by
      have : (eval 4 P).re > 0 := hP4
      rw [h_eval4_P_re] at this
      exact pos_of_mul_pos_right this (by linarith)
    have ih_Q := ih Q h_deg_Q hroots_Q hQ4
    have h_eval1_P : eval 1 P = eval 1 (X - C z) * eval 1 Q := by rw [hQ, eval_mul]
    have h_eval1_P_re : (eval 1 P).re = (1 - z.re) * (eval 1 Q).re := by
      rw [h_eval1_P, h_eval1_X_cz, h_eq_z]
      simp [Complex.mul_re]
    rw [h_eval1_P_re]
    nlinarith

lemma complex_poly_roots_ge_1_2 (n : ℕ) :
    ∀ (P : Polynomial ℂ) (hdeg : P.natDegree = n)
      (hroots : ∀ z : ℂ, eval z P = 0 → z.im = 0 ∧ z.re ∈ Set.Icc 0 1)
      (hP2 : (eval 2 P).re > 0),
      (eval 2 P).re ≥ 2 ^ P.natDegree * (eval 1 P).re := by
  induction' n with n ih
  · intro P hdeg _ _
    have hp0 : P.natDegree = 0 := hdeg
    have h_eq : P = C (coeff P 0) := eq_C_of_natDegree_eq_zero hp0
    rw [h_eq]
    simp
  · intro P hdeg hroots hP2
    have hp_pos : P.degree ≠ 0 := by
      intro h_zero
      have h_nat : P.natDegree = 0 := natDegree_eq_zero_iff_degree_le_zero.mpr (le_of_eq h_zero)
      omega
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_root P hp_pos
    have h_root_P : eval z P = 0 := hz
    have h_z_prop := hroots z h_root_P
    have h_z_im : z.im = 0 := h_z_prop.1
    have h_z_re : z.re ∈ Set.Icc 0 1 := h_z_prop.2
    have h_eq_z : z = (z.re : ℂ) := by
      apply Complex.ext
      · rfl
      · exact h_z_im
    have h_div : X - C z ∣ P := dvd_iff_isRoot.mpr hz
    obtain ⟨Q, hQ⟩ := h_div
    have hQ_ne : Q ≠ 0 := by
      intro h_zero
      rw [h_zero, mul_zero] at hQ
      rw [hQ] at hdeg
      simp only [natDegree_zero] at hdeg
      omega
    have h_X_cz_ne : X - C z ≠ 0 := by
      intro h_zero
      have h_deg : (X - C z).natDegree = 1 := natDegree_X_sub_C z
      rw [h_zero] at h_deg
      simp only [natDegree_zero] at h_deg
      omega
    have h_nat_mul : P.natDegree = (X - C z).natDegree + Q.natDegree := by
      rw [hQ]
      exact natDegree_mul h_X_cz_ne hQ_ne
    have h_deg_Q : Q.natDegree = n := by
      rw [natDegree_X_sub_C] at h_nat_mul
      omega
    have hroots_Q : ∀ w : ℂ, eval w Q = 0 → w.im = 0 ∧ w.re ∈ Set.Icc 0 1 := by
      intro w hw
      have h_eval : eval w P = 0 := by
        rw [hQ]
        simp only [eval_mul, hw, mul_zero]
      exact hroots w h_eval
    have h_eval2_X_cz : eval 2 (X - C z) = 2 - z := by simp only [eval_sub, eval_X, eval_C]
    have h_eval1_X_cz : eval 1 (X - C z) = 1 - z := by simp only [eval_sub, eval_X, eval_C]
    have h_factor2_pos : 2 - z.re > 0 := by
      rcases h_z_re with ⟨h1, h2⟩
      linarith
    have h_factor1_pos : 1 - z.re ≥ 0 := by
      rcases h_z_re with ⟨h1, h2⟩
      linarith
    have h_eval2_P : eval 2 P = eval 2 (X - C z) * eval 2 Q := by rw [hQ, eval_mul]
    have h_eval2_P_re : (eval 2 P).re = (2 - z.re) * (eval 2 Q).re := by
      rw [h_eval2_P, h_eval2_X_cz, h_eq_z]
      simp [Complex.mul_re]
    have hQ2 : (eval 2 Q).re > 0 := by
      have : (eval 2 P).re > 0 := hP2
      rw [h_eval2_P_re] at this
      exact pos_of_mul_pos_right this (by linarith)
    have ih_Q := ih Q h_deg_Q hroots_Q hQ2
    have h_eval1_P : eval 1 P = eval 1 (X - C z) * eval 1 Q := by rw [hQ, eval_mul]
    have h_eval1_P_re : (eval 1 P).re = (1 - z.re) * (eval 1 Q).re := by
      rw [h_eval1_P, h_eval1_X_cz, h_eq_z]
      simp [Complex.mul_re]
    have h_mul_le : (2 - z.re) * (2 ^ Q.natDegree * (eval 1 Q).re) ≤ (2 - z.re) * (eval 2 Q).re := by
      have h_factor2_nonneg : 2 - z.re ≥ 0 := by linarith
      nlinarith
    have h_ineq_z : 2 * (1 - z.re) ≤ 2 - z.re := by
      rcases h_z_re with ⟨h1, h2⟩
      linarith
    have h_factor_le : (2 * (1 - z.re)) * (2 ^ Q.natDegree * (eval 1 Q).re) ≤ (2 - z.re) * (2 ^ Q.natDegree * (eval 1 Q).re) := by
      have h_nonneg : (2 : ℝ) ^ Q.natDegree * (eval 1 Q).re ≥ 0 := by
        have h_pow : (2 : ℝ) ^ Q.natDegree ≥ 0 := by positivity
        have hQ1_ge := complex_poly_roots_eval_1_ge_zero_of_eval_2_gt_zero Q.natDegree Q rfl hroots_Q hQ2
        positivity
      nlinarith
    have h_trans : (2 * (1 - z.re)) * (2 ^ Q.natDegree * (eval 1 Q).re) ≤ (eval 2 P).re := by
      rw [h_eval2_P_re]
      linarith
    have h_simpl : (2 * (1 - z.re)) * (2 ^ Q.natDegree * (eval 1 Q).re) = 2 ^ P.natDegree * (eval 1 P).re := by
      rw [hdeg]
      rw [h_eval1_P_re]
      rw [h_deg_Q]
      ring
    rw [h_simpl] at h_trans
    exact h_trans

lemma real_poly_roots_ge_1_2 (P : Polynomial ℝ)
    (hroots : ∀ z : ℂ, (P.map (algebraMap ℝ ℂ)).eval z = 0 → z.im = 0 ∧ z.re ∈ Set.Icc 0 1)
    (hP2 : P.eval 2 > 0) :
    P.eval 2 ≥ 2 ^ P.natDegree * P.eval 1 := by
  have h_comp : (P.map (algebraMap ℝ ℂ)).natDegree = P.natDegree := natDegree_map (algebraMap ℝ ℂ)
  have hP2_re : (eval 2 (P.map (algebraMap ℝ ℂ))).re > 0 := by
    have h_eval_map : (P.map (algebraMap ℝ ℂ)).eval (algebraMap ℝ ℂ 2) = algebraMap ℝ ℂ (P.eval 2) := Polynomial.eval_map_apply (algebraMap ℝ ℂ) 2
    have h_two : algebraMap ℝ ℂ 2 = 2 := rfl
    rw [← h_two, h_eval_map]
    simp [hP2]
  have h_res := complex_poly_roots_ge_1_2 (P.map (algebraMap ℝ ℂ)).natDegree (P.map (algebraMap ℝ ℂ)) rfl hroots hP2_re
  rw [h_comp] at h_res
  have h_eval_map_1 : (P.map (algebraMap ℝ ℂ)).eval (algebraMap ℝ ℂ 1) = algebraMap ℝ ℂ (P.eval 1) := Polynomial.eval_map_apply (algebraMap ℝ ℂ) 1
  have h_eval_map_2 : (P.map (algebraMap ℝ ℂ)).eval (algebraMap ℝ ℂ 2) = algebraMap ℝ ℂ (P.eval 2) := Polynomial.eval_map_apply (algebraMap ℝ ℂ) 2
  have h_one : algebraMap ℝ ℂ 1 = 1 := rfl
  have h_two : algebraMap ℝ ℂ 2 = 2 := rfl
  rw [← h_one, h_eval_map_1] at h_res
  rw [← h_two, h_eval_map_2] at h_res
  simp at h_res
  exact h_res

lemma complex_poly_roots_ge_1_4 (n : ℕ) :
    ∀ (P : Polynomial ℂ) (hdeg : P.natDegree = n)
      (hroots : ∀ z : ℂ, eval z P = 0 → z.im = 0 ∧ z.re ∈ Set.Icc 0 1)
      (hP4 : (eval 4 P).re > 0),
      (eval 4 P).re ≥ 4 ^ P.natDegree * (eval 1 P).re := by
  induction' n with n ih
  · intro P hdeg _ _
    have hp0 : P.natDegree = 0 := hdeg
    have h_eq : P = C (coeff P 0) := eq_C_of_natDegree_eq_zero hp0
    rw [h_eq]
    simp
  · intro P hdeg hroots hP4
    have hp_pos : P.degree ≠ 0 := by
      intro h_zero
      have h_nat : P.natDegree = 0 := natDegree_eq_zero_iff_degree_le_zero.mpr (le_of_eq h_zero)
      omega
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_root P hp_pos
    have h_root_P : eval z P = 0 := hz
    have h_z_prop := hroots z h_root_P
    have h_z_im : z.im = 0 := h_z_prop.1
    have h_z_re : z.re ∈ Set.Icc 0 1 := h_z_prop.2
    have h_eq_z : z = (z.re : ℂ) := by
      apply Complex.ext
      · rfl
      · exact h_z_im
    have h_div : X - C z ∣ P := dvd_iff_isRoot.mpr hz
    obtain ⟨Q, hQ⟩ := h_div
    have hQ_ne : Q ≠ 0 := by
      intro h_zero
      rw [h_zero, mul_zero] at hQ
      rw [hQ] at hdeg
      simp only [natDegree_zero] at hdeg
      omega
    have h_X_cz_ne : X - C z ≠ 0 := by
      intro h_zero
      have h_deg : (X - C z).natDegree = 1 := natDegree_X_sub_C z
      rw [h_zero] at h_deg
      simp only [natDegree_zero] at h_deg
      omega
    have h_nat_mul : P.natDegree = (X - C z).natDegree + Q.natDegree := by
      rw [hQ]
      exact natDegree_mul h_X_cz_ne hQ_ne
    have h_deg_Q : Q.natDegree = n := by
      rw [natDegree_X_sub_C] at h_nat_mul
      omega
    have hroots_Q : ∀ w : ℂ, eval w Q = 0 → w.im = 0 ∧ w.re ∈ Set.Icc 0 1 := by
      intro w hw
      have h_eval : eval w P = 0 := by
        rw [hQ]
        simp only [eval_mul, hw, mul_zero]
      exact hroots w h_eval
    have h_eval4_X_cz : eval 4 (X - C z) = 4 - z := by simp only [eval_sub, eval_X, eval_C]
    have h_eval1_X_cz : eval 1 (X - C z) = 1 - z := by simp only [eval_sub, eval_X, eval_C]
    have h_factor4_pos : 4 - z.re > 0 := by
      rcases h_z_re with ⟨h1, h2⟩
      linarith
    have h_factor1_pos : 1 - z.re ≥ 0 := by
      rcases h_z_re with ⟨h1, h2⟩
      linarith
    have h_eval4_P : eval 4 P = eval 4 (X - C z) * eval 4 Q := by rw [hQ, eval_mul]
    have h_eval4_P_re : (eval 4 P).re = (4 - z.re) * (eval 4 Q).re := by
      rw [h_eval4_P, h_eval4_X_cz, h_eq_z]
      simp [Complex.mul_re]
    have hQ4 : (eval 4 Q).re > 0 := by
      have : (eval 4 P).re > 0 := hP4
      rw [h_eval4_P_re] at this
      exact pos_of_mul_pos_right this (by linarith)
    have ih_Q := ih Q h_deg_Q hroots_Q hQ4
    have h_eval1_P : eval 1 P = eval 1 (X - C z) * eval 1 Q := by rw [hQ, eval_mul]
    have h_eval1_P_re : (eval 1 P).re = (1 - z.re) * (eval 1 Q).re := by
      rw [h_eval1_P, h_eval1_X_cz, h_eq_z]
      simp [Complex.mul_re]
    have h_mul_le : (4 - z.re) * (4 ^ Q.natDegree * (eval 1 Q).re) ≤ (4 - z.re) * (eval 4 Q).re := by
      have h_factor4_nonneg : 4 - z.re ≥ 0 := by linarith
      nlinarith
    have h_ineq_z : 4 * (1 - z.re) ≤ 4 - z.re := by
      rcases h_z_re with ⟨h1, h2⟩
      linarith
    have h_factor_le : (4 * (1 - z.re)) * (4 ^ Q.natDegree * (eval 1 Q).re) ≤ (4 - z.re) * (4 ^ Q.natDegree * (eval 1 Q).re) := by
      have h_nonneg : (4 : ℝ) ^ Q.natDegree * (eval 1 Q).re ≥ 0 := by
        have h_pow : (4 : ℝ) ^ Q.natDegree ≥ 0 := by positivity
        have hQ1_ge := complex_poly_roots_eval_1_ge_zero_of_eval_4_gt_zero Q.natDegree Q rfl hroots_Q hQ4
        positivity
      nlinarith
    have h_trans : (4 * (1 - z.re)) * (4 ^ Q.natDegree * (eval 1 Q).re) ≤ (eval 4 P).re := by
      rw [h_eval4_P_re]
      linarith
    have h_simpl : (4 * (1 - z.re)) * (4 ^ Q.natDegree * (eval 1 Q).re) = 4 ^ P.natDegree * (eval 1 P).re := by
      rw [hdeg]
      rw [h_eval1_P_re]
      rw [h_deg_Q]
      ring
    rw [h_simpl] at h_trans
    exact h_trans

lemma real_poly_roots_ge_1_4 (P : Polynomial ℝ)
    (hroots : ∀ z : ℂ, (P.map (algebraMap ℝ ℂ)).eval z = 0 → z.im = 0 ∧ z.re ∈ Set.Icc 0 1)
    (hP4 : P.eval 4 > 0) :
    P.eval 4 ≥ 4 ^ P.natDegree * P.eval 1 := by
  have h_comp : (P.map (algebraMap ℝ ℂ)).natDegree = P.natDegree := natDegree_map (algebraMap ℝ ℂ)
  have hP4_re : (eval 4 (P.map (algebraMap ℝ ℂ))).re > 0 := by
    have h_eval_map : (P.map (algebraMap ℝ ℂ)).eval (algebraMap ℝ ℂ 4) = algebraMap ℝ ℂ (P.eval 4) := Polynomial.eval_map_apply (algebraMap ℝ ℂ) 4
    have h_four : algebraMap ℝ ℂ 4 = 4 := rfl
    rw [← h_four, h_eval_map]
    simp [hP4]
  have h_res := complex_poly_roots_ge_1_4 (P.map (algebraMap ℝ ℂ)).natDegree (P.map (algebraMap ℝ ℂ)) rfl hroots hP4_re
  rw [h_comp] at h_res
  have h_eval_map_1 : (P.map (algebraMap ℝ ℂ)).eval (algebraMap ℝ ℂ 1) = algebraMap ℝ ℂ (P.eval 1) := Polynomial.eval_map_apply (algebraMap ℝ ℂ) 1
  have h_eval_map_4 : (P.map (algebraMap ℝ ℂ)).eval (algebraMap ℝ ℂ 4) = algebraMap ℝ ℂ (P.eval 4) := Polynomial.eval_map_apply (algebraMap ℝ ℂ) 4
  have h_one : algebraMap ℝ ℂ 1 = 1 := rfl
  have h_four : algebraMap ℝ ℂ 4 = 4 := rfl
  rw [← h_one, h_eval_map_1] at h_res
  rw [← h_four, h_eval_map_4] at h_res
  simp at h_res
  exact h_res

lemma Q_roots_in_Icc (Q : Polynomial ℝ)
    (hroots : ∀ z : ℂ, (Q.map (algebraMap ℝ ℂ)).eval (z^2) = 0 → z.im = 0 ∧ z.re ∈ Set.Icc (-1) 1)
    (w : ℂ) (hw : (Q.map (algebraMap ℝ ℂ)).eval w = 0) :
    w.im = 0 ∧ w.re ∈ Set.Icc 0 1 := by
  obtain ⟨z, hz⟩ : ∃ z : ℂ, w = z^2 := by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_eq_mul_self w
    use z
    rw [hz, sq]
  have h_eval : (Q.map (algebraMap ℝ ℂ)).eval (z^2) = 0 := by rw [← hz, hw]
  have h_res := hroots z h_eval
  have hz_im : z.im = 0 := h_res.1
  have hz_re : z.re ∈ Set.Icc (-1) 1 := h_res.2
  have h_eq : z = (z.re : ℂ) := by
    apply Complex.ext
    · rfl
    · exact hz_im
  have h_w : w = (((z.re ^ 2 : ℝ) : ℂ)) := by
    rw [hz, h_eq]
    push_cast
    rfl
  constructor
  · rw [h_w]
    exact Complex.ofReal_im (z.re ^ 2)
  · rw [h_w]
    rw [Complex.ofReal_re]
    have : z.re^2 ∈ Set.Icc 0 1 := by
      rcases hz_re with ⟨h1, h2⟩
      constructor
      · positivity
      · nlinarith
    exact this

lemma complex_poly_roots_ge_4_9 (n : ℕ) :
    ∀ (P : Polynomial ℂ) (hdeg : P.natDegree = n)
      (hroots : ∀ z : ℂ, eval z P = 0 → z.im = 0 ∧ z.re ∈ Set.Icc 0 1)
      (hP4 : (eval 4 P).re > 0),
      (eval 9 P).re ≥ (9 / 4) ^ P.natDegree * (eval 4 P).re := by
  induction' n with n ih
  · intro P hdeg _ _
    have hp0 : P.natDegree = 0 := hdeg
    have h_eq : P = C (coeff P 0) := eq_C_of_natDegree_eq_zero hp0
    rw [h_eq]
    simp
  · intro P hdeg hroots hP4
    have hp_pos : P.degree ≠ 0 := by
      intro h_zero
      have h_nat : P.natDegree = 0 := natDegree_eq_zero_iff_degree_le_zero.mpr (le_of_eq h_zero)
      omega
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_root P hp_pos
    have h_root_P : eval z P = 0 := hz
    have h_z_prop := hroots z h_root_P
    have h_z_im : z.im = 0 := h_z_prop.1
    have h_z_re : z.re ∈ Set.Icc 0 1 := h_z_prop.2
    have h_eq_z : z = (z.re : ℂ) := by
      apply Complex.ext
      · rfl
      · exact h_z_im
    -- P = (X - C z) * Q
    have h_div : X - C z ∣ P := dvd_iff_isRoot.mpr hz
    obtain ⟨Q, hQ⟩ := h_div
    have hQ_ne : Q ≠ 0 := by
      intro h_zero
      rw [h_zero, mul_zero] at hQ
      rw [hQ] at hdeg
      simp only [natDegree_zero] at hdeg
      omega
    have h_X_cz_ne : X - C z ≠ 0 := by
      intro h_zero
      have h_deg : (X - C z).natDegree = 1 := natDegree_X_sub_C z
      rw [h_zero] at h_deg
      simp only [natDegree_zero] at h_deg
      omega
    have h_nat_mul : P.natDegree = (X - C z).natDegree + Q.natDegree := by
      rw [hQ]
      exact natDegree_mul h_X_cz_ne hQ_ne
    have h_deg_Q : Q.natDegree = n := by
      rw [natDegree_X_sub_C] at h_nat_mul
      omega
    have hroots_Q : ∀ w : ℂ, eval w Q = 0 → w.im = 0 ∧ w.re ∈ Set.Icc 0 1 := by
      intro w hw
      have h_eval : eval w P = 0 := by
        rw [hQ]
        simp only [eval_mul, hw, mul_zero]
      exact hroots w h_eval
    have h_eval4_X_cz : eval 4 (X - C z) = 4 - z := by simp only [eval_sub, eval_X, eval_C]
    have h_eval9_X_cz : eval 9 (X - C z) = 9 - z := by simp only [eval_sub, eval_X, eval_C]
    have h_factor4_pos : 4 - z.re > 0 := by
      rcases h_z_re with ⟨h1, h2⟩
      linarith
    have h_factor9_pos : 9 - z.re > 0 := by
      rcases h_z_re with ⟨h1, h2⟩
      linarith
    have h_eval4_P : eval 4 P = eval 4 (X - C z) * eval 4 Q := by rw [hQ, eval_mul]
    have h_eval4_P_re : (eval 4 P).re = (4 - z.re) * (eval 4 Q).re := by
      rw [h_eval4_P, h_eval4_X_cz, h_eq_z]
      simp [Complex.mul_re]
    have hQ4 : (eval 4 Q).re > 0 := by
      have : (eval 4 P).re > 0 := hP4
      rw [h_eval4_P_re] at this
      exact pos_of_mul_pos_right this (by linarith)
    have ih_Q := ih Q h_deg_Q hroots_Q hQ4
    have h_eval9_P : eval 9 P = eval 9 (X - C z) * eval 9 Q := by rw [hQ, eval_mul]
    have h_eval9_P_re : (eval 9 P).re = (9 - z.re) * (eval 9 Q).re := by
      rw [h_eval9_P, h_eval9_X_cz, h_eq_z]
      simp [Complex.mul_re]
    have h_mul_le : (9 - z.re) * ((9 / 4) ^ Q.natDegree * (eval 4 Q).re) ≤ (9 - z.re) * (eval 9 Q).re := by
      have h_factor9_nonneg : 9 - z.re ≥ 0 := by linarith
      nlinarith
    have h_ineq_z : (9 / 4) * (4 - z.re) ≤ 9 - z.re := by
      rcases h_z_re with ⟨h1, h2⟩
      linarith
    have h_factor_le : ((9 / 4) * (4 - z.re)) * ((9 / 4) ^ Q.natDegree * (eval 4 Q).re) ≤ (9 - z.re) * ((9 / 4) ^ Q.natDegree * (eval 4 Q).re) := by
      have h_nonneg : (9 / 4) ^ Q.natDegree * (eval 4 Q).re ≥ 0 := by
        have h_pow : (9 / 4 : ℝ) ^ Q.natDegree ≥ 0 := by positivity
        have hQ4_ge : (eval 4 Q).re ≥ 0 := by linarith
        positivity
      nlinarith
    have h_trans : ((9 / 4) * (4 - z.re)) * ((9 / 4) ^ Q.natDegree * (eval 4 Q).re) ≤ (eval 9 P).re := by
      rw [h_eval9_P_re]
      linarith
    have h_simpl : ((9 / 4) * (4 - z.re)) * ((9 / 4) ^ Q.natDegree * (eval 4 Q).re) = (9 / 4) ^ P.natDegree * (eval 4 P).re := by
      rw [hdeg]
      rw [h_eval4_P_re]
      rw [h_deg_Q]
      ring
    rw [h_simpl] at h_trans
    exact h_trans

lemma real_poly_roots_ge_4_9 (P : Polynomial ℝ)
    (hroots : ∀ z : ℂ, (P.map (algebraMap ℝ ℂ)).eval z = 0 → z.im = 0 ∧ z.re ∈ Set.Icc 0 1)
    (hP4 : P.eval 4 > 0) :
    P.eval 9 ≥ (9 / 4) ^ P.natDegree * P.eval 4 := by
  have h_comp : (P.map (algebraMap ℝ ℂ)).natDegree = P.natDegree := natDegree_map (algebraMap ℝ ℂ)
  have hP4_re : (eval 4 (P.map (algebraMap ℝ ℂ))).re > 0 := by
    have h_eval_map : (P.map (algebraMap ℝ ℂ)).eval (algebraMap ℝ ℂ 4) = algebraMap ℝ ℂ (P.eval 4) := Polynomial.eval_map_apply (algebraMap ℝ ℂ) 4
    have h_four : algebraMap ℝ ℂ 4 = 4 := rfl
    rw [← h_four, h_eval_map]
    simp [hP4]
  have h_res := complex_poly_roots_ge_4_9 (P.map (algebraMap ℝ ℂ)).natDegree (P.map (algebraMap ℝ ℂ)) rfl hroots hP4_re
  rw [h_comp] at h_res
  have h_eval_map_9 : (P.map (algebraMap ℝ ℂ)).eval (algebraMap ℝ ℂ 9) = algebraMap ℝ ℂ (P.eval 9) := Polynomial.eval_map_apply (algebraMap ℝ ℂ) 9
  have h_eval_map_4 : (P.map (algebraMap ℝ ℂ)).eval (algebraMap ℝ ℂ 4) = algebraMap ℝ ℂ (P.eval 4) := Polynomial.eval_map_apply (algebraMap ℝ ℂ) 4
  have h_nine : algebraMap ℝ ℂ 9 = 9 := rfl
  have h_four : algebraMap ℝ ℂ 4 = 4 := rfl
  rw [← h_nine, h_eval_map_9] at h_res
  rw [← h_four, h_eval_map_4] at h_res
  simp at h_res
  exact h_res


lemma complex_poly_roots_le_4_9 (n : ℕ) :
    ∀ (P : Polynomial ℂ) (hdeg : P.natDegree = n)
      (hroots : ∀ z : ℂ, eval z P = 0 → z.im = 0 ∧ z.re ∈ Set.Icc 0 1)
      (hP4 : (eval 4 P).re > 0),
      (eval 9 P).re ≤ (8 / 3) ^ P.natDegree * (eval 4 P).re := by
  induction' n with n ih
  · intro P hdeg _ _
    have hp0 : P.natDegree = 0 := hdeg
    have h_eq : P = C (coeff P 0) := eq_C_of_natDegree_eq_zero hp0
    rw [h_eq]
    simp
  · intro P hdeg hroots hP4
    have hp_pos : P.degree ≠ 0 := by
      intro h_zero
      have h_nat : P.natDegree = 0 := natDegree_eq_zero_iff_degree_le_zero.mpr (le_of_eq h_zero)
      omega
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_root P hp_pos
    have h_root_P : eval z P = 0 := hz
    have h_z_prop := hroots z h_root_P
    have h_z_im : z.im = 0 := h_z_prop.1
    have h_z_re : z.re ∈ Set.Icc 0 1 := h_z_prop.2
    have h_eq_z : z = (z.re : ℂ) := by
      apply Complex.ext
      · rfl
      · exact h_z_im
    -- P = (X - C z) * Q
    have h_div : X - C z ∣ P := dvd_iff_isRoot.mpr hz
    obtain ⟨Q, hQ⟩ := h_div
    have hQ_ne : Q ≠ 0 := by
      intro h_zero
      rw [h_zero, mul_zero] at hQ
      rw [hQ] at hdeg
      simp only [natDegree_zero] at hdeg
      omega
    have h_X_cz_ne : X - C z ≠ 0 := by
      intro h_zero
      have h_deg : (X - C z).natDegree = 1 := natDegree_X_sub_C z
      rw [h_zero] at h_deg
      simp only [natDegree_zero] at h_deg
      omega
    have h_nat_mul : P.natDegree = (X - C z).natDegree + Q.natDegree := by
      rw [hQ]
      exact natDegree_mul h_X_cz_ne hQ_ne
    have h_deg_Q : Q.natDegree = n := by
      rw [natDegree_X_sub_C] at h_nat_mul
      omega
    have hroots_Q : ∀ w : ℂ, eval w Q = 0 → w.im = 0 ∧ w.re ∈ Set.Icc 0 1 := by
      intro w hw
      have h_eval : eval w P = 0 := by
        rw [hQ]
        simp only [eval_mul, hw, mul_zero]
      exact hroots w h_eval
    have h_eval4_X_cz : eval 4 (X - C z) = 4 - z := by simp only [eval_sub, eval_X, eval_C]
    have h_eval9_X_cz : eval 9 (X - C z) = 9 - z := by simp only [eval_sub, eval_X, eval_C]
    have h_factor4_pos : 4 - z.re > 0 := by
      rcases h_z_re with ⟨h1, h2⟩
      linarith
    have h_factor9_pos : 9 - z.re > 0 := by
      rcases h_z_re with ⟨h1, h2⟩
      linarith
    have h_eval4_P : eval 4 P = eval 4 (X - C z) * eval 4 Q := by rw [hQ, eval_mul]
    have h_eval4_P_re : (eval 4 P).re = (4 - z.re) * (eval 4 Q).re := by
      rw [h_eval4_P, h_eval4_X_cz, h_eq_z]
      simp [Complex.mul_re]
    have hQ4 : (eval 4 Q).re > 0 := by
      have : (eval 4 P).re > 0 := hP4
      rw [h_eval4_P_re] at this
      exact pos_of_mul_pos_right this (by linarith)
    have ih_Q := ih Q h_deg_Q hroots_Q hQ4
    have h_eval9_P : eval 9 P = eval 9 (X - C z) * eval 9 Q := by rw [hQ, eval_mul]
    have h_eval9_P_re : (eval 9 P).re = (9 - z.re) * (eval 9 Q).re := by
      rw [h_eval9_P, h_eval9_X_cz, h_eq_z]
      simp [Complex.mul_re]
    have h_mul_le : (9 - z.re) * (eval 9 Q).re ≤ (9 - z.re) * ((8 / 3) ^ Q.natDegree * (eval 4 Q).re) := by
      have h_factor9_nonneg : 9 - z.re ≥ 0 := by linarith
      nlinarith
    have h_ineq_z : 9 - z.re ≤ (8 / 3) * (4 - z.re) := by
      rcases h_z_re with ⟨h1, h2⟩
      linarith
    have h_factor_le : (9 - z.re) * ((8 / 3) ^ Q.natDegree * (eval 4 Q).re) ≤ ((8 / 3) * (4 - z.re)) * ((8 / 3) ^ Q.natDegree * (eval 4 Q).re) := by
      have h_nonneg : (8 / 3) ^ Q.natDegree * (eval 4 Q).re ≥ 0 := by
        have h_pow : (8 / 3 : ℝ) ^ Q.natDegree ≥ 0 := by positivity
        have hQ4_ge : (eval 4 Q).re ≥ 0 := by linarith
        positivity
      nlinarith
    have h_trans : (eval 9 P).re ≤ ((8 / 3) * (4 - z.re)) * ((8 / 3) ^ Q.natDegree * (eval 4 Q).re) := by
      rw [h_eval9_P_re]
      linarith
    have h_simpl : ((8 / 3) * (4 - z.re)) * ((8 / 3) ^ Q.natDegree * (eval 4 Q).re) = (8 / 3) ^ P.natDegree * (eval 4 P).re := by
      rw [hdeg]
      rw [h_eval4_P_re]
      rw [h_deg_Q]
      ring
    rw [h_simpl] at h_trans
    exact h_trans

lemma real_poly_roots_le_4_9 (P : Polynomial ℝ)
    (hroots : ∀ z : ℂ, (P.map (algebraMap ℝ ℂ)).eval z = 0 → z.im = 0 ∧ z.re ∈ Set.Icc 0 1)
    (hP4 : P.eval 4 > 0) :
    P.eval 9 ≤ (8 / 3) ^ P.natDegree * P.eval 4 := by
  have h_comp : (P.map (algebraMap ℝ ℂ)).natDegree = P.natDegree := natDegree_map (algebraMap ℝ ℂ)
  have hP4_re : (eval 4 (P.map (algebraMap ℝ ℂ))).re > 0 := by
    have h_eval_map : (P.map (algebraMap ℝ ℂ)).eval (algebraMap ℝ ℂ 4) = algebraMap ℝ ℂ (P.eval 4) := Polynomial.eval_map_apply (algebraMap ℝ ℂ) 4
    have h_four : algebraMap ℝ ℂ 4 = 4 := rfl
    rw [← h_four, h_eval_map]
    simp [hP4]
  have h_res := complex_poly_roots_le_4_9 (P.map (algebraMap ℝ ℂ)).natDegree (P.map (algebraMap ℝ ℂ)) rfl hroots hP4_re
  rw [h_comp] at h_res
  have h_eval_map_9 : (P.map (algebraMap ℝ ℂ)).eval (algebraMap ℝ ℂ 9) = algebraMap ℝ ℂ (P.eval 9) := Polynomial.eval_map_apply (algebraMap ℝ ℂ) 9
  have h_eval_map_4 : (P.map (algebraMap ℝ ℂ)).eval (algebraMap ℝ ℂ 4) = algebraMap ℝ ℂ (P.eval 4) := Polynomial.eval_map_apply (algebraMap ℝ ℂ) 4
  have h_nine : algebraMap ℝ ℂ 9 = 9 := rfl
  have h_four : algebraMap ℝ ℂ 4 = 4 := rfl
  rw [← h_nine, h_eval_map_9] at h_res
  rw [← h_four, h_eval_map_4] at h_res
  simp at h_res
  exact h_res


lemma complex_poly_roots_ge_5_4 (n : ℕ) :
    ∀ (P : Polynomial ℂ) (hdeg : P.natDegree = n)
      (hroots : ∀ z : ℂ, eval z P = 0 → z.im = 0 ∧ z.re ∈ Set.Icc 0 1)
      (hP4 : (eval 4 P).re > 0),
      (eval 5 P).re ≥ (eval 4 P).re := by
  induction' n with n ih
  · intro P hdeg _ _
    have hp0 : P.natDegree = 0 := hdeg
    have h_eq : P = C (coeff P 0) := eq_C_of_natDegree_eq_zero hp0
    rw [h_eq]
    simp
  · intro P hdeg hroots hP4
    have hp_pos : P.degree ≠ 0 := by
      intro h_zero
      have h_nat : P.natDegree = 0 := natDegree_eq_zero_iff_degree_le_zero.mpr (le_of_eq h_zero)
      omega
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_root P hp_pos
    have h_root_P : eval z P = 0 := hz
    have h_z_prop := hroots z h_root_P
    have h_z_im : z.im = 0 := h_z_prop.1
    have h_z_re : z.re ∈ Set.Icc 0 1 := h_z_prop.2
    have h_eq_z : z = (z.re : ℂ) := by
      apply Complex.ext
      · rfl
      · exact h_z_im
    -- P = (X - C z) * Q
    have h_div : X - C z ∣ P := dvd_iff_isRoot.mpr hz
    obtain ⟨Q, hQ⟩ := h_div
    have hQ_ne : Q ≠ 0 := by
      intro h_zero
      rw [h_zero, mul_zero] at hQ
      rw [hQ] at hdeg
      simp only [natDegree_zero] at hdeg
      omega
    have h_X_cz_ne : X - C z ≠ 0 := by
      intro h_zero
      have h_deg : (X - C z).natDegree = 1 := natDegree_X_sub_C z
      rw [h_zero] at h_deg
      simp only [natDegree_zero] at h_deg
      omega
    have h_nat_mul : P.natDegree = (X - C z).natDegree + Q.natDegree := by
      rw [hQ]
      exact natDegree_mul h_X_cz_ne hQ_ne
    have h_deg_Q : Q.natDegree = n := by
      rw [natDegree_X_sub_C] at h_nat_mul
      omega
    have hroots_Q : ∀ w : ℂ, eval w Q = 0 → w.im = 0 ∧ w.re ∈ Set.Icc 0 1 := by
      intro w hw
      have h_eval : eval w P = 0 := by
        rw [hQ]
        simp only [eval_mul, hw, mul_zero]
      exact hroots w h_eval
    have h_eval4_X_cz : eval 4 (X - C z) = 4 - z := by simp only [eval_sub, eval_X, eval_C]
    have h_eval5_X_cz : eval 5 (X - C z) = 5 - z := by simp only [eval_sub, eval_X, eval_C]
    have h_factor4_pos : 4 - z.re > 0 := by
      rcases h_z_re with ⟨h1, h2⟩
      linarith
    have h_factor5_pos : 5 - z.re > 0 := by
      rcases h_z_re with ⟨h1, h2⟩
      linarith
    have h_eval4_P : eval 4 P = eval 4 (X - C z) * eval 4 Q := by rw [hQ, eval_mul]
    have h_eval4_P_re : (eval 4 P).re = (4 - z.re) * (eval 4 Q).re := by
      rw [h_eval4_P, h_eval4_X_cz, h_eq_z]
      simp [Complex.mul_re]
    have hQ4 : (eval 4 Q).re > 0 := by
      have : (eval 4 P).re > 0 := hP4
      rw [h_eval4_P_re] at this
      exact pos_of_mul_pos_right this (by linarith)
    have ih_Q := ih Q h_deg_Q hroots_Q hQ4
    have h_eval5_P : eval 5 P = eval 5 (X - C z) * eval 5 Q := by rw [hQ, eval_mul]
    have h_eval5_P_re : (eval 5 P).re = (5 - z.re) * (eval 5 Q).re := by
      rw [h_eval5_P, h_eval5_X_cz, h_eq_z]
      simp [Complex.mul_re]
    have h_mul_le : (5 - z.re) * (eval 4 Q).re ≤ (5 - z.re) * (eval 5 Q).re := by
      have h_factor5_nonneg : 5 - z.re ≥ 0 := by linarith
      nlinarith
    have h_ineq_z : (4 - z.re) ≤ 5 - z.re := by linarith
    have h_factor_le : (4 - z.re) * (eval 4 Q).re ≤ (5 - z.re) * (eval 4 Q).re := by
      have h_nonneg : (eval 4 Q).re ≥ 0 := by linarith
      nlinarith
    have h_trans : (4 - z.re) * (eval 4 Q).re ≤ (eval 5 P).re := by
      rw [h_eval5_P_re]
      linarith
    rw [← h_eval4_P_re] at h_trans
    exact h_trans

lemma real_poly_roots_ge_5_4 (P : Polynomial ℝ)
    (hroots : ∀ z : ℂ, (P.map (algebraMap ℝ ℂ)).eval z = 0 → z.im = 0 ∧ z.re ∈ Set.Icc 0 1)
    (hP4 : P.eval 4 > 0) :
    P.eval 5 ≥ P.eval 4 := by
  have h_comp : (P.map (algebraMap ℝ ℂ)).natDegree = P.natDegree := natDegree_map (algebraMap ℝ ℂ)
  have hP4_re : (eval 4 (P.map (algebraMap ℝ ℂ))).re > 0 := by
    have h_eval_map : (P.map (algebraMap ℝ ℂ)).eval (algebraMap ℝ ℂ 4) = algebraMap ℝ ℂ (P.eval 4) := Polynomial.eval_map_apply (algebraMap ℝ ℂ) 4
    have h_four : algebraMap ℝ ℂ 4 = 4 := rfl
    rw [← h_four, h_eval_map]
    simp [hP4]
  have h_res := complex_poly_roots_ge_5_4 (P.map (algebraMap ℝ ℂ)).natDegree (P.map (algebraMap ℝ ℂ)) rfl hroots hP4_re
  have h_eval_map_5 : (P.map (algebraMap ℝ ℂ)).eval (algebraMap ℝ ℂ 5) = algebraMap ℝ ℂ (P.eval 5) := Polynomial.eval_map_apply (algebraMap ℝ ℂ) 5
  have h_eval_map_4 : (P.map (algebraMap ℝ ℂ)).eval (algebraMap ℝ ℂ 4) = algebraMap ℝ ℂ (P.eval 4) := Polynomial.eval_map_apply (algebraMap ℝ ℂ) 4
  have h_five : algebraMap ℝ ℂ 5 = 5 := rfl
  have h_four : algebraMap ℝ ℂ 4 = 4 := rfl
  rw [← h_five, h_eval_map_5] at h_res
  rw [← h_four, h_eval_map_4] at h_res
  simp at h_res
  exact h_res


lemma complex_poly_roots_ge_9_16 (n : ℕ) :
    ∀ (P : Polynomial ℂ) (hdeg : P.natDegree = n)
      (hroots : ∀ z : ℂ, eval z P = 0 → z.im = 0 ∧ z.re ∈ Set.Icc 0 1)
      (hP9 : (eval 9 P).re > 0),
      (eval 16 P).re ≥ (16 / 9) ^ P.natDegree * (eval 9 P).re := by
  induction' n with n ih
  · intro P hdeg _ _
    have hp0 : P.natDegree = 0 := hdeg
    have h_eq : P = C (coeff P 0) := eq_C_of_natDegree_eq_zero hp0
    rw [h_eq]
    simp
  · intro P hdeg hroots hP9
    have hp_pos : P.degree ≠ 0 := by
      intro h_zero
      have h_nat : P.natDegree = 0 := natDegree_eq_zero_iff_degree_le_zero.mpr (le_of_eq h_zero)
      omega
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_root P hp_pos
    have h_root_P : eval z P = 0 := hz
    have h_z_prop := hroots z h_root_P
    have h_z_im : z.im = 0 := h_z_prop.1
    have h_z_re : z.re ∈ Set.Icc 0 1 := h_z_prop.2
    have h_eq_z : z = (z.re : ℂ) := by
      apply Complex.ext
      · rfl
      · exact h_z_im
    have h_div : X - C z ∣ P := dvd_iff_isRoot.mpr hz
    obtain ⟨Q, hQ⟩ := h_div
    have hQ_ne : Q ≠ 0 := by
      intro h_zero
      rw [h_zero, mul_zero] at hQ
      rw [hQ] at hdeg
      simp only [natDegree_zero] at hdeg
      omega
    have h_X_cz_ne : X - C z ≠ 0 := by
      intro h_zero
      have h_deg : (X - C z).natDegree = 1 := natDegree_X_sub_C z
      rw [h_zero] at h_deg
      simp only [natDegree_zero] at h_deg
      omega
    have h_nat_mul : P.natDegree = (X - C z).natDegree + Q.natDegree := by
      rw [hQ]
      exact natDegree_mul h_X_cz_ne hQ_ne
    have h_deg_Q : Q.natDegree = n := by
      rw [natDegree_X_sub_C] at h_nat_mul
      omega
    have hroots_Q : ∀ w : ℂ, eval w Q = 0 → w.im = 0 ∧ w.re ∈ Set.Icc 0 1 := by
      intro w hw
      have h_eval : eval w P = 0 := by
        rw [hQ]
        simp only [eval_mul, hw, mul_zero]
      exact hroots w h_eval
    have h_eval9_X_cz : eval 9 (X - C z) = 9 - z := by simp only [eval_sub, eval_X, eval_C]
    have h_eval16_X_cz : eval 16 (X - C z) = 16 - z := by simp only [eval_sub, eval_X, eval_C]
    have h_factor9_pos : 9 - z.re > 0 := by
      rcases h_z_re with ⟨h1, h2⟩
      linarith
    have h_factor16_pos : 16 - z.re > 0 := by
      rcases h_z_re with ⟨h1, h2⟩
      linarith
    have h_eval9_P : eval 9 P = eval 9 (X - C z) * eval 9 Q := by rw [hQ, eval_mul]
    have h_eval9_P_re : (eval 9 P).re = (9 - z.re) * (eval 9 Q).re := by
      rw [h_eval9_P, h_eval9_X_cz, h_eq_z]
      simp [Complex.mul_re]
    have hQ9 : (eval 9 Q).re > 0 := by
      have : (eval 9 P).re > 0 := hP9
      rw [h_eval9_P_re] at this
      exact pos_of_mul_pos_right this (by linarith)
    have ih_Q := ih Q h_deg_Q hroots_Q hQ9
    have h_eval16_P : eval 16 P = eval 16 (X - C z) * eval 16 Q := by rw [hQ, eval_mul]
    have h_eval16_P_re : (eval 16 P).re = (16 - z.re) * (eval 16 Q).re := by
      rw [h_eval16_P, h_eval16_X_cz, h_eq_z]
      simp [Complex.mul_re]
    have h_mul_le : (16 - z.re) * ((16 / 9) ^ Q.natDegree * (eval 9 Q).re) ≤ (16 - z.re) * (eval 16 Q).re := by
      have h_factor16_nonneg : 16 - z.re ≥ 0 := by linarith
      nlinarith
    have h_ineq_z : (16 / 9) * (9 - z.re) ≤ 16 - z.re := by
      rcases h_z_re with ⟨h1, h2⟩
      linarith
    have h_factor_le : ((16 / 9) * (9 - z.re)) * ((16 / 9) ^ Q.natDegree * (eval 9 Q).re) ≤ (16 - z.re) * ((16 / 9) ^ Q.natDegree * (eval 9 Q).re) := by
      have h_nonneg : (16 / 9 : ℝ) ^ Q.natDegree * (eval 9 Q).re ≥ 0 := by
        have h_pow : (16 / 9 : ℝ) ^ Q.natDegree ≥ 0 := by positivity
        have hQ9_ge : (eval 9 Q).re ≥ 0 := by linarith
        positivity
      nlinarith
    have h_trans : ((16 / 9) * (9 - z.re)) * ((16 / 9) ^ Q.natDegree * (eval 9 Q).re) ≤ (eval 16 P).re := by
      rw [h_eval16_P_re]
      linarith
    have h_simpl : ((16 / 9) * (9 - z.re)) * ((16 / 9) ^ Q.natDegree * (eval 9 Q).re) = (16 / 9) ^ P.natDegree * (eval 9 P).re := by
      rw [hdeg]
      rw [h_eval9_P_re]
      rw [h_deg_Q]
      ring
    rw [h_simpl] at h_trans
    exact h_trans

lemma real_poly_roots_ge_9_16 (P : Polynomial ℝ)
    (hroots : ∀ z : ℂ, (P.map (algebraMap ℝ ℂ)).eval z = 0 → z.im = 0 ∧ z.re ∈ Set.Icc 0 1)
    (hP9 : P.eval 9 > 0) :
    P.eval 16 ≥ (16 / 9) ^ P.natDegree * P.eval 9 := by
  have h_comp : (P.map (algebraMap ℝ ℂ)).natDegree = P.natDegree := natDegree_map (algebraMap ℝ ℂ)
  have hP9_re : (eval 9 (P.map (algebraMap ℝ ℂ))).re > 0 := by
    have h_eval_map : (P.map (algebraMap ℝ ℂ)).eval (algebraMap ℝ ℂ 9) = algebraMap ℝ ℂ (P.eval 9) := Polynomial.eval_map_apply (algebraMap ℝ ℂ) 9
    have h_nine : algebraMap ℝ ℂ 9 = 9 := rfl
    rw [← h_nine, h_eval_map]
    simp [hP9]
  have h_res := complex_poly_roots_ge_9_16 (P.map (algebraMap ℝ ℂ)).natDegree (P.map (algebraMap ℝ ℂ)) rfl hroots hP9_re
  rw [h_comp] at h_res
  have h_eval_map_16 : (P.map (algebraMap ℝ ℂ)).eval (algebraMap ℝ ℂ 16) = algebraMap ℝ ℂ (P.eval 16) := Polynomial.eval_map_apply (algebraMap ℝ ℂ) 16
  have h_eval_map_9 : (P.map (algebraMap ℝ ℂ)).eval (algebraMap ℝ ℂ 9) = algebraMap ℝ ℂ (P.eval 9) := Polynomial.eval_map_apply (algebraMap ℝ ℂ) 9
  have h_sixteen : algebraMap ℝ ℂ 16 = 16 := rfl
  have h_nine : algebraMap ℝ ℂ 9 = 9 := rfl
  rw [← h_sixteen, h_eval_map_16] at h_res
  rw [← h_nine, h_eval_map_9] at h_res
  simp at h_res
  exact h_res


/--
We have mathematically disproved Peter Bala's conjecture for A103885.
Specifically, for m = 17:
1. The unique symmetric polynomial P of degree 34 satisfying the recurrence relation has complex roots.
-/

lemma a_51_pos : (A103885 51 : ℝ) > 0 := by
  have : A103885 51 > 0 := by rw [a_51_eq]; decide
  exact Nat.cast_pos.mpr this

lemma a_68_pos : (A103885 68 : ℝ) > 0 := by
  have : A103885 68 > 0 := by rw [a_68_eq]; decide
  exact Nat.cast_pos.mpr this

lemma prod_factor_plus_17_3_pos : (prod_factor_plus_nat 17 3 : ℝ) > 0 := by
  have : prod_factor_plus_nat 17 3 > 0 := by rw [prod_factor_plus_17_3_eq]; decide
  exact Nat.cast_pos.mpr this


/--
We have mathematically disproved Peter Bala's conjecture for A103885.
Specifically, for m = 17:
1. The unique symmetric polynomial P of degree 34 satisfying the recurrence relation has complex roots.
-/
theorem oeis_a103885_conjecture_0.disproof :
    ¬ (∀ (m : ℕ) (hm : 1 ≤ m),
      ∃ (P Q : Polynomial ℝ),
        -- P and Q have degree 2m
        P.degree = (2 * m : ℕ) ∧ Q.degree = (2 * m : ℕ) ∧
        -- The recurrence relation holds for all n >= 1
        (∀ (n : ℕ) (hn : 1 ≤ n),
          (prod_factor_plus m n * P.eval (n : ℝ)) * (A103885_subsequence_real m (n + 1)) +

          ((-1 : ℝ) ^ m * prod_factor_minus m n * P.eval (-(n : ℝ))) * (A103885_subsequence_real m (n - 1)) =

          (Q.eval ((n : ℝ)^2)) * (A103885_subsequence_real m n)) ∧

        -- P symmetry: P(x) = P(1-x)
        (∀ x : ℝ, P.eval x = P.eval (1 - x)) ∧

        -- P has real zeros in [0, 1]: all complex zeros are real and in [0, 1]
        (∀ z : ℂ, (P.map (algebraMap ℝ ℂ)).eval z = 0 → z.im = 0 ∧ z.re ∈ (Set.Icc 0 1)) ∧

        -- Q zero properties: The zeros of Q(x^2) are real and in [-1, 1].
        (∀ z : ℂ, (Q.map (algebraMap ℝ ℂ)).eval (z^2) = 0 → z.im = 0 ∧ z.re ∈ (Set.Icc (-1) 1))) := by
  intro h
  obtain ⟨P, Q, hdegP, hdegQ, hrec, hsymm, hrootsP, hrootsQ⟩ := h 17 (by decide)
  have h_minus_1 : prod_factor_minus 17 1 = 0 := prod_factor_minus_one_eq_zero 17 (by decide)
  have hrec1 := hrec 1 (by decide)
  push_cast at hrec1
  rw [h_minus_1] at hrec1
  have h_zero : (-1 : ℝ) ^ 17 * 0 * P.eval (-1) * A103885_subsequence_real 17 0 = 0 := by ring
  rw [h_zero, add_zero] at hrec1
  have h_symm1 : P.eval 1 = P.eval 0 := by
    have := hsymm 1
    rw [this]
    ring_nf
  rw [h_symm1] at hrec1
  have h_plus_1 : prod_factor_plus 17 1 = (prod_factor_plus_nat 17 1 : ℝ) := prod_factor_plus_eq_nat 17 1
  rw [h_plus_1] at hrec1
  dsimp [A103885_subsequence_real] at hrec1
  rw [prod_factor_plus_17_1_eq, a_34_eq, a_17_eq] at hrec1
  ring_nf at hrec1
  have h_eval_map (x : ℝ) : (P.map (algebraMap ℝ ℂ)).eval (algebraMap ℝ ℂ x) = algebraMap ℝ ℂ (P.eval x) :=
    Polynomial.eval_map_apply (algebraMap ℝ ℂ) x
  have h_ne_zero {x : ℝ} (hx : x < 0 ∨ 1 < x) : P.eval x ≠ 0 := by
    intro h_eval
    have h_roots := hrootsP (algebraMap ℝ ℂ x)
    have h_eval_complex : (P.map (algebraMap ℝ ℂ)).eval (algebraMap ℝ ℂ x) = 0 := by
      rw [h_eval_map]
      rw [h_eval]
      exact RingHom.map_zero (algebraMap ℝ ℂ)
    have h_res := h_roots h_eval_complex
    have h_re : (algebraMap ℝ ℂ x).re = x := rfl
    have h_in_Icc := h_res.2
    rw [h_re] at h_in_Icc
    rcases h_in_Icc with ⟨hx_ge, hx_le⟩
    rcases hx with hx1 | hx2
    · linarith
    · linarith
  have h_eval_map_Q (x : ℝ) : (Q.map (algebraMap ℝ ℂ)).eval (algebraMap ℝ ℂ x) = algebraMap ℝ ℂ (Q.eval x) :=
    Polynomial.eval_map_apply (algebraMap ℝ ℂ) x
  have h_q_ge_zero {y : ℝ} (hy : y < 0) : Q.eval y ≠ 0 := by
    intro h_eval
    let z : ℂ := Complex.I * (Real.sqrt (-y) : ℂ)
    have h_z_sq : z^2 = algebraMap ℝ ℂ y := by
      dsimp [z]
      have h1 : (Complex.I * (Real.sqrt (-y) : ℂ)) ^ 2 = Complex.I ^ 2 * (Real.sqrt (-y) : ℂ) ^ 2 := by ring
      rw [h1, Complex.I_sq]
      have h2 : Real.sqrt (-y) ^ 2 = -y := Real.sq_sqrt (by linarith)
      have h3 : ((Real.sqrt (-y) : ℂ) ^ 2) = (Real.sqrt (-y) ^ 2 : ℝ) := by push_cast; rfl
      rw [h3, h2]
      push_cast
      ring
    have h_roots := hrootsQ z
    have h_eval_complex : (Q.map (algebraMap ℝ ℂ)).eval (z^2) = 0 := by
      rw [h_z_sq]
      rw [h_eval_map_Q]
      rw [h_eval]
      exact RingHom.map_zero (algebraMap ℝ ℂ)
    have h_res := h_roots h_eval_complex
    have h_z_im : z.im = Real.sqrt (-y) := by
      dsimp [z]
      simp
    have h_im_zero := h_res.1
    rw [h_z_im] at h_im_zero
    have h_pos : -y > 0 := by linarith
    have h_sqrt_ne_zero : Real.sqrt (-y) ≠ 0 := Real.sqrt_ne_zero'.mpr h_pos
    exact h_sqrt_ne_zero h_im_zero
  have h_q_le_one {y : ℝ} (hy : y > 1) : Q.eval y ≠ 0 := by
    intro h_eval
    let z : ℂ := (Real.sqrt y : ℂ)
    have h_z_sq : z^2 = algebraMap ℝ ℂ y := by
      dsimp [z]
      have h3 : ((Real.sqrt y : ℂ) ^ 2) = (Real.sqrt y ^ 2 : ℝ) := by push_cast; rfl
      rw [h3, Real.sq_sqrt (by linarith)]
    have h_roots := hrootsQ z
    have h_eval_complex : (Q.map (algebraMap ℝ ℂ)).eval (z^2) = 0 := by
      rw [h_z_sq]
      rw [h_eval_map_Q]
      rw [h_eval]
      exact RingHom.map_zero (algebraMap ℝ ℂ)
    have h_res := h_roots h_eval_complex
    have h_re : z.re = Real.sqrt y := rfl
    have h_in_Icc := h_res.2
    rw [h_re] at h_in_Icc
    have h_sqrt_gt1 : 1 < Real.sqrt y := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_lt_sqrt (by linarith) hy
    linarith [h_in_Icc.1, h_in_Icc.2]

  have hP4_ne : P.eval 4 ≠ 0 := h_ne_zero (Or.inr (by norm_num))
  obtain ⟨P', Q', hdegP', hdegQ', hrec', hsymm', hrootsP', hrootsQ', hP4_gt⟩ :
      ∃ (P' Q' : Polynomial ℝ),
        P'.degree = (34 : ℕ) ∧ Q'.degree = (34 : ℕ) ∧
        (∀ (n : ℕ) (hn : 1 ≤ n),
          (prod_factor_plus 17 n * P'.eval (n : ℝ)) * (A103885_subsequence_real 17 (n + 1)) +
          ((-1 : ℝ) ^ 17 * prod_factor_minus 17 n * P'.eval (-(n : ℝ))) * (A103885_subsequence_real 17 (n - 1)) =
          (Q'.eval ((n : ℝ)^2)) * (A103885_subsequence_real 17 n)) ∧
        (∀ x : ℝ, P'.eval x = P'.eval (1 - x)) ∧
        (∀ z : ℂ, (P'.map (algebraMap ℝ ℂ)).eval z = 0 → z.im = 0 ∧ z.re ∈ Set.Icc 0 1) ∧
        (∀ z : ℂ, (Q'.map (algebraMap ℝ ℂ)).eval (z^2) = 0 → z.im = 0 ∧ z.re ∈ Set.Icc (-1) 1) ∧
        P'.eval 4 > 0 := by
    by_cases hP4_gt : P.eval 4 > 0
    · exact ⟨P, Q, hdegP, hdegQ, hrec, hsymm, hrootsP, hrootsQ, hP4_gt⟩
    · have hP4_le : P.eval 4 ≤ 0 := by linarith
      have hP4_lt : P.eval 4 < 0 := lt_of_le_of_ne hP4_le hP4_ne
      refine ⟨-P, -Q, by rw [degree_neg, hdegP], by rw [degree_neg, hdegQ], ?_,
        by intro x; rw [eval_neg, eval_neg, hsymm],
        by intro z hz; exact hrootsP z (by rw [Polynomial.map_neg, eval_neg, neg_eq_zero] at hz; exact hz),
        by intro z hz; exact hrootsQ z (by rw [Polynomial.map_neg, eval_neg, neg_eq_zero] at hz; exact hz),
        by rw [eval_neg]; linarith⟩
      intro n hn
      have hrec_n := hrec n hn
      simp only [eval_neg]
      linarith

  have h_nat : P'.natDegree = 34 := by
    have hdeg : P'.degree = (34 : ℕ) := hdegP'
    exact natDegree_eq_of_degree_eq_some hdeg

  have h_ne_zero' {x : ℝ} (hx : x < 0 ∨ 1 < x) : P'.eval x ≠ 0 := by
    intro h_eval
    have h_eval_map (x : ℝ) : (P'.map (algebraMap ℝ ℂ)).eval (algebraMap ℝ ℂ x) = algebraMap ℝ ℂ (P'.eval x) :=
      Polynomial.eval_map_apply (algebraMap ℝ ℂ) x
    have h_roots := hrootsP' (algebraMap ℝ ℂ x)
    have h_eval_complex : (P'.map (algebraMap ℝ ℂ)).eval (algebraMap ℝ ℂ x) = 0 := by
      rw [h_eval_map]
      rw [h_eval]
      exact RingHom.map_zero (algebraMap ℝ ℂ)
    have h_res := h_roots h_eval_complex
    have h_re : (algebraMap ℝ ℂ x).re = x := rfl
    have h_in_Icc := h_res.2
    rw [h_re] at h_in_Icc
    rcases h_in_Icc with ⟨hx_ge, hx_le⟩
    rcases hx with hx1 | hx2
    · linarith
    · linarith

  have h_roots_ge := real_poly_roots_ge P' hrootsP' hP4_gt
  rw [h_nat] at h_roots_ge

  have hQ4_ne : Q'.eval 4 ≠ 0 := by
    intro h_zero
    have h_eval : (Q'.map (algebraMap ℝ ℂ)).eval ((2 : ℂ) ^ 2) = 0 := by
      rw [show (2 : ℂ) ^ 2 = algebraMap ℝ ℂ 4 by norm_num]
      rw [Polynomial.eval_map_apply, h_zero, map_zero]
    have h_roots := hrootsQ' 2 h_eval
    have h_re : (2 : ℂ).re ∈ Set.Icc (-1) 1 := h_roots.2
    norm_num at h_re

  have h_q_le_one' (y : ℝ) (hy : y > 1) : Q'.eval y ≠ 0 := by
    intro h_eval
    let z : ℂ := (Real.sqrt y : ℂ)
    have h_z_sq : z^2 = algebraMap ℝ ℂ y := by
      dsimp [z]
      have h3 : ((Real.sqrt y : ℂ) ^ 2) = (Real.sqrt y ^ 2 : ℝ) := by push_cast; rfl
      rw [h3, Real.sq_sqrt (by linarith)]
    have h_roots := hrootsQ' z
    have h_eval_complex : (Q'.map (algebraMap ℝ ℂ)).eval (z^2) = 0 := by
      rw [h_z_sq]
      rw [Polynomial.eval_map_apply]
      rw [h_eval]
      exact RingHom.map_zero (algebraMap ℝ ℂ)
    have h_res := h_roots h_eval_complex
    have h_re : z.re = Real.sqrt y := rfl
    have h_in_Icc := h_res.2
    rw [h_re] at h_in_Icc
    have h_sqrt_gt1 : 1 < Real.sqrt y := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_lt_sqrt (by linarith) hy
    linarith [h_in_Icc.1, h_in_Icc.2]

  have hQ4_gt : Q'.eval 4 > 0 := by
    by_contra! hQ4_le
    have hQ4_lt : Q'.eval 4 < 0 := lt_of_le_of_ne hQ4_le hQ4_ne
    have h_neg_q_pos : (-Q').eval 4 > 0 := by
      rw [eval_neg]
      linarith
    have h_neg_q_le_one (y : ℝ) (hy : y > 1) : (-Q').eval y ≠ 0 := by
      rw [eval_neg]
      intro h_zero_val
      have : Q'.eval y = 0 := by linarith
      exact h_q_le_one' y hy this
    have h_neg_q_9_pos := sign_Q9_of_Q4_pos (-Q') h_neg_q_le_one h_neg_q_pos
    have hQ9_lt : Q'.eval 9 < 0 := by
      rw [eval_neg] at h_neg_q_9_pos
      linarith

    have hrec3 := hrec' 3 (by decide)
    norm_num at hrec3
    have h_symm3 : P'.eval (-3) = P'.eval 4 := by
      have := hsymm' (-3)
      ring_nf at this
      exact this
    rw [h_symm3] at hrec3
    have h_plus_3 : prod_factor_plus 17 3 = (prod_factor_plus_nat 17 3 : ℝ) := prod_factor_plus_eq_nat 17 3
    have h_minus_3 : prod_factor_minus 17 3 = (prod_factor_minus_nat 17 3 : ℝ) := prod_factor_minus_eq_nat 17 3 (by decide)
    rw [h_plus_3, h_minus_3] at hrec3
    dsimp [A103885_subsequence_real] at hrec3

    have h_sub_lt_zero : (prod_factor_plus_nat 17 3 : ℝ) * P'.eval 3 * (A103885 68 : ℝ) - (prod_factor_minus_nat 17 3 : ℝ) * P'.eval 4 * (A103885 34 : ℝ) < 0 := by
      have : Q'.eval 9 * (A103885 51 : ℝ) < 0 := mul_neg_of_neg_of_pos hQ9_lt a_51_pos
      linarith [hrec3]

    have h_bound : (prod_factor_plus_nat 17 3 : ℝ) * ((2 / 3) ^ 34 * P'.eval 4) * (A103885 68 : ℝ) - (prod_factor_minus_nat 17 3 : ℝ) * P'.eval 4 * (A103885 34 : ℝ) < 0 := by
      have h_pos_coeff : (prod_factor_plus_nat 17 3 : ℝ) * (A103885 68 : ℝ) > 0 := mul_pos prod_factor_plus_17_3_pos a_68_pos
      have h_mul : (prod_factor_plus_nat 17 3 : ℝ) * P'.eval 3 * (A103885 68 : ℝ) ≥ (prod_factor_plus_nat 17 3 : ℝ) * ((2 / 3) ^ 34 * P'.eval 4) * (A103885 68 : ℝ) := by
        calc (prod_factor_plus_nat 17 3 : ℝ) * P'.eval 3 * (A103885 68 : ℝ)
            = ((prod_factor_plus_nat 17 3 : ℝ) * (A103885 68 : ℝ)) * P'.eval 3 := by ring
          _ ≥ ((prod_factor_plus_nat 17 3 : ℝ) * (A103885 68 : ℝ)) * ((2 / 3) ^ 34 * P'.eval 4) :=
            mul_le_mul_of_nonneg_left h_roots_ge (by linarith [h_pos_coeff])
          _ = (prod_factor_plus_nat 17 3 : ℝ) * ((2 / 3) ^ 34 * P'.eval 4) * (A103885 68 : ℝ) := by ring
      linarith

    have h_final : (prod_factor_plus_nat 17 3 : ℝ) * (2 / 3) ^ 34 * P'.eval 4 * (A103885 68 : ℝ) < (prod_factor_minus_nat 17 3 : ℝ) * P'.eval 4 * (A103885 34 : ℝ) := by
      linarith [h_bound]

    rw [prod_factor_plus_17_3_eq, prod_factor_minus_17_3_eq, a_68_eq, a_34_eq] at h_final
    norm_num at h_final
    linarith

  have h_q_roots_Icc := Q_roots_in_Icc Q' hrootsQ'
  have h_natQ : Q'.natDegree = 34 := by
    have hdeg : Q'.degree = (34 : ℕ) := hdegQ'
    exact natDegree_eq_of_degree_eq_some hdeg

  have h_q_roots_ge := real_poly_roots_ge_4_9 Q' h_q_roots_Icc hQ4_gt
  rw [h_natQ] at h_q_roots_ge
  have h_q_roots_le := real_poly_roots_le_4_9 Q' h_q_roots_Icc hQ4_gt
  rw [h_natQ] at h_q_roots_le

  have hrec1' := hrec' 1 (by decide)
  push_cast at hrec1'
  rw [prod_factor_minus_one_eq_zero 17 (by decide)] at hrec1'
  have h_zero' : (-1 : ℝ) ^ 17 * 0 * P'.eval (-1) * A103885_subsequence_real 17 0 = 0 := by ring
  rw [h_zero', add_zero] at hrec1'
  have h_symm1' : P'.eval 1 = P'.eval 0 := by
    have := hsymm' 1
    rw [this]
    ring_nf
  rw [h_symm1'] at hrec1'
  have h_plus_1' : prod_factor_plus 17 1 = (prod_factor_plus_nat 17 1 : ℝ) := prod_factor_plus_eq_nat 17 1
  rw [h_plus_1'] at hrec1'
  dsimp [A103885_subsequence_real] at hrec1'

  have hrec2 := hrec' 2 (by decide)
  norm_num at hrec2
  have h_symm2 : P'.eval (-2) = P'.eval 3 := by
    have := hsymm' (-2)
    ring_nf at this
    exact this
  rw [h_symm2] at hrec2
  have h_plus_2 : prod_factor_plus 17 2 = (prod_factor_plus_nat 17 2 : ℝ) := prod_factor_plus_eq_nat 17 2
  have h_minus_2 : prod_factor_minus 17 2 = (prod_factor_minus_nat 17 2 : ℝ) := prod_factor_minus_eq_nat 17 2 (by decide)
  rw [h_plus_2, h_minus_2] at hrec2
  dsimp [A103885_subsequence_real] at hrec2

  -- We have P'(3) > 0 because of P'(3) >= (2/3)^34 * P'(4) > 0
  have hP3_gt : P'.eval 3 > 0 := by
    have h_pos_coeff : (2 / 3 : ℝ) ^ 34 > 0 := by positivity
    have : (2 / 3 : ℝ) ^ 34 * P'.eval 4 > 0 := mul_pos h_pos_coeff hP4_gt
    linarith [h_roots_ge]

  have hP2_ge_half := real_poly_roots_ge_2_3_half P' hrootsP' hP3_gt
  rw [h_nat] at hP2_ge_half

  have hp2_gt : P'.eval 2 > 0 := by
    have h_pos_coeff : (1 / 2 : ℝ) ^ 34 > 0 := by positivity
    linarith [hP2_ge_half, hP3_gt]

  have hp2_ge := real_poly_roots_ge_1_2 P' hrootsP' hp2_gt
  rw [h_nat] at hp2_ge
  rw [h_symm1'] at hp2_ge

  have hq4_ge := real_poly_roots_ge_1_4 Q' h_q_roots_Icc hQ4_gt
  rw [h_natQ] at hq4_ge

  rw [show (1 : ℝ)^2 = 1 by norm_num] at hrec1'
  rw [prod_factor_plus_17_1_eq, a_34_eq, a_17_eq] at hrec1'

  have hp2_le_four := real_poly_roots_le_2_4 P' hrootsP' hP4_gt
  rw [h_nat] at hp2_le_four

  have hp2_le_three : P'.eval 2 ≤ (3 / 4) ^ 34 * P'.eval 3 := by linarith [hp2_le_four, h_roots_ge]

  have hrec1_vars := hrec1'
  have hrec2_vars := hrec2

  have h_p2_ge_vars : P'.eval 2 ≥ (2 : ℝ) ^ 34 * P'.eval 0 := hp2_ge
  have h_q4_ge_vars : Q'.eval 4 ≥ (4 : ℝ) ^ 34 * Q'.eval 1 := hq4_ge
  have hp2_le_three_vars : P'.eval 2 ≤ (3 / 4) ^ 34 * P'.eval 3 := hp2_le_three
  have h_p3_ge : P'.eval 3 ≥ 0 := by linarith [hP3_gt]

  rw [prod_factor_plus_17_2_eq, prod_factor_minus_17_2_eq,
      a_17_eq, a_34_eq, a_51_eq] at hrec2_vars

  push_cast at hrec1_vars hrec2_vars
  ring_nf at hrec1_vars hrec2_vars h_p2_ge_vars h_q4_ge_vars hp2_le_three_vars
  linarith [hrec1_vars, hrec2_vars, h_p2_ge_vars, h_q4_ge_vars, hp2_le_three_vars, h_p3_ge]
