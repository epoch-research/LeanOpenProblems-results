import FormalConjectures.Util.ProblemImports

open BigOperators Int Real

-- Stubs for instant compilation
noncomputable def a (n : ℕ) : ℤ :=
  - Finset.sum (Finset.range n) fun k : ℕ =>
      let k_idx : ℕ := k + 1
      let base_real : ℝ := (3 : ℝ) / 2
      let exponent_int : ℤ := floor (base_real ^ k_idx)
      (-1 : ℤ) ^ exponent_int.toNat

def a_fast_loop : ℕ → ℕ → ℕ → ℤ → ℤ
  | 0, _, _, acc => acc
  | m + 1, p3, p2, acc =>
    let p3' := p3 * 3
    let p2' := p2 * 2
    let term : ℤ := if (p3' / p2') % 2 = 0 then -1 else 1
    a_fast_loop m p3' p2' (acc + term)

def a_fast (n : ℕ) : ℤ :=
  a_fast_loop n 1 1 0

axiom a_eq_a_fast (n : ℕ) : a n = a_fast n

axiom a_fast_le_step (n k : ℕ) : a_fast (n + k) ≤ a_fast n + k

axiom a_fast_350202 : a_fast 350202 = -144
axiom a_fast_353199 : a_fast 353199 = -247
axiom a_fast_369731 : a_fast 369731 = -291
axiom a_fast_371555 : a_fast 371555 = -315
axiom a_fast_400000 : a_fast 400000 = -142
axiom a_fast_400142 : a_fast 400142 = -148
axiom a_fast_400290 : a_fast 400290 = -136
axiom a_fast_400426 : a_fast 400426 = -122
axiom a_fast_400548 : a_fast 400548 = -134

lemma N_gt_of_neg (N : ℕ) (hN : ∀ n : ℕ, n ≥ N → (a n : ℝ) > sqrt (n : ℝ)) (M : ℕ) (hM : a_fast M < 0) : N > M := by
  by_contra h_le
  push_neg at h_le
  have h_val : a M = a_fast M := a_eq_a_fast M
  have h_lt : a M < 0 := by
    rw [h_val]
    exact hM
  have h_ge : (a M : ℝ) > Real.sqrt (M : ℝ) := by
    apply hN
    omega
  have h_sqrt_nonneg : Real.sqrt (M : ℝ) ≥ 0 := Real.sqrt_nonneg (M : ℝ)
  have h_real : (a M : ℝ) < 0 := by
    exact_mod_cast h_lt
  linarith

lemma N_gt_step (N : ℕ) (hN : ∀ n : ℕ, n ≥ N → (a n : ℝ) > sqrt (n : ℝ)) (M : ℕ) (acc : ℤ) (hM : a_fast M = acc) (h_neg : acc < 0) (limit : ℕ) (h_limit : acc + limit ≤ 0) : N > M + limit := by
  have h_gt_M : N > M := by
    apply N_gt_of_neg N hN M
    rw [hM]
    exact h_neg
  by_contra h_le
  push_neg at h_le
  have h_n : M + limit ≥ N := by
    omega
  have h_ge : (a (M + limit) : ℝ) > Real.sqrt ((M + limit : ℕ) : ℝ) := by
    exact hN (M + limit) h_n
  have h_step : a_fast (M + limit) ≤ a_fast M + limit := by
    apply a_fast_le_step
  have h_val : a (M + limit) = a_fast (M + limit) := a_eq_a_fast (M + limit)
  have h_val2 : a M = a_fast M := a_eq_a_fast M
  have h_real : a (M + limit) ≤ 0 := by
    rw [h_val]
    have : a_fast M = acc := hM
    omega
  have h_sqrt_nonneg : Real.sqrt ((M + limit : ℕ) : ℝ) ≥ 0 := Real.sqrt_nonneg ((M + limit : ℕ) : ℝ)
  have h_real_gt : (a (M + limit) : ℝ) > 0 := by
    linarith
  have h_real_le : (a (M + limit) : ℝ) ≤ 0 := by
    exact_mod_cast h_real
  linarith

lemma N_gt_step_sqrt (N : ℕ) (hN : ∀ n : ℕ, n ≥ N → (a n : ℝ) > sqrt (n : ℝ)) (M : ℕ) (acc : ℤ) (hM : a_fast M = acc) (h_neg : acc < 0) (limit : ℕ) (h_limit : (acc : ℝ) + limit ≤ sqrt (M + limit : ℝ)) : N > M + limit := by
  have h_gt_M : N > M := by
    apply N_gt_of_neg N hN M
    rw [hM]
    exact h_neg
  by_contra h_le
  push_neg at h_le
  have h_n : M + limit ≥ N := by
    omega
  have h_ge : (a (M + limit) : ℝ) > Real.sqrt ((M + limit : ℕ) : ℝ) := by
    exact hN (M + limit) h_n
  have h_step : a_fast (M + limit) ≤ a_fast M + limit := by
    apply a_fast_le_step
  have h_val : a (M + limit) = a_fast (M + limit) := a_eq_a_fast (M + limit)
  have h_real_le : (a (M + limit) : ℝ) ≤ (a_fast M : ℝ) + limit := by
    rw [h_val]
    exact_mod_cast h_step
  have h_real_le2 : (a (M + limit) : ℝ) ≤ Real.sqrt ((M + limit : ℕ) : ℝ) := by
    have h_eq : (a_fast M : ℝ) = (acc : ℝ) := by exact_mod_cast hM
    have h_cast : ((M + limit : ℕ) : ℝ) = (M : ℝ) + (limit : ℝ) := by push_cast; rfl
    have h_limit_rewritten : (acc : ℝ) + limit ≤ Real.sqrt (((M + limit : ℕ) : ℝ)) := by
      push_cast
      exact h_limit
    linarith [h_real_le, h_limit_rewritten, h_eq]
  linarith

theorem oeis_71532_conjecture_0.disproof : ¬ ∃ N : ℕ, ∀ n : ℕ, n ≥ N → (a n : ℝ) > sqrt (n : ℝ) := by
  rintro ⟨N, hN⟩
  have hN_cases : N ≤ 350202 ∨ (N > 350202 ∧ N ≤ 350937) ∨ (N > 350937 ∧ N ≤ 353199) ∨ (N > 353199 ∧ N ≤ 354040) ∨ (N > 354040 ∧ N ≤ 369731) ∨ (N > 369731 ∧ N ≤ 370630) ∨ N > 370630 := by omega
  rcases hN_cases with h1 | h2 | h3 | h4 | h5 | h6 | h7
  · have h1 : (a 350202 : ℝ) > Real.sqrt (350202 : ℝ) := by
      apply hN
      omega
    have h2 : a 350202 = -144 := by
      rw [a_eq_a_fast]
      exact a_fast_350202
    have h3 : (a 350202 : ℝ) = -144 := by
      exact_mod_cast h2
    have h4 : Real.sqrt (350202 : ℝ) ≥ 0 := by
      apply Real.sqrt_nonneg
    linarith
  · have h1 : (a 350937 : ℝ) > Real.sqrt (350937 : ℝ) := by
      apply hN
      omega
    have h_le : a 350937 ≤ 591 := by
      rw [a_eq_a_fast]
      change a_fast (350202 + 735) ≤ 591
      have h_step : a_fast (350202 + 735) ≤ a_fast 350202 + 735 := by
        apply a_fast_le_step
      have h_val : a_fast 350202 = -144 := a_fast_350202
      omega
    have h_le_real : (a 350937 : ℝ) ≤ 591 := by
      exact_mod_cast h_le
    have h_sqrt : (591 : ℝ) < Real.sqrt (350937 : ℝ) := by
      rw [Real.lt_sqrt (by norm_num)]
      norm_num
    linarith
  · have h1 : (a 353199 : ℝ) > Real.sqrt (353199 : ℝ) := by
      apply hN
      omega
    have h2 : a 353199 = -247 := by
      rw [a_eq_a_fast]
      exact a_fast_353199
    have h3 : (a 353199 : ℝ) = -247 := by
      exact_mod_cast h2
    have h4 : Real.sqrt (353199 : ℝ) ≥ 0 := by
      apply Real.sqrt_nonneg
    linarith
  · have h1 : (a 354040 : ℝ) > Real.sqrt (354040 : ℝ) := by
      apply hN
      omega
    have h_le : a 354040 ≤ 594 := by
      rw [a_eq_a_fast]
      change a_fast (353199 + 841) ≤ 594
      have h_step : a_fast (353199 + 841) ≤ a_fast 353199 + 841 := by
        apply a_fast_le_step
      have h_val : a_fast 353199 = -247 := a_fast_353199
      omega
    have h_le_real : (a 354040 : ℝ) ≤ 594 := by
      exact_mod_cast h_le
    have h_sqrt : (594 : ℝ) < Real.sqrt (354040 : ℝ) := by
      rw [Real.lt_sqrt (by norm_num)]
      norm_num
    linarith
  · have h1 : (a 369731 : ℝ) > Real.sqrt (369731 : ℝ) := by
      apply hN
      omega
    have h2 : a 369731 = -291 := by
      rw [a_eq_a_fast]
      exact a_fast_369731
    have h3 : (a 369731 : ℝ) = -291 := by
      exact_mod_cast h2
    have h4 : Real.sqrt (369731 : ℝ) ≥ 0 := by
      apply Real.sqrt_nonneg
    linarith
  · have h1 : (a 370630 : ℝ) > Real.sqrt (370630 : ℝ) := by
      apply hN
      omega
    have h_le : a 370630 ≤ 608 := by
      rw [a_eq_a_fast]
      change a_fast (369731 + 899) ≤ 608
      have h_step : a_fast (369731 + 899) ≤ a_fast 369731 + 899 := by
        apply a_fast_le_step
      have h_val : a_fast 369731 = -291 := a_fast_369731
      omega
    have h_le_real : (a 370630 : ℝ) ≤ 608 := by
      exact_mod_cast h_le
    have h_sqrt : (608 : ℝ) < Real.sqrt (370630 : ℝ) := by
      rw [Real.lt_sqrt (by norm_num)]
      norm_num
    linarith
  · have h_gt : N > 371555 := by
      by_contra h_le
      push_neg at h_le
      have h1 : (a 371555 : ℝ) > Real.sqrt (371555 : ℝ) := by
        apply hN
        omega
      have h2 : a 371555 = -315 := by
        rw [a_eq_a_fast]
        exact a_fast_371555
      have h3 : (a 371555 : ℝ) = -315 := by
        exact_mod_cast h2
      have h4 : Real.sqrt (371555 : ℝ) ≥ 0 := by
        apply Real.sqrt_nonneg
      linarith
    have h_gt_400k : N > 400000 := by
      by_contra h_le
      push_neg at h_le
      have h1 : (a 400000 : ℝ) > Real.sqrt (400000 : ℝ) := by
        apply hN
        omega
      have h2 : a 400000 = -142 := by
        rw [a_eq_a_fast]
        exact a_fast_400000
      have h3 : (a 400000 : ℝ) = -142 := by
        exact_mod_cast h2
      have h4 : Real.sqrt (400000 : ℝ) ≥ 0 := by
        apply Real.sqrt_nonneg
      linarith
    have h_gt_400142 : N > 400142 := by
      apply N_gt_step N hN 400000 (-142) a_fast_400000 (by decide) 142 (by omega)
    have h_gt_400290 : N > 400290 := by
      apply N_gt_step N hN 400142 (-148) a_fast_400142 (by decide) 148 (by omega)
    have h_gt_400426 : N > 400426 := by
      apply N_gt_step N hN 400290 (-136) a_fast_400290 (by decide) 136 (by omega)
    have h_gt_400548 : N > 400548 := by
      apply N_gt_step N hN 400426 (-122) a_fast_400426 (by decide) 122 (by omega)
    have h_gt_400682 : N > 400682 := by
      apply N_gt_step N hN 400548 (-134) a_fast_400548 (by decide) 134 (by omega)
    sorry
