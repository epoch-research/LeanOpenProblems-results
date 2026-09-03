import Submission.HyperbolicLargeSieve

/-!
# Character-dependent hyperbolic cutoffs

The cutoff may be chosen independently for every character. A pointwise
Fourier coefficient envelope makes the logarithmic loss uniform in these
choices; this is stronger than a fixed-cutoff estimate.
-/

open scoped BigOperators
open Finset

namespace Erdos821.AnalyticSieve

lemma weighted_norm_variable_combination_le {ι κ : Type*}
    (I : Finset ι) (J : Finset κ) (w : ι → ℝ) (c : ι → κ → ℂ) (F : κ → ι → ℂ)
    (η : κ → ℝ) (hw : ∀ i ∈ I, 0 ≤ w i) (hη : ∀ j ∈ J, 0 ≤ η j)
    (hc : ∀ i ∈ I, ∀ j ∈ J, ‖c i j‖ ≤ η j) (D : ℝ)
    (hF : ∀ j ∈ J, (∑ i ∈ I, w i * ‖F j i‖) ≤ D) :
    (∑ i ∈ I, w i * ‖∑ j ∈ J, c i j * F j i‖) ≤ (∑ j ∈ J, η j) * D := by
  calc
    _ ≤ ∑ i ∈ I, w i * ∑ j ∈ J, η j * ‖F j i‖ := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_left _ (hw i hi)
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hc i hi j hj) (norm_nonneg _)
    _ = ∑ j ∈ J, η j * ∑ i ∈ I, w i * ‖F j i‖ := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ ∑ j ∈ J, η j * D :=
      Finset.sum_le_sum (fun j hj => mul_le_mul_of_nonneg_left (hF j hj) (hη j hj))
    _ = _ := by rw [Finset.sum_mul]

section Fourier

variable {W : ℕ} [NeZero W]

noncomputable def fourierEnvelope (r : ZMod W) : ℝ :=
  if r.val = 0 then 1 else
    1 / 2 * ((r.val : ℝ)⁻¹ + ((W - r.val : ℕ) : ℝ)⁻¹)

omit [NeZero W] in
lemma fourierEnvelope_nonneg (r : ZMod W) : 0 ≤ fourierEnvelope r := by
  unfold fourierEnvelope
  split_ifs <;> positivity

lemma norm_interval_fourier_le_envelope (T : ℕ) (hT : T ≤ W) (r : ZMod W) :
    ‖normalizedFourier (intervalIndicator T) r‖ ≤ fourierEnvelope (-r) := by
  have hWpos : (0 : ℝ) < W := by exact_mod_cast (NeZero.pos W)
  rw [normalizedFourier, norm_mul, norm_inv, Complex.norm_natCast, dft_intervalIndicator T hT]
  unfold fourierEnvelope
  split_ifs with h
  · rw [h]
    simp only [Nat.cast_zero, zero_div, intervalWaveSum, wave, Complex.ofReal_zero,
      mul_zero, Complex.exp_zero, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      mul_one, Complex.norm_natCast]
    rw [mul_comm, ← div_eq_mul_inv]
    exact (div_le_one hWpos).mpr (by exact_mod_cast hT)
  · calc
      _ ≤ (W : ℝ)⁻¹ * ((W : ℝ) / 2 *
          (((-r).val : ℝ)⁻¹ + ((W - (-r).val : ℕ) : ℝ)⁻¹)) :=
        mul_le_mul_of_nonneg_left
          (norm_intervalWaveSum_rational_le (Nat.pos_of_ne_zero h) (-r).val_lt 0 T) (by positivity)
      _ = _ := by field_simp

lemma sum_fourierEnvelope :
    (∑ r : ZMod W, fourierEnvelope r) = 1 + (harmonic (W - 1) : ℝ) := by
  classical
  have heq : range W = insert 0 (Icc 1 (W - 1)) := by
    ext a
    simp only [mem_range, mem_insert, mem_Icc]
    have := NeZero.pos W
    omega
  calc
    _ = ∑ a ∈ range W, if a = 0 then (1 : ℝ) else
        1 / 2 * ((a : ℝ)⁻¹ + ((W - a : ℕ) : ℝ)⁻¹) := by
      rw [sum_zmod_eq_sum_range]
      apply Finset.sum_congr rfl
      intro a ha
      simp only [fourierEnvelope, ZMod.val_natCast_of_lt (mem_range.mp ha)]
    _ = 1 + ∑ a ∈ Icc 1 (W - 1),
        1 / 2 * ((a : ℝ)⁻¹ + ((W - a : ℕ) : ℝ)⁻¹) := by
      rw [heq, Finset.sum_insert (by simp), if_pos rfl]
      congr 1
      apply Finset.sum_congr rfl
      intro a ha
      rw [if_neg (by have := mem_Icc.mp ha; omega)]
    _ = _ := by rw [← Finset.mul_sum, reciprocal_pair_sum]; ring

lemma sum_neg_fourierEnvelope_le (hW : 2 ≤ W) :
    (∑ r : ZMod W, fourierEnvelope (-r)) ≤ 2 + Real.log W := by
  have heq : (∑ r : ZMod W, fourierEnvelope (-r)) = ∑ r : ZMod W, fourierEnvelope r :=
    Fintype.sum_equiv (Equiv.neg (ZMod W)) _ _ (fun r => rfl)
  rw [heq, sum_fourierEnvelope]
  have hlog : Real.log (W - 1 : ℕ) ≤ Real.log W :=
    Real.log_le_log (by exact_mod_cast (show 0 < W - 1 by omega)) (by exact_mod_cast Nat.sub_le W 1)
  linarith [harmonic_le_one_add_log (W - 1)]

/-- Every primitive character is allowed its own additive cutoff. -/
theorem adaptive_interval_cutoff_large_sieve (hW : 2 ≤ W)
    (M : Finset ℕ+) (Q : ℕ) (hQ : 0 < Q) (hM : ∀ q ∈ M, (q : ℕ) ≤ Q)
    (C : ∀ q : ℕ+, Finset (DirichletCharacter ℂ (q : ℕ)))
    (hC : ∀ q ∈ M, ∀ χ ∈ C q, χ.IsPrimitive)
    (A B : Finset ℤ) (a b : ℤ → ℂ) (X Y : ℝ) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hA : ∀ n ∈ A, |(n : ℝ)| ≤ X) (hB : ∀ n ∈ B, |(n : ℝ)| ≤ Y)
    (α β : ℤ → ZMod W)
    (T : (q : ℕ+) → DirichletCharacter ℂ (q : ℕ) → ℕ)
    (hT : ∀ q ∈ M, ∀ χ ∈ C q, T q χ ≤ W) :
    (∑ q ∈ M, ((q : ℕ) : ℝ) / (q : ℕ).totient * ∑ χ ∈ C q,
      ‖∑ m ∈ A, ∑ n ∈ B, if (α m + β n).val < T q χ then
        (a m * b n) * χ ((m * n : ℤ) : ZMod (q : ℕ)) else 0‖) ≤
      (2 + Real.log W) *
        Real.sqrt ((2 * (Q : ℝ) ^ 2 + 4 * (2 * Real.pi * X + 1)) *
          (2 * (Q : ℝ) ^ 2 + 4 * (2 * Real.pi * Y + 1)) *
          (∑ n ∈ A, ‖a n‖ ^ 2) * (∑ n ∈ B, ‖b n‖ ^ 2)) := by
  classical
  have h := weighted_norm_variable_combination_le (M.sigma C) (univ : Finset (ZMod W))
    (fun z => ((z.1 : ℕ) : ℝ) / (z.1 : ℕ).totient)
    (fun z r => normalizedFourier (intervalIndicator (T z.1 z.2)) r)
    (fun r z => characterSum A (fourierTwist r α a) z.2 * characterSum B (fourierTwist r β b) z.2)
    (fun r => fourierEnvelope (-r)) (fun z hz => by positivity)
    (fun r hr => fourierEnvelope_nonneg _)
    (fun z hz r hr => norm_interval_fourier_le_envelope _
      (hT z.1 (mem_sigma.mp hz).1 z.2 (mem_sigma.mp hz).2) r)
    (Real.sqrt ((2 * (Q : ℝ) ^ 2 + 4 * (2 * Real.pi * X + 1)) *
      (2 * (Q : ℝ) ^ 2 + 4 * (2 * Real.pi * Y + 1)) *
      (∑ n ∈ A, ‖a n‖ ^ 2) * (∑ n ∈ B, ‖b n‖ ^ 2))) (fun r hr => ?_)
  · simp only [← bilinear_fourier_completion, Finset.sum_sigma, ← Finset.mul_sum,
      intervalIndicator, mul_ite, mul_one, mul_zero] at h
    exact h.trans (mul_le_mul_of_nonneg_right (sum_neg_fourierEnvelope_le hW) (Real.sqrt_nonneg _))
  · have hr := Real.le_sqrt_of_sq_le (bilinear_characterSum_large_sieve M Q hQ hM C hC A B
      (fourierTwist r α a) (fourierTwist r β b) X Y hX hY hA hB)
    simpa only [norm_fourierTwist, Finset.sum_sigma, norm_mul, ← Finset.mul_sum] using hr

end Fourier

/-- A maximal version of the hyperbolic bilinear bound: the cutoff
`R(q, χ)` may be chosen independently for each character, subject to `R ≤ N`. -/
theorem adaptive_hyperbolic_large_sieve
    (M : Finset ℕ+) (Q : ℕ) (hQ : 0 < Q) (hM : ∀ q ∈ M, (q : ℕ) ≤ Q)
    (C : ∀ q : ℕ+, Finset (DirichletCharacter ℂ (q : ℕ)))
    (hC : ∀ q ∈ M, ∀ χ ∈ C q, χ.IsPrimitive)
    (A B : Finset ℤ) (a b : ℤ → ℂ) (X Y : ℝ) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hA : ∀ n ∈ A, |(n : ℝ)| ≤ X) (hB : ∀ n ∈ B, |(n : ℝ)| ≤ Y)
    (N : ℕ) (R : (q : ℕ+) → DirichletCharacter ℂ (q : ℕ) → ℕ)
    (hR : ∀ q ∈ M, ∀ χ ∈ C q, R q χ ≤ N)
    (hAN : ∀ n ∈ A, 1 ≤ n ∧ n ≤ N) (hBN : ∀ n ∈ B, 1 ≤ n ∧ n ≤ N) :
    (∑ q ∈ M, ((q : ℕ) : ℝ) / (q : ℕ).totient * ∑ χ ∈ C q,
      ‖∑ m ∈ A, ∑ n ∈ B, if m * n ≤ R q χ then
        (a m * b n) * χ ((m * n : ℤ) : ZMod (q : ℕ)) else 0‖) ≤
      (6 + 2 * Real.log ((N : ℝ) + 1)) *
        Real.sqrt ((2 * (Q : ℝ) ^ 2 + 4 * (2 * Real.pi * X + 1)) *
          (2 * (Q : ℝ) ^ 2 + 4 * (2 * Real.pi * Y + 1)) *
          (∑ n ∈ A, ‖a n‖ ^ 2) * (∑ n ∈ B, ‖b n‖ ^ 2)) := by
  have h := adaptive_interval_cutoff_large_sieve (hyperbolicModulus_ge_two N)
    M Q hQ hM C hC A B a b X Y hX hY hA hB (logResidue N) (logResidue N)
    (fun q χ => logCutoff N (R q χ))
    (fun q hq χ hχ => logCutoff_le_modulus (hR q hq χ hχ))
  have heq :
      (∑ q ∈ M, ((q : ℕ) : ℝ) / (q : ℕ).totient * ∑ χ ∈ C q,
        ‖∑ m ∈ A, ∑ n ∈ B, if (logResidue N m + logResidue N n).val < logCutoff N (R q χ) then
          (a m * b n) * χ ((m * n : ℤ) : ZMod (q : ℕ)) else 0‖) =
      ∑ q ∈ M, ((q : ℕ) : ℝ) / (q : ℕ).totient * ∑ χ ∈ C q,
        ‖∑ m ∈ A, ∑ n ∈ B, if m * n ≤ R q χ then
          (a m * b n) * χ ((m * n : ℤ) : ZMod (q : ℕ)) else 0‖ := by
    apply Finset.sum_congr rfl
    intro q hq
    congr 1
    apply Finset.sum_congr rfl
    intro χ hχ
    congr 1
    apply Finset.sum_congr rfl
    intro m hm
    apply Finset.sum_congr rfl
    intro n hn
    simp only [logResidue_condition (hR q hq χ hχ)
      (hAN m hm).1 (hAN m hm).2 (hBN n hn).1 (hBN n hn).2]
  rw [heq] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  linarith [log_hyperbolicModulus_le N]

end Erdos821.AnalyticSieve
