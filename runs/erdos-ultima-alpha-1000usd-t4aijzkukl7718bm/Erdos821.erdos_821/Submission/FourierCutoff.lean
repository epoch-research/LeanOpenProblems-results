import Submission.PolyaVinogradov

/-!
# Finite Fourier completion of bilinear sums

An interval cutoff on an auxiliary cyclic group has Fourier L¹ norm at
most `2 + log W`. Multiplicative large-sieve bounds therefore persist for
cutoffs expressible as an additive condition in that group.
-/

open scoped BigOperators
open Finset

namespace Erdos821.AnalyticSieve

lemma weighted_norm_linear_combination_le {ι κ : Type*}
    (I : Finset ι) (J : Finset κ) (w : ι → ℝ) (c : κ → ℂ) (F : κ → ι → ℂ)
    (hw : ∀ i ∈ I, 0 ≤ w i) (D : ℝ)
    (hF : ∀ j ∈ J, (∑ i ∈ I, w i * ‖F j i‖) ≤ D) :
    (∑ i ∈ I, w i * ‖∑ j ∈ J, c j * F j i‖) ≤ (∑ j ∈ J, ‖c j‖) * D := by
  calc
    _ ≤ ∑ i ∈ I, w i * ∑ j ∈ J, ‖c j‖ * ‖F j i‖ := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_left _ (hw i hi)
      simpa only [norm_mul] using norm_sum_le J (fun j => c j * F j i)
    _ = ∑ j ∈ J, ‖c j‖ * ∑ i ∈ I, w i * ‖F j i‖ := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ ∑ j ∈ J, ‖c j‖ * D :=
      Finset.sum_le_sum (fun j hj => mul_le_mul_of_nonneg_left (hF j hj) (norm_nonneg _))
    _ = _ := by rw [Finset.sum_mul]

section Fourier

variable {W : ℕ} [NeZero W]

noncomputable def normalizedFourier (H : ZMod W → ℂ) (r : ZMod W) : ℂ :=
  (W : ℂ)⁻¹ * ZMod.dft H r

lemma normalizedFourier_inversion (H : ZMod W → ℂ) (x : ZMod W) :
    H x = ∑ r : ZMod W, normalizedFourier H r * ZMod.stdAddChar (r * x) := by
  have h := congrFun (ZMod.dft.symm_apply_apply H) x
  rw [ZMod.invDFT_apply] at h
  rw [← h]
  simp only [normalizedFourier, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  ring

noncomputable def intervalIndicator (T : ℕ) (x : ZMod W) : ℂ :=
  if x.val < T then 1 else 0

lemma dft_intervalIndicator (T : ℕ) (hT : T ≤ W) (r : ZMod W) :
    ZMod.dft (intervalIndicator T) r =
      intervalWaveSum 0 T (((-r).val : ℝ) / W) := by
  classical
  simp only [ZMod.dft_apply, intervalIndicator, smul_eq_mul, mul_ite, mul_one, mul_zero,
    ← Finset.sum_filter, intervalWaveSum, zero_add]
  apply Finset.sum_bij (fun x _ => x.val)
  · intro x hx
    simpa only [mem_filter, mem_univ, true_and, mem_range] using hx
  · intro x hx y hy hxy
    exact ZMod.val_injective W hxy
  · intro n hn
    have hnW : n < W := (mem_range.mp hn).trans_le hT
    refine ⟨(n : ZMod W), ?_, ZMod.val_natCast_of_lt hnW⟩
    simpa only [mem_filter, mem_univ, true_and, ZMod.val_natCast_of_lt hnW] using mem_range.mp hn
  · intro x hx
    rw [← stdAddChar_int_mul]
    simp only [Int.cast_natCast, ZMod.natCast_zmod_val, mul_neg]

lemma sum_zmod_eq_sum_range {E : Type*} [AddCommMonoid E] (f : ZMod W → E) :
    (∑ r : ZMod W, f r) = ∑ a ∈ range W, f (a : ZMod W) := by
  apply Finset.sum_bij (fun r _ => r.val)
  · intro r hr
    exact mem_range.mpr r.val_lt
  · intro r hr s hs h
    exact ZMod.val_injective W h
  · intro a ha
    exact ⟨(a : ZMod W), mem_univ _, ZMod.val_natCast_of_lt (mem_range.mp ha)⟩
  · intro r hr
    rw [ZMod.natCast_zmod_val]

lemma sum_norm_dft_intervalIndicator_le (T : ℕ) (hT : T ≤ W) :
    (∑ r : ZMod W, ‖ZMod.dft (intervalIndicator T) r‖) ≤
      (T : ℝ) + (W : ℝ) * (harmonic (W - 1) : ℝ) := by
  classical
  have heq : range W = insert 0 (Icc 1 (W - 1)) := by
    ext a
    simp only [mem_range, mem_insert, mem_Icc]
    have := NeZero.pos W
    omega
  calc
    _ = ∑ r : ZMod W, ‖intervalWaveSum 0 T ((r.val : ℝ) / W)‖ := by
      simp only [dft_intervalIndicator T hT]
      exact Fintype.sum_equiv (Equiv.neg (ZMod W)) _ _ (fun r => rfl)
    _ = ∑ a ∈ range W, ‖intervalWaveSum 0 T ((a : ℝ) / W)‖ := by
      rw [sum_zmod_eq_sum_range]
      apply Finset.sum_congr rfl
      intro a ha
      rw [ZMod.val_natCast_of_lt (mem_range.mp ha)]
    _ = (T : ℝ) + ∑ a ∈ Icc 1 (W - 1), ‖intervalWaveSum 0 T ((a : ℝ) / W)‖ := by
      rw [heq, Finset.sum_insert (by simp)]
      simp only [Nat.cast_zero, zero_div, intervalWaveSum, wave, Complex.ofReal_zero,
        mul_zero, Complex.exp_zero, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        mul_one, Complex.norm_natCast]
    _ ≤ (T : ℝ) + ∑ a ∈ Icc 1 (W - 1),
        (W : ℝ) / 2 * ((a : ℝ)⁻¹ + ((W - a : ℕ) : ℝ)⁻¹) := by
      apply add_le_add le_rfl
      apply Finset.sum_le_sum
      intro a ha
      simp only [mem_Icc] at ha
      exact norm_intervalWaveSum_rational_le (by omega) (by omega) 0 T
    _ = _ := by rw [← Finset.mul_sum, reciprocal_pair_sum]; ring

lemma intervalIndicator_fourier_l1 (hW : 2 ≤ W) (T : ℕ) (hT : T ≤ W) :
    (∑ r : ZMod W, ‖normalizedFourier (intervalIndicator T) r‖) ≤
      2 + Real.log W := by
  have hWpos : (0 : ℝ) < W := by exact_mod_cast (NeZero.pos W)
  calc
    _ = (W : ℝ)⁻¹ * ∑ r : ZMod W, ‖ZMod.dft (intervalIndicator T) r‖ := by
      simp only [normalizedFourier, norm_mul, norm_inv, Complex.norm_natCast, Finset.mul_sum]
    _ ≤ (W : ℝ)⁻¹ * ((T : ℝ) + (W : ℝ) * (harmonic (W - 1) : ℝ)) :=
      mul_le_mul_of_nonneg_left (sum_norm_dft_intervalIndicator_le T hT) (by positivity)
    _ = (T : ℝ) / W + (harmonic (W - 1) : ℝ) := by field_simp
    _ ≤ 1 + (1 + Real.log W) := by
      apply add_le_add
      · exact (div_le_one hWpos).mpr (by exact_mod_cast hT)
      · apply (harmonic_le_one_add_log _).trans
        apply add_le_add le_rfl
        apply Real.log_le_log
        · exact_mod_cast (show 0 < W - 1 by omega)
        · exact_mod_cast Nat.sub_le W 1
    _ = _ := by ring

noncomputable def fourierTwist (r : ZMod W) (α : ℤ → ZMod W) (a : ℤ → ℂ) (n : ℤ) : ℂ :=
  a n * ZMod.stdAddChar (r * α n)

lemma norm_fourierTwist (r : ZMod W) (α : ℤ → ZMod W) (a : ℤ → ℂ) (n : ℤ) :
    ‖fourierTwist r α a n‖ = ‖a n‖ := by
  have hc : ‖ZMod.stdAddChar (r * α n)‖ = 1 := Circle.norm_coe _
  rw [fourierTwist, norm_mul, hc, mul_one]

lemma bilinear_fourier_completion {q : ℕ} (χ : DirichletCharacter ℂ q)
    (A B : Finset ℤ) (a b : ℤ → ℂ) (α β : ℤ → ZMod W) (H : ZMod W → ℂ) :
    (∑ m ∈ A, ∑ n ∈ B, (a m * b n) * χ ((m * n : ℤ) : ZMod q) * H (α m + β n)) =
      ∑ r : ZMod W, normalizedFourier H r *
        (characterSum A (fourierTwist r α a) χ * characterSum B (fourierTwist r β b) χ) := by
  calc
    _ = ∑ m ∈ A, ∑ n ∈ B, ∑ r : ZMod W,
        normalizedFourier H r *
          ((fourierTwist r α a m * χ (m : ZMod q)) *
            (fourierTwist r β b n * χ (n : ZMod q))) := by
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro n hn
      rw [normalizedFourier_inversion H (α m + β n), Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      simp only [fourierTwist, Int.cast_mul, map_mul, mul_add, AddChar.map_add_eq_mul]
      ring
    _ = ∑ r : ZMod W, ∑ m ∈ A, ∑ n ∈ B,
        normalizedFourier H r *
          ((fourierTwist r α a m * χ (m : ZMod q)) *
            (fourierTwist r β b n * χ (n : ZMod q))) := by
      simp_rw [Finset.sum_comm (s := B) (t := (univ : Finset (ZMod W)))]
      rw [Finset.sum_comm]
    _ = _ := by
      simp only [characterSum]
      simp_rw [Finset.sum_mul_sum]
      simp only [Finset.mul_sum]

/-- Fourier completion transfers the rectangular bilinear large sieve to
an arbitrary cutoff on an auxiliary cyclic group, paying its Fourier L¹ norm. -/
theorem bilinear_fourier_large_sieve
    (M : Finset ℕ+) (Q : ℕ) (hQ : 0 < Q) (hM : ∀ q ∈ M, (q : ℕ) ≤ Q)
    (C : ∀ q : ℕ+, Finset (DirichletCharacter ℂ (q : ℕ)))
    (hC : ∀ q ∈ M, ∀ χ ∈ C q, χ.IsPrimitive)
    (A B : Finset ℤ) (a b : ℤ → ℂ) (X Y : ℝ) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hA : ∀ n ∈ A, |(n : ℝ)| ≤ X) (hB : ∀ n ∈ B, |(n : ℝ)| ≤ Y)
    (α β : ℤ → ZMod W) (H : ZMod W → ℂ) :
    (∑ q ∈ M, ((q : ℕ) : ℝ) / (q : ℕ).totient * ∑ χ ∈ C q,
      ‖∑ m ∈ A, ∑ n ∈ B, (a m * b n) * χ ((m * n : ℤ) : ZMod (q : ℕ)) * H (α m + β n)‖) ≤
      (∑ r : ZMod W, ‖normalizedFourier H r‖) *
        Real.sqrt ((2 * (Q : ℝ) ^ 2 + 4 * (2 * Real.pi * X + 1)) *
          (2 * (Q : ℝ) ^ 2 + 4 * (2 * Real.pi * Y + 1)) *
          (∑ n ∈ A, ‖a n‖ ^ 2) * (∑ n ∈ B, ‖b n‖ ^ 2)) := by
  classical
  have h := weighted_norm_linear_combination_le (M.sigma C) (univ : Finset (ZMod W))
    (fun z => ((z.1 : ℕ) : ℝ) / (z.1 : ℕ).totient) (normalizedFourier H)
    (fun r z => characterSum A (fourierTwist r α a) z.2 * characterSum B (fourierTwist r β b) z.2)
    (fun z hz => by positivity)
    (Real.sqrt ((2 * (Q : ℝ) ^ 2 + 4 * (2 * Real.pi * X + 1)) *
      (2 * (Q : ℝ) ^ 2 + 4 * (2 * Real.pi * Y + 1)) *
      (∑ n ∈ A, ‖a n‖ ^ 2) * (∑ n ∈ B, ‖b n‖ ^ 2))) (fun r hr => ?_)
  · simpa only [← bilinear_fourier_completion, Finset.sum_sigma, ← Finset.mul_sum] using h
  · have hr := Real.le_sqrt_of_sq_le (bilinear_characterSum_large_sieve M Q hQ hM C hC A B
      (fourierTwist r α a) (fourierTwist r β b) X Y hX hY hA hB)
    simpa only [norm_fourierTwist, Finset.sum_sigma, norm_mul, ← Finset.mul_sum] using hr

/-- An additive interval cutoff costs only a logarithmic factor. -/
theorem bilinear_interval_cutoff_large_sieve (hW : 2 ≤ W)
    (M : Finset ℕ+) (Q : ℕ) (hQ : 0 < Q) (hM : ∀ q ∈ M, (q : ℕ) ≤ Q)
    (C : ∀ q : ℕ+, Finset (DirichletCharacter ℂ (q : ℕ)))
    (hC : ∀ q ∈ M, ∀ χ ∈ C q, χ.IsPrimitive)
    (A B : Finset ℤ) (a b : ℤ → ℂ) (X Y : ℝ) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hA : ∀ n ∈ A, |(n : ℝ)| ≤ X) (hB : ∀ n ∈ B, |(n : ℝ)| ≤ Y)
    (α β : ℤ → ZMod W) (T : ℕ) (hT : T ≤ W) :
    (∑ q ∈ M, ((q : ℕ) : ℝ) / (q : ℕ).totient * ∑ χ ∈ C q,
      ‖∑ m ∈ A, ∑ n ∈ B, if (α m + β n).val < T then
        (a m * b n) * χ ((m * n : ℤ) : ZMod (q : ℕ)) else 0‖) ≤
      (2 + Real.log W) *
        Real.sqrt ((2 * (Q : ℝ) ^ 2 + 4 * (2 * Real.pi * X + 1)) *
          (2 * (Q : ℝ) ^ 2 + 4 * (2 * Real.pi * Y + 1)) *
          (∑ n ∈ A, ‖a n‖ ^ 2) * (∑ n ∈ B, ‖b n‖ ^ 2)) := by
  have h := bilinear_fourier_large_sieve M Q hQ hM C hC A B a b X Y hX hY hA hB
    α β (intervalIndicator T)
  simp only [intervalIndicator, mul_ite, mul_one, mul_zero] at h
  exact h.trans (mul_le_mul_of_nonneg_right (intervalIndicator_fourier_l1 hW T hT) (Real.sqrt_nonneg _))

end Fourier

end Erdos821.AnalyticSieve
