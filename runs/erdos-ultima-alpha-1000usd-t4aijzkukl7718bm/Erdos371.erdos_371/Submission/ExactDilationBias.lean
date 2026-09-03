import Submission.ExactMultiplierChirpObstruction

/-! Biased natural adjacent correlations with exact invariance under every
fixed positive multiplier. These auxiliary models are not max-prime labels. -/
namespace Erdos371.ExactMultiplierChirpObstruction
open Finset Filter MultiplicativeChirpObstruction
open scoped Topology

noncomputable def imaginaryBias (f : ℕ → ℂ) (N : ℕ) : ℝ :=
  (∑ n ∈ Icc 1 N, (f (n+1)*(starRingEnd ℂ) (f n)).im)/N

lemma imaginaryBias_chirp (N : ℕ) : imaginaryBias (chirp N) N = chirpCorrelationMean N := by
  unfold imaginaryBias chirpCorrelationMean
  congr 2

lemma imaginary_correlation_error (f g : ℕ → ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (hg : ∀ n, ‖g n‖ ≤ 1) (n : ℕ) :
    |(f (n+1)*(starRingEnd ℂ) (f n)).im-(g (n+1)*(starRingEnd ℂ) (g n)).im| ≤
      ‖f (n+1)-g (n+1)‖+‖f n-g n‖ := by
  rw [← Complex.sub_im]
  apply (Complex.abs_im_le_norm _).trans
  have he : f (n+1)*(starRingEnd ℂ) (f n)-g (n+1)*(starRingEnd ℂ) (g n) =
      (f (n+1)-g (n+1))*(starRingEnd ℂ) (f n)+g (n+1)*(starRingEnd ℂ) (f n-g n) := by
    rw [map_sub]
    ring
  rw [he]
  calc
    _ ≤ ‖(f (n+1)-g (n+1))*(starRingEnd ℂ) (f n)‖+
        ‖g (n+1)*(starRingEnd ℂ) (f n-g n)‖ := norm_add_le _ _
    _ ≤ _ := by
      simp only [norm_mul,Complex.norm_conj]
      exact add_le_add
        (mul_le_of_le_one_right (norm_nonneg _) (hf n))
        (mul_le_of_le_one_left (norm_nonneg _) (hg (n+1)))

lemma sum_successor_le (E : ℕ → ℝ) (hE : ∀ n, 0 ≤ E n) (N : ℕ) :
    (∑ n ∈ Icc 1 N, E (n+1)) ≤ ∑ n ∈ Icc 1 (N+1), E n := by
  have he : (∑ n ∈ Icc 1 N, E (n+1)) = ∑ n ∈ (Icc 1 N).image (fun n => n+1), E n := by
    rw [sum_image (by intro a _ b _ h; dsimp only at h; omega)]
  rw [he]
  apply sum_le_sum_of_subset_of_nonneg
  · intro n hn
    obtain ⟨m,hm,rfl⟩ := mem_image.mp hn
    obtain ⟨hm,hmN⟩ := mem_Icc.mp hm
    exact mem_Icc.mpr ⟨by omega,by omega⟩
  · intro n _ _
    exact hE n

lemma imaginaryBias_error (f g : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) (hg : ∀ n, ‖g n‖ ≤ 1)
    (N : ℕ) :
    |imaginaryBias f N-imaginaryBias g N| ≤
      2*(∑ n ∈ Icc 1 (N+1), ‖f n-g n‖)/N := by
  unfold imaginaryBias
  rw [← sub_div,abs_div,abs_of_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N),← sum_sub_distrib]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  have hs : (∑ n ∈ Icc 1 N, ‖f n-g n‖) ≤ ∑ n ∈ Icc 1 (N+1), ‖f n-g n‖ :=
    sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right (by omega)) (by intros; positivity)
  calc
    _ ≤ ∑ n ∈ Icc 1 N, |(f (n+1)*(starRingEnd ℂ) (f n)).im-
        (g (n+1)*(starRingEnd ℂ) (g n)).im| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Icc 1 N, (‖f (n+1)-g (n+1)‖+‖f n-g n‖) :=
      sum_le_sum fun n _ => imaginary_correlation_error f g hf hg n
    _ ≤ _ := by
      rw [sum_add_distrib]
      linarith [sum_successor_le (fun n => ‖f n-g n‖) (fun _ => norm_nonneg _) N]

lemma strippedChirp_bias_error (t : ℝ) (B N : ℕ) (hN : 0 < N) :
    |imaginaryBias (strippedChirp t B) N-imaginaryBias (chirp t) N| ≤
      4*(∑ p ∈ (B+1).primesBelow, ‖chirp t p-1‖) := by
  have he := imaginaryBias_error (strippedChirp t B) (chirp t)
    (strippedChirp_norm_le_one t B) (chirp_norm_le_one t) N
  have hs := strippedChirp_error_sum t B (N+1)
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  apply he.trans
  apply (div_le_iff₀ hNr).mpr
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hp : 0 ≤ ∑ p ∈ (B+1).primesBelow, ‖chirp t p-1‖ := by positivity
  push_cast at hs
  nlinarith

/-- For any prescribed finite multiplier range, stripping causes arbitrarily
small mean error along a suitable unbounded chirp subsequence. -/
theorem exists_stripped_biased_chirp (B : ℕ) :
    ∃ N : ℕ, B ≤ N ∧ 9 ≤ N ∧ (1/120 : ℝ) ≤ imaginaryBias (strippedChirp N B) N := by
  obtain ⟨a,ha,hres,hbias⟩ := exists_chirp_subsequence_fixed_multipliers
  have he : Tendsto (fun j => ∑ p ∈ (B+1).primesBelow, ‖chirp (a j) p-1‖) atTop (nhds 0) := by
    have ht := tendsto_finset_sum (B+1).primesBelow (fun p hp =>
      ((hres p (Nat.mem_primesBelow.mp hp).2.pos).sub_const 1).norm)
    simpa only [sub_self,norm_zero,sum_const_zero] using ht
  obtain ⟨j,⟨⟨hjB,hj9⟩,hjb⟩,hje⟩ := (ha.eventually_ge_atTop B |>.and
    (ha.eventually_ge_atTop 9) |>.and hbias |>.and
      (he.eventually_lt_const (by norm_num : (0 : ℝ) < 1/1000))).exists
  have herr := strippedChirp_bias_error (a j) B (a j) (by omega)
  rw [imaginaryBias_chirp] at herr
  refine ⟨a j,hjB,hj9,?_⟩
  have hlo := (abs_le.mp herr).1
  linarith

/-- Exact eventual invariance under EVERY fixed multiplier, uniformly over
all starting integers, does not force real natural adjacent correlations.
The functions are endpoint-dependent and are not max-under-multiplication. -/
theorem exists_exact_dilation_stable_biased_family :
    ∃ N : ℕ → ℕ, ∃ F : ℕ → ℕ → ℂ,
      Tendsto N atTop atTop ∧
      (∀ j n, ‖F j n‖ ≤ 1) ∧
      (∀ j k, 0 < k → k ≤ j → ∀ n, F j (k*n) = F j n) ∧
      ∀ j, (1/120 : ℝ) ≤ imaginaryBias (F j) (N j) := by
  choose N hNB hN9 hb using exists_stripped_biased_chirp
  refine ⟨N,fun j => strippedChirp (N j) j,tendsto_atTop_mono hNB tendsto_id,?_,?_,hb⟩
  · intro j n
    exact strippedChirp_norm_le_one _ _ _
  · intro j k hk hkj n
    exact strippedChirp_small_multiplier _ _ _ _ hk hkj

#print axioms exists_exact_dilation_stable_biased_family
end Erdos371.ExactMultiplierChirpObstruction
