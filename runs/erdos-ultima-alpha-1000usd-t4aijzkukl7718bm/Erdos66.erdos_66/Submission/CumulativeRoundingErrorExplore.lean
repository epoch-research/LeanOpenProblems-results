import Submission.RoundingExplore

/-! Bounded prefix discrepancy gives a quantitative bound on cumulative
representation error. This is not pointwise control of the quadratic error. -/
namespace Erdos66CumulativeRoundingError
open AdditiveCombinatorics Erdos66Fractional Erdos66Rounding Erdos66Generating
open scoped Classical
set_option maxHeartbeats 1200000

lemma prefix_convolution (f g : ℕ → ℝ) (n : ℕ) :
    prefixSum (fun k ↦ sumConv f g k) n=sumConv (prefixSum f) g n := by
  have hnz : (1-PowerSeries.X : PowerSeries ℝ) ≠ 0 := by
    intro he
    have hh := congrArg (PowerSeries.coeff 0) he
    simpa using hh
  have hmk : PowerSeries.mk (fun k ↦ sumConv f g k)=PowerSeries.mk f*PowerSeries.mk g := by
    ext k
    simp only [PowerSeries.coeff_mul,PowerSeries.coeff_mk,sumConv]
  have he : PowerSeries.mk (prefixSum (fun k ↦ sumConv f g k))=
      PowerSeries.mk (prefixSum f)*PowerSeries.mk g := by
    apply mul_left_cancel₀ hnz
    rw [prefix_first_difference,← mul_assoc,prefix_first_difference,hmk]
  have hh := congrArg (PowerSeries.coeff n) he
  simpa only [PowerSeries.coeff_mul,PowerSeries.coeff_mk,sumConv] using hh

lemma difference_of_convolution_squares (f g : ℕ → ℝ) (n : ℕ) :
    sumConv (fun k ↦ f k-g k) (fun k ↦ f k+g k) n=
      sumConv f f n-sumConv g g n := by
  unfold sumConv
  simp only [sub_mul,mul_add,Finset.sum_sub_distrib,Finset.sum_add_distrib]
  change sumConv f f n-sumConv g f n+(sumConv f g n-sumConv g g n)=sumConv f f n-sumConv g g n
  rw [sumConv_comm_real g f]
  ring

lemma bounded_prefix_convolution (e g : ℕ → ℝ) (D : ℝ)
    (he : ∀ n, |prefixSum e n| ≤ D) (hg : ∀ n, 0 ≤ g n) (n : ℕ) :
    |prefixSum (fun k ↦ sumConv e g k) n| ≤ D*prefixSum g n := by
  rw [prefix_convolution,sumConv_comm_real]
  calc
    _ ≤ ∑ ab∈Finset.antidiagonal n, |g ab.1*prefixSum e ab.2| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ ab∈Finset.antidiagonal n, D*g ab.1 := by
      apply Finset.sum_le_sum
      intro ab hab
      rw [abs_mul,abs_of_nonneg (hg _)]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left (he ab.2) (hg ab.1)
    _ = _ := by rw [← Finset.mul_sum,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]; rfl

lemma representation_prefix_error (A : Set ℕ) (D : ℝ) (hD : 0 ≤ D)
    (he : ∀ n, |prefixSum (roundingError A) n| ≤ D) (n : ℕ) :
    |prefixSum (fun k ↦ (sumRep A k : ℝ)-(harmonic (k+1) : ℝ)) n| ≤
      D*(2*prefixSum profile n+D) := by
  have hident : (fun k ↦ (sumRep A k : ℝ)-(harmonic (k+1) : ℝ))=
      fun k ↦ sumConv (roundingError A) (fun i ↦ indicator A i+profile i) k := by
    funext k
    change (sumRep A k : ℝ)-(harmonic (k+1) : ℝ)=
      sumConv (fun i ↦ indicator A i-profile i) (fun i ↦ indicator A i+profile i) k
    rw [difference_of_convolution_squares,profile_convolution]
    rw [sumConv,sum_indicator_antidiagonal]
  rw [hident]
  have hg : ∀ i, 0 ≤ indicator A i+profile i := fun i ↦ add_nonneg (indicator_nonneg A i) (profile_nonneg i)
  have hb := bounded_prefix_convolution (roundingError A) (fun i ↦ indicator A i+profile i) D he hg n
  have ha : prefixSum (indicator A) n ≤ prefixSum profile n+D := by
    have hh := (abs_le.mp (he n)).2
    simp only [prefixSum,roundingError,Finset.sum_sub_distrib] at hh ⊢
    linarith
  simp only [prefixSum,Finset.sum_add_distrib] at hb
  change |prefixSum (fun k ↦ sumConv (roundingError A) (fun i ↦ indicator A i+profile i) k) n| ≤ _
  apply hb.trans
  change D*(prefixSum (indicator A) n+prefixSum profile n) ≤ _
  exact mul_le_mul_of_nonneg_left (by linarith) hD

lemma prefix_square_le_convolution_prefix (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) (n : ℕ) :
    (prefixSum f n)^2 ≤ prefixSum (fun k ↦ sumConv f f k) (2*n) := by
  let S := (Finset.range (n+1)) ×ˢ (Finset.range (n+1))
  have hsq : (prefixSum f n)^2=∑ ab∈S, f ab.1*f ab.2 := by
    simp only [prefixSum,pow_two,Finset.sum_mul,Finset.mul_sum,Finset.sum_product,S]
    exact Finset.sum_congr rfl (fun i hi ↦ Finset.sum_congr rfl (fun j hj ↦ mul_comm _ _))
  have hsum := Finset.sum_fiberwise_of_maps_to (s := S) (t := Finset.range (2*n+1))
    (g := fun ab : ℕ × ℕ ↦ ab.1+ab.2) (f := fun ab ↦ f ab.1*f ab.2) (by
      intro ab hab
      obtain ⟨ha,hb⟩ := Finset.mem_product.mp hab
      have ha' := Finset.mem_range.mp ha
      have hb' := Finset.mem_range.mp hb
      exact Finset.mem_range.mpr (by dsimp only; omega))
  rw [hsq,← hsum]
  apply Finset.sum_le_sum
  intro k hk
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro ab hab
    exact Finset.mem_antidiagonal.mpr (Finset.mem_filter.mp hab).2
  · intro ab hab hnot
    exact mul_nonneg (hf _) (hf _)

lemma harmonic_monotone_real : Monotone (fun n ↦ (harmonic n : ℝ)) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [harmonic_succ]
  push_cast
  exact le_add_of_nonneg_right (by positivity)

lemma profile_prefix_square_bound (n : ℕ) :
    (prefixSum profile n)^2 ≤ ((2*n+1 : ℕ) : ℝ)*(harmonic (2*n+1) : ℝ) := by
  have hh := prefix_square_le_convolution_prefix profile profile_nonneg n
  simp only [profile_convolution] at hh
  apply hh.trans
  change (∑ k∈Finset.range (2*n+1), (harmonic (k+1) : ℝ)) ≤ _
  calc
    _ ≤ ∑ _k∈Finset.range (2*n+1), (harmonic (2*n+1) : ℝ) := by
      apply Finset.sum_le_sum
      intro k hk
      exact harmonic_monotone_real (by have := Finset.mem_range.mp hk; omega)
    _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]

/-- An explicit cumulative error bound for every bounded-discrepancy
rounding, without an unproved quadratic-convolution hypothesis. -/
theorem cumulative_rounding_error_bound (A : Set ℕ) (D : ℝ) (hD : 0 ≤ D)
    (he : ∀ n, |prefixSum (roundingError A) n| ≤ D) (n : ℕ) :
    |prefixSum (fun k ↦ (sumRep A k : ℝ)-(harmonic (k+1) : ℝ)) n| ≤
      2*D*Real.sqrt (((2*n+1 : ℕ) : ℝ)*(harmonic (2*n+1) : ℝ))+D^2 := by
  have hp := Real.le_sqrt_of_sq_le (profile_prefix_square_bound n)
  have hm := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 2*D)
  have hh := representation_prefix_error A D hD he n
  nlinarith

lemma rounded_cumulative_error_bound (n : ℕ) :
    |prefixSum (fun k ↦ (sumRep (roundedSet profile) k : ℝ)-(harmonic (k+1) : ℝ)) n| ≤
      2*Real.sqrt (((2*n+1 : ℕ) : ℝ)*(harmonic (2*n+1) : ℝ))+1 := by
  simpa only [mul_one,one_pow] using cumulative_rounding_error_bound (roundedSet profile) 1
    (by norm_num) harmonic_rounding_discrepancy n

end Erdos66CumulativeRoundingError
