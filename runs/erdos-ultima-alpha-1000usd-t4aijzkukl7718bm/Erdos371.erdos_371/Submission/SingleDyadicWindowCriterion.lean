import Submission.DyadicEndpointRegularity
import Submission.InteriorWindowCriterion
import Submission.DyadicHarmonicCancellation

/-! Using the already proved logarithmic absolute endpoint theorem, a single
unnormalized dyadic harmonic window is enough. Its cancellation is not proved. -/
namespace Erdos371
open Finset Filter FiniteInformation
open scoped Topology
set_option autoImplicit false

lemma sum_range_double_pair (f : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ range (2*N), f n) = ∑ k ∈ range N, (f (2*k)+f (2*k+1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 2*(N+1)=(2*N+1)+1 by omega, sum_range_succ, sum_range_succ,
      ih, sum_range_succ]
    ring

lemma prefixMean_double_pair (f : ℕ → ℝ) (N : ℕ) :
    prefixMean (2*N) f = prefixMean N (fun k => (f (2*k)+f (2*k+1))/2) := by
  unfold prefixMean
  rw [sum_range_double_pair, ← sum_div]
  push_cast
  ring

noncomputable def dyadicHarmonicRounding (f : ℕ → ℝ) (k : ℕ) : ℝ :=
  f (2*k+1)*((1 : ℝ)/(2*k+1)-(1 : ℝ)/(2*k))

lemma dyadicHarmonicRounding_bound (f : ℕ → ℝ) (hf : ∀ n, |f n|≤1) (k : ℕ) :
    |dyadicHarmonicRounding f k| ≤ 1/(k+1 : ℝ)^2 := by
  by_cases hk : k=0
  · subst k
    simpa [dyadicHarmonicRounding] using hf 1
  have hk1 : (1 : ℝ)≤k := by exact_mod_cast (show 1≤k by omega)
  have hk0 : (0 : ℝ)<k := by positivity
  have h2k : (0 : ℝ)<2*k := by positivity
  have h2k1 : (0 : ℝ)<2*k+1 := by positivity
  have hgap : (1 : ℝ)/(2*k+1)≤1/(2*k) :=
    one_div_le_one_div_of_le h2k (by linarith)
  unfold dyadicHarmonicRounding
  rw [abs_mul,abs_of_nonpos (sub_nonpos.mpr hgap)]
  calc
    _ ≤ 1*((1 : ℝ)/(2*k)-1/(2*k+1)) := by
      convert mul_le_mul_of_nonneg_right (hf (2*k+1)) (sub_nonneg.mpr hgap) using 1; ring
    _ = 1/((2*k)*(2*k+1)) := by field_simp; ring
    _ ≤ 1/(k+1 : ℝ)^2 := by
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith [sq_nonneg ((k : ℝ)-1)]

lemma summable_dyadicHarmonicRounding (f : ℕ → ℝ) (hf : ∀ n, |f n|≤1) :
    Summable (dyadicHarmonicRounding f) := by
  have hs : Summable (fun k : ℕ => (1 : ℝ)/(k+1 : ℝ)^2) := by
    have h := (summable_nat_add_iff 1).mpr
      (Real.summable_one_div_nat_pow.mpr (by norm_num : 1<2))
    simpa only [Nat.cast_add,Nat.cast_one] using h
  exact (Summable.of_nonneg_of_le (fun k => abs_nonneg _) (dyadicHarmonicRounding_bound f hf) hs).of_abs

lemma dyadic_coboundary_rawHarmonicSum (f : ℕ → ℝ) (N : ℕ) :
    rawHarmonicSum (fun k => f k-(f (2*k)+f (2*k+1))/2) N =
      rawHarmonicSum f N-rawHarmonicSum f (2*N)+
        ∑ k ∈ range N, dyadicHarmonicRounding f k := by
  unfold rawHarmonicSum
  rw [sum_range_double_pair, ← sum_sub_distrib, ← sum_add_distrib]
  apply sum_congr rfl
  intro k hk
  unfold dyadicHarmonicRounding
  push_cast
  ring

/-- A vanishing dyadic harmonic window implies dyadic regularity of ordinary
prefix means. The summable reciprocal rounding error must be retained. -/
theorem prefixMean_dyadic_regularity_of_harmonic_window (f : ℕ → ℝ)
    (hf : ∀ n, |f n|≤1)
    (hw : Tendsto (fun N => rawHarmonicSum f (2*N)-rawHarmonicSum f N) atTop (𝓝 0)) :
    Tendsto (fun N => prefixMean (2*N) f-prefixMean N f) atTop (𝓝 0) := by
  let h := fun k => f k-(f (2*k)+f (2*k+1))/2
  have he := (summable_dyadicHarmonicRounding f hf).hasSum.tendsto_sum_nat
  have ht := hw.neg.add he
  simp only [neg_zero,zero_add] at ht
  have hc : Tendsto (rawHarmonicSum h) atTop
      (𝓝 (∑' k, dyadicHarmonicRounding f k)) := by
    apply ht.congr
    intro N
    dsimp only [h]
    rw [dyadic_coboundary_rawHarmonicSum]
    ring
  have hg := (prefixMean_zero_of_rawHarmonicSum_tendsto h _ hc).neg
  simp only [neg_zero] at hg
  apply hg.congr
  intro N
  simp only [h,prefixMean_sub,← prefixMean_double_pair]
  ring

lemma prefixMean_consecutive_difference_zero (f : ℕ → ℝ) (hf : ∀ n, |f n|≤1) :
    Tendsto (fun N => prefixMean (N+1) f-prefixMean N f) atTop (𝓝 0) := by
  have ht : Tendsto (fun N : ℕ => (2 : ℝ)/(N+1 : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      ((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add (tendsto_const_nhds (x := (1 : ℝ))))
  apply squeeze_zero_norm' _ ht
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  have hb := prefixMean_endpoint_bound N (N+1) hN (by omega) f 1 (fun n _ => hf n)
  simpa only [Real.norm_eq_abs,Nat.add_sub_cancel_left,Nat.cast_one,mul_one,
    Nat.cast_add] using hb

/-- Taking absolute values and a second Cesàro mean preserves dyadic
regularity of the ordinary prefix means of a bounded sequence. -/
theorem absolute_prefixMean_dyadic_regularity (f : ℕ → ℝ) (hf : ∀ n, |f n|≤1)
    (hg : Tendsto (fun N => prefixMean (2*N) f-prefixMean N f) atTop (𝓝 0)) :
    Tendsto (fun N => prefixMean (2*N) (fun k => |prefixMean k f|)-
      prefixMean N (fun k => |prefixMean k f|)) atTop (𝓝 0) := by
  have ht : Tendsto (fun N : ℕ => 2*N) atTop atTop :=
    tendsto_atTop_mono (fun N => by dsimp; omega) tendsto_id
  have ho := ((prefixMean_consecutive_difference_zero f hf).comp ht).add hg
  simp only [Function.comp_apply,sub_add_sub_cancel,add_zero] at ho
  have hE : Tendsto (fun N => |prefixMean (2*N) f|-|prefixMean N f|) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun N => ?_) (show Tendsto _ atTop (𝓝 0) from by
      simpa only [abs_zero] using hg.abs)
    simpa only [Real.norm_eq_abs] using abs_abs_sub_abs_le (prefixMean (2*N) f) (prefixMean N f)
  have hO : Tendsto (fun N => |prefixMean (2*N+1) f|-|prefixMean N f|) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun N => ?_) (show Tendsto _ atTop (𝓝 0) from by
      simpa only [abs_zero] using ho.abs)
    simpa only [Real.norm_eq_abs] using abs_abs_sub_abs_le (prefixMean (2*N+1) f) (prefixMean N f)
  have h := ((hE.add hO).div_const 2).cesaro
  norm_num only [add_zero,zero_div] at h
  apply h.congr
  intro N
  rw [prefixMean_double_pair]
  simp only [prefixMean,← sum_div,sum_add_distrib,sum_sub_distrib]
  ring

/-- For the actual prime comparison, ordinary dyadic regularity alone now
suffices, because logarithmically almost all ordinary endpoints are good. -/
theorem density_of_factorSign_dyadic_regularity
    (h : Tendsto (fun N => prefixMean (2*N) factorSign-prefixMean N factorSign)
      atTop (𝓝 0)) :
    {n | Nat.maxPrimeFac (n+1)>Nat.maxPrimeFac n}.HasDensity (1/2) := by
  have hf : ∀ n, |factorSign n|≤1 := by
    intro n
    simpa only [← Real.norm_eq_abs,factorSign_norm] using (le_refl (1 : ℝ))
  exact density_of_smoothedEndpointBias_dyadic_regularity
    (absolute_prefixMean_dyadic_regularity factorSign hf h)

/-- A single dyadic unnormalized harmonic window suffices for this conjecture.
The limit on the right remains unproved. -/
theorem density_iff_single_dyadic_harmonic_window :
    {n | Nat.maxPrimeFac (n+1)>Nat.maxPrimeFac n}.HasDensity (1/2) ↔
      Tendsto (fun N => rawHarmonicSum factorSign (2*N)-rawHarmonicSum factorSign N)
        atTop (𝓝 0) := by
  have hf : ∀ n, |factorSign n|≤1 := by
    intro n
    simpa only [← Real.norm_eq_abs,factorSign_norm] using (le_refl (1 : ℝ))
  constructor
  · intro h
    rw [density_iff_signed_count] at h
    have hg : Tendsto (fun N => prefixMean N factorSign) atTop (𝓝 0) := by
      simpa only [prefixMean,factorSign_sum_eq_count_difference] using h
    exact harmonic_window_zero_of_prefixMean_zero factorSign hf hg 2 (by omega)
  · intro h
    exact density_of_factorSign_dyadic_regularity
      (prefixMean_dyadic_regularity_of_harmonic_window factorSign hf h)

/-- The same single-window criterion after removing the already controlled
low and near-linear boundary terms. This is not a proof of the limit. -/
theorem density_iff_single_dyadic_interior_harmonic_window :
    {n | Nat.maxPrimeFac (n+1)>Nat.maxPrimeFac n}.HasDensity (1/2) ↔
      Tendsto (fun N => rawHarmonicSum dyadicInteriorSign (2*N)-
        rawHarmonicSum dyadicInteriorSign N) atTop (𝓝 0) := by
  rw [density_iff_single_dyadic_harmonic_window]
  have he := dyadic_boundary_harmonic_window_zero 2 (by omega)
  constructor
  · intro h
    simpa only [sub_sub_cancel,sub_zero] using h.sub he
  · intro h
    simpa only [add_sub_cancel,add_zero] using h.add he

lemma nonBetweenHarmonicSum_as_raw_dyadic_coboundary (N : ℕ) :
    nonBetweenHarmonicSum N =
      rawHarmonicSum (fun k => factorSign k-
        (factorSign (2*k)+factorSign (2*k+1))/2) (N+1) := by
  rw [rawHarmonicSum,sum_range_succ']
  simp only [Nat.cast_zero,div_zero,add_zero]
  unfold nonBetweenHarmonicSum
  apply sum_congr rfl
  intro k hk
  have he := factorSign_dyadic_positive (k+1) (by omega)
  rw [he]
  push_cast
  split_ifs <;> ring

/-- The bounded non-between harmonic sums converge if and only if the
original natural-density assertion holds. Boundedness alone is insufficient. -/
theorem density_iff_nonBetweenHarmonicSum_converges :
    {n | Nat.maxPrimeFac (n+1)>Nat.maxPrimeFac n}.HasDensity (1/2) ↔
      ∃ L : ℝ, Tendsto nonBetweenHarmonicSum atTop (𝓝 L) := by
  let f := factorSign
  let h := fun k => f k-(f (2*k)+f (2*k+1))/2
  have hf : ∀ n, |f n|≤1 := by
    intro n
    simpa only [f,← Real.norm_eq_abs,factorSign_norm] using (le_refl (1 : ℝ))
  constructor
  · intro hd
    have hw := density_iff_single_dyadic_harmonic_window.mp hd
    have he := (summable_dyadicHarmonicRounding f hf).hasSum.tendsto_sum_nat
    have ht := hw.neg.add he
    simp only [neg_zero,zero_add] at ht
    have hc : Tendsto (rawHarmonicSum h) atTop
        (𝓝 (∑' k, dyadicHarmonicRounding f k)) := by
      apply ht.congr
      intro N
      dsimp only [h,f]
      rw [dyadic_coboundary_rawHarmonicSum]
      ring
    refine ⟨∑' k, dyadicHarmonicRounding f k,?_⟩
    have hc' := hc.comp (tendsto_add_atTop_nat 1)
    apply hc'.congr
    intro N
    exact (nonBetweenHarmonicSum_as_raw_dyadic_coboundary N).symm
  · rintro ⟨L,hL⟩
    have hc' : Tendsto (fun N => rawHarmonicSum h (N+1)) atTop (𝓝 L) := by
      simpa only [h,f,← nonBetweenHarmonicSum_as_raw_dyadic_coboundary] using hL
    have hc : Tendsto (rawHarmonicSum h) atTop (𝓝 L) :=
      (tendsto_add_atTop_iff_nat 1).mp hc'
    have hg := (prefixMean_zero_of_rawHarmonicSum_tendsto h L hc).neg
    simp only [neg_zero] at hg
    apply density_of_factorSign_dyadic_regularity
    apply hg.congr
    intro N
    simp only [h,f,prefixMean_sub,← prefixMean_double_pair]
    ring

#print axioms density_iff_nonBetweenHarmonicSum_converges

#print axioms density_iff_single_dyadic_harmonic_window
#print axioms density_iff_single_dyadic_interior_harmonic_window
end Erdos371
