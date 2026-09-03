import Submission.PrimeWinnerHarmonicLimits

/-! A sufficient natural-density criterion: uniform prime-label tails for
unnormalized harmonic currents. The required tail estimate is not asserted. -/
namespace Erdos371
open Finset Filter FiniteInformation
open scoped Topology
set_option autoImplicit false

noncomputable def rawHarmonicSum (a : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ range N, a n/(n : ℝ)

lemma sum_from_rawHarmonicSum (a : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ range (N+1), a n) = a 0+(N : ℝ)*rawHarmonicSum a (N+1)-
      ∑ k ∈ range (N+1), rawHarmonicSum a k := by
  induction N with
  | zero => simp [rawHarmonicSum]
  | succ N ih =>
    rw [sum_range_succ,ih]
    have hh : rawHarmonicSum a (N+1+1)=rawHarmonicSum a (N+1)+a (N+1)/(N+1 : ℕ) := by
      exact sum_range_succ _ _
    have hs : (∑ k ∈ range (N+1+1), rawHarmonicSum a k) =
        (∑ k ∈ range (N+1), rawHarmonicSum a k)+rawHarmonicSum a (N+1) :=
      sum_range_succ _ _
    rw [hh,hs]
    push_cast
    have hN : (N : ℝ)+1≠0 := by positivity
    field_simp
    ring

/-- Kronecker's elementary summation lemma in the form needed here.
The UNNORMALIZED harmonic partial sums must converge. -/
theorem prefixMean_zero_of_rawHarmonicSum_tendsto (a : ℕ → ℝ) (L : ℝ)
    (h : Tendsto (rawHarmonicSum a) atTop (𝓝 L)) :
    Tendsto (fun N => prefixMean N a) atTop (𝓝 0) := by
  have h1 := h.comp (tendsto_add_atTop_nat 1)
  have hc := h.cesaro.comp (tendsto_add_atTop_nat 1)
  have hn : Tendsto (fun N : ℕ => (N+1 : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have he := ((tendsto_const_nhds (x := a 0)).sub h1).div_atTop hn
  have ht := (h1.sub hc).add he
  simp only [sub_self,add_zero] at ht
  have ht' : Tendsto (fun N => prefixMean (N+1) a) atTop (𝓝 0) := by
    apply ht.congr'
    exact Eventually.of_forall (fun N => by
      dsimp [Function.comp_def]
      rw [prefixMean,sum_from_rawHarmonicSum a N]
      push_cast
      have hN : (N : ℝ)+1≠0 := by positivity
      field_simp
      ring)
  exact (tendsto_add_atTop_iff_nat 1).mp ht'

lemma rawPrimeWinnerHarmonic_total (N B : ℕ) (hB : N<B) :
    (∑ p ∈ range B, rawPrimeWinnerHarmonic p N)=rawHarmonicSum factorSign N := by
  classical
  unfold rawPrimeWinnerHarmonic primeWinnerHarmonicTerm rawHarmonicSum
  rw [sum_comm]
  apply sum_congr rfl
  intro n hn
  have hw : primeWinner n<B := by
    have hh : primeWinner n≤n+1 := max_le (Nat.maxPrimeFac_le.trans (by omega)) Nat.maxPrimeFac_le
    have hn' := mem_range.mp hn
    omega
  rw [sum_eq_single (primeWinner n)]
  · simp
  · intro p hp hne
    rw [if_neg (Ne.symm hne)]
  · intro hp
    exact False.elim (hp (mem_range.mpr hw))

noncomputable def rawPrimeHarmonicTail (B N : ℕ) : ℝ :=
  ∑ p ∈ (range (N+B+1)).filter (B≤·), |rawPrimeWinnerHarmonic p N|

lemma rawHarmonicSum_low_error_le (B N : ℕ) :
    |rawHarmonicSum factorSign N-∑ p ∈ range B, rawPrimeWinnerHarmonic p N|≤
      rawPrimeHarmonicTail B N := by
  classical
  have he := sum_filter_add_sum_filter_not (range (N+B+1)) (fun p => p<B)
    (fun p => rawPrimeWinnerHarmonic p N)
  have hf : (range (N+B+1)).filter (fun p => p<B)=range B := by
    ext p
    simp only [mem_filter,mem_range]
    omega
  rw [hf,rawPrimeWinnerHarmonic_total N (N+B+1) (by omega)] at he
  simp only [not_lt] at he
  rw [← he,add_sub_cancel_left]
  exact abs_sum_le_sum_abs _ _

/-- Pointwise prime-group convergence, proved in HarmonicLimits, becomes
convergence of the total only if the unnormalized prime tails are tight. -/
theorem rawHarmonicSum_converges_of_prime_tail_tightness
    (htail : ∀ ε : ℝ, 0<ε → ∃ B : ℕ, ∀ᶠ N : ℕ in atTop,
      rawPrimeHarmonicTail B N≤ε) :
    ∃ L : ℝ, Tendsto (rawHarmonicSum factorSign) atTop (𝓝 L) := by
  apply cauchySeq_tendsto_of_complete
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  obtain ⟨B,hB⟩ := htail (ε/8) (by positivity)
  have ht : Tendsto (fun N => ∑ p ∈ range B, rawPrimeWinnerHarmonic p N) atTop
      (𝓝 (∑ p ∈ range B, primeWinnerHarmonicLimit p)) :=
    tendsto_finset_sum (range B) (fun p _ => rawPrimeWinnerHarmonic_tendsto p)
  have hclose := Metric.tendsto_nhds.mp ht (ε/8) (by positivity)
  obtain ⟨T,hT⟩ := eventually_atTop.mp (hB.and hclose)
  refine ⟨T,?_⟩
  intro m hm n hn
  have hm' := hT m hm
  have hn' := hT n hn
  have hem := (rawHarmonicSum_low_error_le B m).trans hm'.1
  have hen := (rawHarmonicSum_low_error_le B n).trans hn'.1
  rw [Real.dist_eq] at hm' hn' ⊢
  have hmid := abs_sub_le (∑ p ∈ range B, rawPrimeWinnerHarmonic p m)
    (∑ p ∈ range B, primeWinnerHarmonicLimit p)
    (∑ p ∈ range B, rawPrimeWinnerHarmonic p n)
  rw [abs_sub_comm (∑ p ∈ range B, primeWinnerHarmonicLimit p)] at hmid
  have ht1 := abs_sub_le (rawHarmonicSum factorSign m)
    (∑ p ∈ range B, rawPrimeWinnerHarmonic p m) (rawHarmonicSum factorSign n)
  have ht2 := abs_sub_le (∑ p ∈ range B, rawPrimeWinnerHarmonic p m)
    (∑ p ∈ range B, rawPrimeWinnerHarmonic p n) (rawHarmonicSum factorSign n)
  rw [abs_sub_comm (∑ p ∈ range B, rawPrimeWinnerHarmonic p n)] at ht2
  linarith [hm'.2,hn'.2]

/-- A substantive missing UNNORMALIZED tail estimate would prove the
original natural-density statement. Normalized harmonic l1 convergence is
not this hypothesis. -/
theorem density_of_rawPrimeHarmonic_tightness
    (htail : ∀ ε : ℝ, 0<ε → ∃ B : ℕ, ∀ᶠ N : ℕ in atTop,
      rawPrimeHarmonicTail B N≤ε) :
    {n | Nat.maxPrimeFac (n+1)>Nat.maxPrimeFac n}.HasDensity (1/2) := by
  obtain ⟨L,hL⟩ := rawHarmonicSum_converges_of_prime_tail_tightness htail
  rw [density_iff_signed_count]
  simpa only [prefixMean,factorSign_sum_eq_count_difference] using
    prefixMean_zero_of_rawHarmonicSum_tendsto factorSign L hL

#print axioms prefixMean_zero_of_rawHarmonicSum_tendsto
#print axioms rawHarmonicSum_converges_of_prime_tail_tightness
#print axioms density_of_rawPrimeHarmonic_tightness
end Erdos371
