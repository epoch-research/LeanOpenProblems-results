import Submission.NaturalDensityUniqueness

/-! A harmonic limit of a bounded sequence is a subsequential limit of its
ordinary prefix means. Applying this to the actual comparison yields natural
rise proportions approaching one half along diverging endpoints, not a limit
along all endpoints. -/
namespace Erdos371.FiniteInformation
open Finset Filter
open scoped Topology
set_option autoImplicit false

lemma eventual_prefixMean_lower_le_harmonic_limit (F : ℕ → ℝ)
    (hF : ∀ n, |F n| ≤ 1) (d a : ℝ)
    (hd : Tendsto (fun N => harmonicMean (N+1) F) atTop (𝓝 d))
    (ha : ∀ᶠ N : ℕ in atTop, a ≤ prefixMean N F) : a ≤ d := by
  obtain ⟨T,hT⟩ := eventually_atTop.mp ha
  let K := |a|+1
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hrange : Tendsto (fun N => harmonicRangeMean (N+1) F) atTop (𝓝 d) := by
    have herr : Tendsto (fun N => harmonicRangeMean (N+1) F-harmonicMean (N+1) F)
        atTop (𝓝 0) := by
      have hz : Tendsto (fun N : ℕ => (2 : ℝ)/(harmonic (N+1) : ℝ)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop harmonic_real_tendsto
      apply squeeze_zero_norm' _ hz
      exact Eventually.of_forall fun N => by
        simpa only [Real.norm_eq_abs] using harmonicMean_range_error N F hF
    simpa only [zero_add,sub_add_cancel] using herr.add hd
  have hsmall : Tendsto (fun N : ℕ => K*(harmonic T : ℝ)/(harmonic (N+1) : ℝ))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop harmonic_real_tendsto
  have hlow : ∀ᶠ N : ℕ in atTop,
      a-K*(harmonic T : ℝ)/(harmonic (N+1) : ℝ) ≤ harmonicRangeMean (N+1) F := by
    filter_upwards [eventually_ge_atTop T] with N hNT
    have hpoint (i : Fin (N+1)) :
        a+(-K)*(if harmonicPrefixLength N i<T then (1 : ℝ) else 0) ≤
          prefixMean (harmonicPrefixLength N i) F := by
      by_cases hi : harmonicPrefixLength N i<T
      · rw [if_pos hi,mul_one]
        have hb := (abs_le.mp (abs_prefixMean_le _ (harmonicPrefixLength_pos N i)
          F 1 (fun n _ => hF n))).1
        dsimp [K]
        linarith [le_abs_self a]
      · rw [if_neg hi,mul_zero,add_zero]
        exact hT _ (not_lt.mp hi)
    have hm := mean_mono (harmonicPrefixLaw N) _ _ hpoint
    rw [mean_add,mean_const,mean_smul,harmonicPrefixLaw_representation] at hm
    have hs := mul_le_mul_of_nonneg_left
      (harmonicPrefixLaw_short_length_mass N T (by omega)) hK
    change _ ≤ harmonicRangeMean (N+1) F at hm
    rw [← mul_div_assoc] at hs
    linarith
  have hl := (tendsto_const_nhds (x := a)).sub hsmall
  simp only [sub_zero] at hl
  exact le_of_tendsto_of_tendsto hl hrange hlow

lemma eventual_prefixMean_upper_ge_harmonic_limit (F : ℕ → ℝ)
    (hF : ∀ n, |F n| ≤ 1) (d a : ℝ)
    (hd : Tendsto (fun N => harmonicMean (N+1) F) atTop (𝓝 d))
    (ha : ∀ᶠ N : ℕ in atTop, prefixMean N F ≤ a) : d ≤ a := by
  have hn : Tendsto (fun N => harmonicMean (N+1) (fun n => -F n)) atTop (𝓝 (-d)) := by
    simpa only [harmonicMean,neg_div,sum_neg_distrib] using hd.neg
  have hp : ∀ᶠ N : ℕ in atTop, -a ≤ prefixMean N (fun n => -F n) := by
    filter_upwards [ha] with N hN
    simpa only [prefixMean,sum_neg_distrib,neg_div,neg_le_neg_iff] using hN
  have h := eventual_prefixMean_lower_le_harmonic_limit (fun n => -F n)
    (fun n => by simpa only [abs_neg] using hF n) (-d) (-a) hn hp
  linarith

/-- No gap around the harmonic limit can contain all sufficiently late
ordinary prefix means: their successive jumps tend to zero. -/
theorem exists_late_prefixMean_near_harmonic_limit (F : ℕ → ℝ)
    (hF : ∀ n, |F n| ≤ 1) (d : ℝ)
    (hd : Tendsto (fun N => harmonicMean (N+1) F) atTop (𝓝 d))
    (ε : ℝ) (hε : 0 < ε) (M : ℕ) :
    ∃ N : ℕ, M ≤ N ∧ |prefixMean N F-d| < ε := by
  by_contra h
  have haway : ∀ N, M ≤ N → ε ≤ |prefixMean N F-d| := by
    intro N hMN
    by_contra hn
    exact h ⟨N,hMN,lt_of_not_ge hn⟩
  have ht : Tendsto (fun N : ℕ => (2 : ℝ)/(N+1 : ℕ)) atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat 2).comp (tendsto_add_atTop_nat 1)
  obtain ⟨T,hT⟩ := eventually_atTop.mp (ht.eventually_lt_const hε)
  let B := max (max T M) 1
  have hBM : M ≤ B := (le_max_right T M).trans (le_max_left _ _)
  have hBT : T ≤ B := (le_max_left T M).trans (le_max_left _ _)
  have hB1 : 1 ≤ B := le_max_right _ _
  have hstep (N : ℕ) (hBN : B ≤ N) : |prefixMean (N+1) F-prefixMean N F| < ε := by
    have hh := prefixMean_endpoint_bound N (N+1) (by omega) (by omega)
      F 1 (fun n _ => hF n)
    simp only [Nat.add_sub_cancel_left,Nat.cast_one,mul_one] at hh
    exact hh.trans_lt (hT N (hBT.trans hBN))
  have hside (N : ℕ) (hBN : B ≤ N) :
      prefixMean N F ≤ d-ε ∨ d+ε ≤ prefixMean N F := by
    have hh := haway N (hBM.trans hBN)
    rcases le_abs.mp hh with hpos | hneg
    · exact Or.inr (by linarith)
    · exact Or.inl (by linarith)
  rcases hside B le_rfl with hleft | hright
  · have hl : ∀ k : ℕ, prefixMean (B+k) F ≤ d-ε := by
      intro k
      induction k with
      | zero => simpa only [Nat.add_zero] using hleft
      | succ k ih =>
        rcases hside (B+k+1) (by omega) with hl | hr
        · simpa only [Nat.add_assoc] using hl
        · have hs := (abs_lt.mp (hstep (B+k) (by omega))).2
          linarith
    have he : ∀ᶠ N : ℕ in atTop, prefixMean N F ≤ d-ε := by
      filter_upwards [eventually_ge_atTop B] with N hN
      simpa only [Nat.add_sub_of_le hN] using hl (N-B)
    have hx := eventual_prefixMean_upper_ge_harmonic_limit F hF d (d-ε) hd he
    linarith
  · have hr : ∀ k : ℕ, d+ε ≤ prefixMean (B+k) F := by
      intro k
      induction k with
      | zero => simpa only [Nat.add_zero] using hright
      | succ k ih =>
        rcases hside (B+k+1) (by omega) with hl | hr
        · have hs := (abs_lt.mp (hstep (B+k) (by omega))).1
          linarith
        · simpa only [Nat.add_assoc] using hr
    have he : ∀ᶠ N : ℕ in atTop, d+ε ≤ prefixMean N F := by
      filter_upwards [eventually_ge_atTop B] with N hN
      simpa only [Nat.add_sub_of_le hN] using hr (N-B)
    have hx := eventual_prefixMean_lower_le_harmonic_limit F hF d (d+ε) hd he
    linarith

theorem exists_diverging_prefixMean_limit (F : ℕ → ℝ)
    (hF : ∀ n, |F n| ≤ 1) (d : ℝ)
    (hd : Tendsto (fun N => harmonicMean (N+1) F) atTop (𝓝 d)) :
    ∃ D : ℕ → ℕ, Tendsto D atTop atTop ∧
      Tendsto (fun k => prefixMean (D k) F) atTop (𝓝 d) := by
  have hex (k : ℕ) := exists_late_prefixMean_near_harmonic_limit F hF d hd
    (1/(k+1 : ℝ)) (by positivity) k
  choose D hD hnear using hex
  refine ⟨D,tendsto_atTop_mono hD tendsto_id,?_⟩
  have ht : Tendsto (fun k : ℕ => (1 : ℝ)/(k+1)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Nat.cast_add,Nat.cast_one] using
      (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp (tendsto_add_atTop_nat 1)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [ht.eventually_lt_const hε] with k hk
  rw [Real.dist_eq]
  exact (hnear k).trans hk

end Erdos371.FiniteInformation

namespace Erdos371
open Finset Filter FiniteInformation
open scoped Topology
set_option autoImplicit false

lemma rising_partialDensity (N : ℕ) :
    {n | Nat.maxPrimeFac (n+1)>Nat.maxPrimeFac n}.partialDensity Set.univ N =
      (risingCount N : ℝ)/N := by
  have h : {n | Nat.maxPrimeFac (n+1)>Nat.maxPrimeFac n} ∩ Set.Iio N =
      ((range N).filter fun n => Nat.maxPrimeFac (n+1)>Nat.maxPrimeFac n : Set ℕ) := by
    ext n
    simp only [Set.mem_inter_iff,Set.mem_setOf_eq,Set.mem_Iio,
      mem_coe,mem_filter,mem_range]
    exact and_comm
  simp only [Set.partialDensity,Set.inter_univ,h,Set.ncard_coe_finset,
    Set.univ_inter,Nat.ncard_Iio,risingCount]

/-- Arbitrarily late ordinary rise proportions come arbitrarily close to
one half. This does not state that all sufficiently late proportions do so. -/
theorem largest_prime_rises_arbitrarily_late_near_half (ε : ℝ) (hε : 0 < ε) (M : ℕ) :
    ∃ N : ℕ, M ≤ N ∧ |(risingCount N : ℝ)/N-1/2| < ε := by
  let R (n : ℕ) : ℝ := if Nat.maxPrimeFac (n+1)>Nat.maxPrimeFac n then 1 else 0
  have hR : ∀ n, |R n| ≤ 1 := by
    intro n
    dsimp [R]
    split_ifs <;> norm_num
  obtain ⟨N,hN,hnear⟩ := exists_late_prefixMean_near_harmonic_limit R hR (1/2)
    largest_prime_rises_harmonic_half ε hε M
  refine ⟨N,hN,?_⟩
  simpa [prefixMean,R,risingCount,← sum_filter] using hnear

/-- Natural density one half along a diverging sequence of endpoints. The
full natural-density limit in Spec.lean is stronger and remains unproved. -/
theorem largest_prime_rises_diverging_endpoints_half :
    ∃ D : ℕ → ℕ, Tendsto D atTop atTop ∧
      Tendsto (fun k => (risingCount (D k) : ℝ)/D k) atTop (𝓝 (1/2)) := by
  let R (n : ℕ) : ℝ := if Nat.maxPrimeFac (n+1)>Nat.maxPrimeFac n then 1 else 0
  have hR : ∀ n, |R n| ≤ 1 := by
    intro n
    dsimp [R]
    split_ifs <;> norm_num
  obtain ⟨D,hD,hlim⟩ := exists_diverging_prefixMean_limit R hR (1/2)
    largest_prime_rises_harmonic_half
  refine ⟨D,hD,?_⟩
  simpa [prefixMean,R,risingCount,← sum_filter] using hlim

/-- The lower and upper natural densities bracket one half. Equality of
these two densities, which would settle the conjecture, is not asserted. -/
theorem largest_prime_rises_lower_upper_density :
    {n | Nat.maxPrimeFac (n+1)>Nat.maxPrimeFac n}.lowerDensity ≤ 1/2 ∧
      (1/2 : ℝ) ≤ {n | Nat.maxPrimeFac (n+1)>Nat.maxPrimeFac n}.upperDensity := by
  let S : Set ℕ := {n | Nat.maxPrimeFac (n+1)>Nat.maxPrimeFac n}
  have hlo : IsBoundedUnder (· ≥ ·) atTop (S.partialDensity Set.univ) :=
    isBoundedUnder_of_eventually_ge (a := (0 : ℝ))
      (Eventually.of_forall fun N => by dsimp [Set.partialDensity]; positivity)
  have hhi : IsBoundedUnder (· ≤ ·) atTop (S.partialDensity Set.univ) :=
    isBoundedUnder_of_eventually_le
      (Eventually.of_forall fun N => Set.partialDensity_le_one S Set.univ N)
  have hnear (ε : ℝ) (hε : 0 < ε) :
      ∃ᶠ N : ℕ in atTop, |S.partialDensity Set.univ N-1/2| < ε := by
    rw [frequently_atTop]
    intro M
    obtain ⟨N,hN,hh⟩ := largest_prime_rises_arbitrarily_late_near_half ε hε M
    exact ⟨N,hN,by simpa only [S,rising_partialDensity] using hh⟩
  constructor
  · apply le_of_forall_pos_le_add
    intro ε hε
    have hf : ∃ᶠ N : ℕ in atTop, S.partialDensity Set.univ N ≤ 1/2+ε :=
      (hnear ε hε).mono fun N hn => by have := (abs_lt.mp hn).2; linarith
    exact liminf_le_of_frequently_le hf hlo
  · apply le_of_forall_pos_le_add
    intro ε hε
    have hf : ∃ᶠ N : ℕ in atTop, 1/2-ε ≤ S.partialDensity Set.univ N :=
      (hnear ε hε).mono fun N hn => by have := (abs_lt.mp hn).1; linarith
    have hh := le_limsup_of_frequently_le hf hhi
    change 1/2-ε ≤ S.upperDensity at hh
    change 1/2 ≤ S.upperDensity+ε
    linarith

#print axioms largest_prime_rises_lower_upper_density
#print axioms largest_prime_rises_arbitrarily_late_near_half
#print axioms largest_prime_rises_diverging_endpoints_half
end Erdos371
