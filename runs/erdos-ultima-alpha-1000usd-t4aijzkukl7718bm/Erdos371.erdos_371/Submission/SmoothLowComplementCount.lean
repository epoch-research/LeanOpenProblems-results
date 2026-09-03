import Submission.CanonicalLowComplement

/-! Absolute control of long low factors even when an arbitrary high
rough divisor is attached. The high divisor count remains bounded for fixed L. -/
namespace Erdos371
open Finset Filter FiniteSieve
open scoped Topology

theorem smoothComplementCount_mean_zero (B U : ℕ → ℕ)
    (hB : Tendsto B atTop atTop)
    (hU : ∀ k : ℕ, ∀ᶠ N in atTop, (B N)^k ≤ U N) (a : ℕ) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N,
      (smoothComplementCount (B N) (U N) ((B N)^a) (n+1) : ℝ))/N) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let M : ℝ := 16*(a+1)
  obtain ⟨L,hL⟩ := prime_pattern_exponential_tail_uniform M ε hε
  have htlog := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hB)).atTop_div_const
    (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  filter_upwards [hB.eventually_gt_atTop 1,htlog.eventually_ge_atTop 2,hU (a*L),
    eventually_gt_atTop (0 : ℕ)] with N hb hl hu hN
  let P := largePrimeSet (B N) ((B N)^a)
  have hP (p : ℕ) (hp : p ∈ P) : p.Prime := ((mem_largePrimeSet_iff p _ _).mp hp).1
  have hmass : primeReciprocalMass P ≤ M := by
    have hh := short_power_band_mass_upper (B N) a hb hl
    have hnonneg := primeReciprocalMass_nonneg P
    change 2*primeReciprocalMass P ≤ M at hh
    linarith
  have hmean := hL N hN P hP hmass
  have hy : 1 ≤ (B N)^a := Nat.pow_pos (by omega)
  have hprod : ((B N)^a)^L ≤ U N := by rw [← pow_mul]; exact hu
  have hs := sum_le_sum (s := range N) (fun n _ =>
    (smoothComplementCount_high_count_bound (B N) (U N) ((B N)^a) L (n+1) (by omega) hy hprod))
  have hd := div_le_div_of_nonneg_right hs (Nat.cast_nonneg (α := ℝ) N)
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (div_nonneg (sum_nonneg fun n _ => Nat.cast_nonneg _) (Nat.cast_nonneg N))]
  exact hd.trans_lt hmean

lemma exists_smooth_complement_count_cutoff (B U : ℕ → ℕ) (hB : Tendsto B atTop atTop)
    (hU : ∀ k : ℕ, ∀ᶠ N in atTop, (B N)^k ≤ U N) :
    ∃ Y : ℕ → ℕ, Tendsto Y atTop atTop ∧ (∀ᶠ N in atTop, Y N ≤ U N) ∧
      (∀ k : ℕ, ∀ᶠ N in atTop, (B N)^k ≤ Y N) ∧
      Tendsto (fun N : ℕ => (∑ n ∈ range N,
        (smoothComplementCount (B N) (U N) (Y N) (n+1) : ℝ))/N) atTop (𝓝 0) := by
  classical
  let P (N a : ℕ) : Prop := (B N)^a ≤ U N ∧
    (∑ n ∈ range N, (smoothComplementCount (B N) (U N) ((B N)^a) (n+1) : ℝ))/(N : ℝ) ≤ 1/(a+1 : ℝ)
  have hP (a : ℕ) : ∀ᶠ N in atTop, P N a := by
    filter_upwards [hU a,(smoothComplementCount_mean_zero B U hB hU a).eventually_lt_const
      (show (0 : ℝ) < 1/(a+1 : ℝ) by positivity)] with N hu hm
    exact ⟨hu,hm.le⟩
  let A (N : ℕ) := Nat.findGreatest (P N) N
  let Y (N : ℕ) := (B N)^(A N)
  have hA : Tendsto A atTop atTop := by
    apply tendsto_atTop.mpr
    intro a
    filter_upwards [eventually_ge_atTop a,hP a] with N hNa hp
    exact Nat.le_findGreatest hNa hp
  have hPA : ∀ᶠ N in atTop, P N (A N) := by
    filter_upwards [hP 0] with N hp
    exact Nat.findGreatest_spec (Nat.zero_le N) hp
  have hY : Tendsto Y atTop atTop := by
    apply tendsto_atTop.mpr
    intro M
    filter_upwards [hB.eventually_ge_atTop M,hB.eventually_gt_atTop 0,hA.eventually_ge_atTop 1]
      with N hb hb0 ha
    exact hb.trans (by simpa only [pow_one] using Nat.pow_le_pow_right hb0 ha)
  refine ⟨Y,hY,hPA.mono (fun N hp => hp.1),?_,?_⟩
  · intro k
    filter_upwards [hB.eventually_gt_atTop 0,hA.eventually_ge_atTop k] with N hb ha
    exact Nat.pow_le_pow_right hb ha
  · apply squeeze_zero' (Eventually.of_forall fun N => div_nonneg
      (sum_nonneg fun n _ => Nat.cast_nonneg _) (Nat.cast_nonneg N)) _
      (tendsto_one_div_add_atTop_nhds_zero_nat.comp hA)
    exact hPA.mono fun N hp => hp.2

noncomputable def smoothLowComplementCount (B U Y W n : ℕ) : ℕ :=
  ((roughRadical B (n*(n+1))).divisors.filter fun e => U < e/roughRadical W e ∧
    (e/roughRadical W e).primeFactors ⊆ largePrimeSet B Y).card

lemma smoothLowComplementCount_le_product (B U Y W n : ℕ) (hn : 0 < n) :
    smoothLowComplementCount B U Y W n ≤
      smoothComplementCount B U Y n*(roughRadical W (n*(n+1))).divisors.card := by
  let R := roughRadical B (n*(n+1))
  let S := R.divisors.filter fun f => U < f ∧ f.primeFactors ⊆ largePrimeSet B Y
  have hc : smoothLowComplementCount B U Y W n ≤
      (S ×ˢ (roughRadical W (n*(n+1))).divisors).card := by
    apply card_le_card_of_injOn (fun e => (e/roughRadical W e,roughRadical W e))
    · intro e he
      change e ∈ R.divisors.filter _ at he
      obtain ⟨he,hlow,hsmooth⟩ := mem_filter.mp he
      have hed := (Nat.mem_divisors.mp he).1
      change (e/roughRadical W e,roughRadical W e) ∈ _
      apply mem_product.mpr
      refine ⟨mem_filter.mpr ⟨?_,hlow,hsmooth⟩,?_⟩
      · exact Nat.mem_divisors.mpr ⟨(Nat.div_dvd_of_dvd (roughRadical_dvd W e)).trans hed,
          (roughRadical_pos B _).ne'⟩
      · exact Nat.mem_divisors.mpr ⟨roughRadical_dvd_of_dvd W e _ (by positivity)
          (hed.trans (roughRadical_dvd B _)),(roughRadical_pos W _).ne'⟩
    · intro e he f hf hef
      have hp := congrArg (fun p : ℕ × ℕ => p.1*p.2) hef
      dsimp only at hp
      simpa only [Nat.div_mul_cancel (roughRadical_dvd W e),Nat.div_mul_cancel (roughRadical_dvd W f)] using hp
  simpa only [card_product,S,R,smoothComplementCount] using hc

lemma smoothLowComplementCount_sample_bound (B U Y W L N n : ℕ)
    (hW : 1 < W) (hWN : N+1 ≤ W^L) (hn : 0 < n) (hnN : n ≤ N) :
    (smoothLowComplementCount B U Y W n : ℝ) ≤ (2 : ℝ)^(2*L)*smoothComplementCount B U Y n := by
  have hgcard : (roughRadical W (n*(n+1))).divisors.card ≤ 2^(2*L) :=
    (squarefree_divisors_card_le _ (roughRadical_squarefree W _)).trans
      (Nat.pow_le_pow_right (by norm_num) (highRadical_card_bound W L N n hW hWN hn hnN))
  have hh := (smoothLowComplementCount_le_product B U Y W n hn).trans
    (Nat.mul_le_mul_left _ hgcard)
  exact_mod_cast (by simpa only [Nat.mul_comm] using hh)

/-- An arbitrary attached high divisor costs only the fixed factor 2^(2L).
The estimate is absolute, and does not discard the Möbius signs elsewhere. -/
theorem smoothLowComplementCount_mean_zero (B U Y W : ℕ → ℕ) (L : ℕ)
    (hW : ∀ᶠ N : ℕ in atTop, 1 < W N ∧ N+1 ≤ (W N)^L)
    (hcount : Tendsto (fun N : ℕ => (∑ n ∈ range N,
      (smoothComplementCount (B N) (U N) (Y N) (n+1) : ℝ))/N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N,
      (smoothLowComplementCount (B N) (U N) (Y N) (W N) (n+1) : ℝ))/N) atTop (𝓝 0) := by
  have ht := hcount.const_mul ((2 : ℝ)^(2*L))
  simp only [mul_zero] at ht
  apply squeeze_zero' (Eventually.of_forall fun N => div_nonneg
    (sum_nonneg fun n _ => Nat.cast_nonneg _) (Nat.cast_nonneg N)) _ ht
  filter_upwards [hW] with N hw
  rw [← mul_div_assoc,mul_sum]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  apply sum_le_sum
  intro n hn
  exact smoothLowComplementCount_sample_bound _ _ _ _ L N (n+1) hw.1 hw.2
    (by omega) (by have := mem_range.mp hn; omega)

#print axioms smoothComplementCount_mean_zero
#print axioms smoothLowComplementCount_mean_zero
end Erdos371
