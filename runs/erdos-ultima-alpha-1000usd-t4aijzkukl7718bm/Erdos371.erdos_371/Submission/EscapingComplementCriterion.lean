import Submission.SmoothLongComplement

/-! Removing the long smooth component with a further controlled diagonal.
The remaining indices contain a prime above a growing smoothness cutoff;
no signed cancellation of those escaping indices is proved. -/
namespace Erdos371
open Finset Filter FiniteSieve
open scoped Topology

lemma exists_smooth_long_cutoff (B D U : ℕ → ℕ) (hB : Tendsto B atTop atTop)
    (hU : ∀ k : ℕ, ∀ᶠ N in atTop, (B N)^k ≤ U N) :
    ∃ Y : ℕ → ℕ, Tendsto Y atTop atTop ∧ (∀ᶠ N in atTop, Y N ≤ U N) ∧
      (∀ k : ℕ, ∀ᶠ N in atTop, (B N)^k ≤ Y N) ∧
      Tendsto (fun N : ℕ => (∑ n ∈ range N,
        |smoothComplementAfterAt (B N) (D N) (U N) (Y N) (n+1)|)/N) atTop (𝓝 0) := by
  classical
  let P (N a : ℕ) : Prop := (B N)^a ≤ U N ∧
    (∑ n ∈ range N, |smoothComplementAfterAt (B N) (D N) (U N) ((B N)^a) (n+1)|)/(N : ℝ) ≤ 1/(a+1 : ℝ)
  have hP (a : ℕ) : ∀ᶠ N in atTop, P N a := by
    filter_upwards [hU a,(smoothComplementAfterAt_absolute_zero B D U hB hU a).eventually_lt_const
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
      (sum_nonneg fun n _ => abs_nonneg _) (Nat.cast_nonneg N)) _
      (tendsto_one_div_add_atTop_nhds_zero_nat.comp hA)
    exact hPA.mono fun N hp => hp.2

lemma rough_divisor_smooth_iff (B m e Y : ℕ) (he : e ∣ roughRadical B m) (he1 : 1 < e) :
    e.primeFactors ⊆ largePrimeSet B Y ↔ Nat.maxPrimeFac e ≤ Y := by
  have he0 : e ≠ 0 := by omega
  constructor
  · intro h
    have hp : Nat.maxPrimeFac e ∈ e.primeFactors := Nat.mem_primeFactors.mpr
      ⟨Nat.prime_maxPrimeFac_of_one_lt e he1,Nat.maxPrimeFac_dvd,he0⟩
    exact ((mem_largePrimeSet_iff _ B Y).mp (h hp)).2.2
  · intro h p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpd := Nat.dvd_of_mem_primeFactors hp
    exact (mem_largePrimeSet_iff p B Y).mpr ⟨hpp,
      roughRadical_prime_large B m p hpp (hpd.trans he),
      (Nat.le_maxPrimeFac he0 hpp hpd).trans h⟩

noncomputable def escapingComplementAfterAt (B D U Y n : ℕ) : ℝ :=
  (ArithmeticFunction.moebius (roughRadical B (n*(n+1))) : ℝ)*
    ∑ e ∈ (roughRadical B (n*(n+1))).divisors,
      if U < e ∧ Y < Nat.maxPrimeFac e ∧ D*e < roughRadical B (n*(n+1)) then
        (ArithmeticFunction.moebius e : ℝ)*divisorSideColour n (roughRadical B (n*(n+1))/e) else 0

lemma complementAfterAt_smooth_add_escaping (B D U Y n : ℕ) (hU : 1 ≤ U) :
    complementAfterAt B D U n=
      smoothComplementAfterAt B D U Y n+escapingComplementAfterAt B D U Y n := by
  unfold complementAfterAt smoothComplementAfterAt escapingComplementAfterAt
  rw [← mul_add,← sum_add_distrib]
  congr 1
  apply sum_congr rfl
  intro e he
  by_cases h : U < e
  · have he1 : 1 < e := lt_of_le_of_lt hU h
    simp only [rough_divisor_smooth_iff B _ e Y (Nat.mem_divisors.mp he).1 he1]
    by_cases hs : Nat.maxPrimeFac e ≤ Y <;>
      by_cases hd : D*e < roughRadical B (n*(n+1)) <;> simp [h,hs,hd]
  · simp [h]

/-- The long sum and its prime-escaping portion have the same limiting
mean once the smooth absolute error has been removed. -/
lemma long_complement_zero_iff_escaping (B D U Y : ℕ → ℕ)
    (hU : Tendsto U atTop atTop)
    (hsmooth : Tendsto (fun N : ℕ => (∑ n ∈ range N,
      |smoothComplementAfterAt (B N) (D N) (U N) (Y N) (n+1)|)/N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, complementAfterAt (B N) (D N) (U N) (n+1))/N) atTop (𝓝 0) ↔
    Tendsto (fun N : ℕ => (∑ n ∈ range N, escapingComplementAfterAt (B N) (D N) (U N) (Y N) (n+1))/N)
      atTop (𝓝 0) := by
  have hs : Tendsto (fun N : ℕ => (∑ n ∈ range N,
      smoothComplementAfterAt (B N) (D N) (U N) (Y N) (n+1))/N) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hsmooth
    apply Eventually.of_forall
    intro N
    rw [Real.norm_eq_abs,abs_div,abs_of_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
    exact div_le_div_of_nonneg_right (abs_sum_le_sum_abs _ _) (Nat.cast_nonneg N)
  have hd : Tendsto (fun N : ℕ =>
      (∑ n ∈ range N, complementAfterAt (B N) (D N) (U N) (n+1))/N-
      (∑ n ∈ range N, escapingComplementAfterAt (B N) (D N) (U N) (Y N) (n+1))/N) atTop (𝓝 0) := by
    apply hs.congr'
    filter_upwards [hU.eventually_ge_atTop 1] with N hu
    simp only [complementAfterAt_smooth_add_escaping (B N) (D N) (U N) (Y N) _ hu,sum_add_distrib,add_div,add_sub_cancel_right]
  constructor
  · intro h
    have ht := h.sub hd
    simp only [sub_zero] at ht
    convert ht using 1
    funext N
    ring
  · intro h
    simpa only [sub_add_cancel,add_zero] using hd.add h

/-- A further unconditional reduction. Y dominates every fixed B-power,
yet the remaining large-prime-weighted sum is NOT estimated here. -/
theorem exists_escaping_complement_criterion :
    ∃ B H U Y : ℕ → ℕ,
      Tendsto B atTop atTop ∧ Tendsto H atTop atTop ∧ Tendsto U atTop atTop ∧ Tendsto Y atTop atTop ∧
      Tendsto (fun N => Real.log (B N+1 : ℝ)/Real.log N) atTop (𝓝 0) ∧
      Tendsto (fun N => Real.log (U N+1 : ℝ)/Real.log N) atTop (𝓝 0) ∧
      (∀ᶠ N in atTop, Y N ≤ U N) ∧ (∀ k : ℕ, ∀ᶠ N in atTop, (B N)^k ≤ Y N) ∧
      ({n | Nat.maxPrimeFac (n+1)>Nat.maxPrimeFac n}.HasDensity (1/2) ↔
        Tendsto (fun N : ℕ =>
          (∑ n ∈ range N, escapingComplementAfterAt (B N) (H N*N) (U N) (Y N) (n+1))/N)
          atTop (𝓝 0)) := by
  obtain ⟨B,H,U,hB,hH,hU,hlog,hlogU,hpowers,hfrac,hiff⟩ := exists_growing_long_complement_criterion
  obtain ⟨Y,hY,hYU,hYpowers,hsmooth⟩ := exists_smooth_long_cutoff B (fun N => H N*N) U hB hpowers
  exact ⟨B,H,U,Y,hB,hH,hU,hY,hlog,hlogU,hYU,hYpowers,
    hiff.trans (long_complement_zero_iff_escaping B (fun N => H N*N) U Y hU hsmooth)⟩

#print axioms exists_escaping_complement_criterion
end Erdos371
