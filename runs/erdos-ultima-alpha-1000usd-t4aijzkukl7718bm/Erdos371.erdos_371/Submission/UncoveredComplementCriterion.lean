import Submission.JointFullEndpointCutoffs
import Submission.EscapingComplementCriterion

/-! An exact remaining arithmetic sum after simultaneous ordinary-prefix,
smooth-long, and full-high mixed-rectangle cancellation. This file does not
assert cancellation of the uncovered remainder. -/
namespace Erdos371
open Finset Filter FiniteSieve
open scoped Topology

lemma mixedComplementSupport_has_large_prime (B W F X n e : ℕ)
    (he : e ∈ mixedComplementSupport B W F X n) : W < Nat.maxPrimeFac e := by
  obtain ⟨fg,hfg,rfl⟩ := mem_image.mp he
  obtain ⟨hf,hg⟩ := mem_product.mp hfg
  obtain ⟨hfd,hfF⟩ := mem_filter.mp hf
  obtain ⟨hgd,hg1,hgX⟩ := mem_filter.mp hg
  have hfpos := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hfd).1 (roughRadical_pos B _)
  have hgp := Nat.minFac_prime (show fg.2 ≠ 1 by omega)
  have hpR := (Nat.minFac_dvd fg.2).trans (Nat.mem_divisors.mp hgd).1
  have hpE : fg.2.minFac ∣ fg.1*fg.2 := (Nat.minFac_dvd fg.2).trans (dvd_mul_left _ _)
  have hE0 : fg.1*fg.2 ≠ 0 := by positivity
  exact (roughRadical_prime_large W _ _ hgp hpR).trans_le (Nat.le_maxPrimeFac hE0 hgp hpE)

lemma mixedComplementSupport_above_prefix (B W F X n e : ℕ) (hFW : F ≤ W)
    (he : e ∈ mixedComplementSupport B W F X n) : F < e := by
  have hh := mixedComplementSupport_has_large_prime B W F X n e he
  exact hFW.trans_lt (hh.trans_le (Nat.maxPrimeFac_le (n := e)))

noncomputable def uncoveredComplementAt (B D U Y W X n : ℕ) : ℝ :=
  (ArithmeticFunction.moebius (roughRadical B (n*(n+1))) : ℝ)*
    ∑ e ∈ (roughRadical B (n*(n+1))).divisors,
      if U < e ∧ Y < Nat.maxPrimeFac e ∧ e ∉ mixedComplementSupport B W U X n ∧
        D*e < roughRadical B (n*(n+1)) then
        (ArithmeticFunction.moebius e : ℝ)*divisorSideColour n (roughRadical B (n*(n+1))/e) else 0

lemma escapingComplementAfterAt_mixed_add_uncovered (B D U Y W X n : ℕ)
    (hBW : B ≤ W) (hUW : U ≤ W) (hYW : Y ≤ W) :
    escapingComplementAfterAt B D U Y n=
      mixedComplementRectangleAt B D W U X n+uncoveredComplementAt B D U Y W X n := by
  rw [mixedComplementRectangleAt_original_support B D W U X n hBW hUW]
  unfold escapingComplementAfterAt uncoveredComplementAt
  rw [← mul_add,← sum_add_distrib]
  congr 1
  apply sum_congr rfl
  intro e he
  by_cases hm : e ∈ mixedComplementSupport B W U X n
  · have hU := mixedComplementSupport_above_prefix B W U X n e hUW hm
    have hY := hYW.trans_lt (mixedComplementSupport_has_large_prime B W U X n e hm)
    by_cases hd : D*e < roughRadical B (n*(n+1)) <;> simp [hm,hU,hY,hd]
  · by_cases hU : U < e <;> by_cases hY : Y < Nat.maxPrimeFac e <;>
      by_cases hd : D*e < roughRadical B (n*(n+1)) <;> simp [hm,hU,hY,hd]

lemma escaping_zero_iff_uncovered (B H U Y W : ℕ → ℕ)
    (hBW : ∀ᶠ N : ℕ in atTop, B N ≤ W N)
    (hUW : ∀ᶠ N : ℕ in atTop, U N ≤ W N)
    (hYW : ∀ᶠ N : ℕ in atTop, Y N ≤ W N)
    (hmixed : Tendsto (fun N : ℕ => (∑ n ∈ range N,
      mixedComplementRectangleAt (B N) (H N*N) (W N) (U N) N (n+1))/N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N,
      escapingComplementAfterAt (B N) (H N*N) (U N) (Y N) (n+1))/N) atTop (𝓝 0) ↔
    Tendsto (fun N : ℕ => (∑ n ∈ range N,
      uncoveredComplementAt (B N) (H N*N) (U N) (Y N) (W N) N (n+1))/N) atTop (𝓝 0) := by
  have hid : (fun N : ℕ => (∑ n ∈ range N,
      escapingComplementAfterAt (B N) (H N*N) (U N) (Y N) (n+1))/N) =ᶠ[atTop]
      (fun N : ℕ => (∑ n ∈ range N,
        mixedComplementRectangleAt (B N) (H N*N) (W N) (U N) N (n+1))/N+
        (∑ n ∈ range N, uncoveredComplementAt (B N) (H N*N) (U N) (Y N) (W N) N (n+1))/N) := by
    filter_upwards [hBW,hUW,hYW] with N hb hu hy
    simp only [escapingComplementAfterAt_mixed_add_uncovered (B N) (H N*N) (U N) (Y N) (W N) N _ hb hu hy,
      sum_add_distrib,add_div]
  constructor
  · intro h
    have hh := (h.congr' hid).sub hmixed
    simp only [sub_zero,add_sub_cancel_left] at hh
    exact hh
  · intro h
    have hh := hmixed.add h
    simp only [add_zero] at hh
    exact hh.congr' hid.symm

/-- The two formerly separate cutoff constructions are now compatible.
Only the displayed uncovered mean remains to be estimated; this is an
unconditional equivalence, not a proof of the density conjecture. -/
theorem exists_uncovered_complement_criterion (W : ℕ → ℕ) (L : ℕ) (hL : 0 < L)
    (hW : ∀ᶠ N : ℕ in atTop, 1 < W N ∧ N+1 ≤ (W N)^L) :
    ∃ B H U Y : ℕ → ℕ,
      Tendsto B atTop atTop ∧ Tendsto H atTop atTop ∧ Tendsto U atTop atTop ∧ Tendsto Y atTop atTop ∧
      Tendsto (fun N => Real.log (B N+1 : ℝ)/Real.log N) atTop (𝓝 0) ∧
      Tendsto (fun N => Real.log (U N+1 : ℝ)/Real.log N) atTop (𝓝 0) ∧
      (∀ᶠ N : ℕ in atTop, Y N ≤ U N ∧ U N ≤ W N) ∧
      (∀ k : ℕ, ∀ᶠ N in atTop, (B N)^k ≤ Y N) ∧
      ({n | Nat.maxPrimeFac (n+1)>Nat.maxPrimeFac n}.HasDensity (1/2) ↔
        Tendsto (fun N : ℕ => (∑ n ∈ range N,
          uncoveredComplementAt (B N) (H N*N) (U N) (Y N) (W N) N (n+1))/N) atTop (𝓝 0)) := by
  obtain ⟨B,H,U,C,hB,hH,hU,hlog,hlogU,hHB,hC,hbudget,hClim,hpowers,hUW,hmixed,hplain⟩ :=
    exists_joint_growing_full_cutoffs W L hL hW
  have hsmall : Tendsto (fun N : ℕ => (∑ n ∈ range N,
      roughSmallDivisorSum (B N) (H N*N) (n+1))/N) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hClim
    filter_upwards [hbudget] with N hp
    rw [norm_div,Real.norm_natCast,Real.norm_eq_abs]
    exact div_le_div_of_nonneg_right (hp N) (Nat.cast_nonneg N)
  have hshort : Tendsto (fun N : ℕ => (∑ n ∈ range N,
      complementPrefixAt (B N) (H N*N) (U N) (n+1))/N) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [hplain ε hε] with N hm
    simpa only [Real.dist_eq,sub_zero] using hm (U N) le_rfl
  have hmix : Tendsto (fun N : ℕ => (∑ n ∈ range N,
      mixedComplementRectangleAt (B N) (H N*N) (W N) (U N) N (n+1))/N) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [hmixed ε hε] with N hm
    simpa only [Real.dist_eq,sub_zero] using hm (U N) le_rfl
  obtain ⟨Y,hY,hYU,hYpowers,hsmooth⟩ := exists_smooth_long_cutoff B (fun N => H N*N) U hB hpowers
  have hBW : ∀ᶠ N : ℕ in atTop, B N ≤ W N := by
    filter_upwards [hpowers 1,hUW] with N hb hu
    have hb' : B N ≤ U N := by simpa only [pow_one] using hb
    exact hb'.trans hu
  have hYW : ∀ᶠ N : ℕ in atTop, Y N ≤ W N := by
    filter_upwards [hYU,hUW] with N hy hu
    exact hy.trans hu
  refine ⟨B,H,U,Y,hB,hH,hU,hY,hlog,hlogU,?_,hYpowers,?_⟩
  · filter_upwards [hYU,hUW] with N hy hu
    exact ⟨hy,hu⟩
  · exact (density_iff_long_complement B H U hH hlog hsmall hshort).trans
      ((long_complement_zero_iff_escaping B (fun N => H N*N) U Y hU hsmooth).trans
        (escaping_zero_iff_uncovered B H U Y W hBW hUW hYW hmix))

#print axioms exists_uncovered_complement_criterion
end Erdos371
