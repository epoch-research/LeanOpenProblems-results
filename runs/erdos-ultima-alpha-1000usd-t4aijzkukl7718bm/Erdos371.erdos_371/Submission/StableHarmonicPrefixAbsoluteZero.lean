import Submission.HarmonicPrefixBiasAnchor
import Submission.ComponentwiseHarmonicPrefixTransfer

/-! L1 logarithmic cancellation of the ordinary prefix means of bounded
skew observables of fixed finite mean-stable labels. This is an almost-all-
logarithmic-scales statement, not convergence at every ordinary endpoint. -/
namespace Erdos371.FiniteInformation
open Finset Filter MeasureTheory DilationSpectrum BlockPrimes EntropyScales
open scoped Topology
set_option autoImplicit false
set_option maxHeartbeats 800000

variable {A : Type*} [Fintype A] [DecidableEq A] [TopologicalSpace A] [DiscreteTopology A]
    [MeasurableSpace A] [BorelSpace A]

lemma harmonicPrefixBias_zero_of_word_limit
    (L : ℕ → A)
    (hL : ∀ p, 0 < p → Tendsto (fun N => prefixMean N (labelDilationDefect p L)) atTop (𝓝 0))
    (D : ℕ → ℕ) (hD : Tendsto D atTop atTop) (μ : ProbabilityMeasure (ℕ → A))
    (hlim : Tendsto (fun j => harmonicEmpirical (D j) (wordOrbit L)) atTop (𝓝 μ))
    (C : A → A → ℝ) (hC : ∀ x y, C y x = -C x y) (hCb : ∀ x y, |C x y| ≤ 1) :
    Tendsto (fun j => harmonicPrefixBias (D j) (fun n => C (L n) (L (n+1)))) atTop (𝓝 0) := by
  have hμ := harmonic_word_limit_measurePreserving L D hD μ hlim
  have hdom := harmonic_word_limit_dilation_cylinder L hL D hD μ hlim
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ : ℝ := min (ε/32) (1/2)
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδε : δ ≤ ε/32 := min_le_left _ _
  have hδh : δ ≤ 1/2 := min_le_right _ _
  let a : ℝ := (1-δ)/2
  let b : ℝ := 1/2
  have ha : 0 < a := by dsimp [a]; linarith
  have hab : a < b := by dsimp [a,b]; linarith
  let c : ℝ := (b-a)/2
  have hc : 0 < c := half_pos (sub_pos.mpr hab)
  obtain ⟨HG,hgap⟩ := harmonicPrefixPrimeSkewL1_narrow_eventually L D hD μ hlim hμ hdom
    a b ha hab (ε/8) (by positivity)
  obtain ⟨HC,hcount⟩ := eventually_atTop.mp (narrowPrimeBand_eventual_count_lower a b ha hab)
  let H₀ := max 8 (max HG HC)
  have hH₀ : 8 ≤ H₀ := le_max_left _ _
  have hGH₀ : HG ≤ H₀ := (le_max_left HG HC).trans (le_max_right _ _)
  have hCH₀ : HC ≤ H₀ := (le_max_right HG HC).trans (le_max_right _ _)
  let S : ℕ → Finset ℕ := narrowPrimeBand a b
  have hS (H : ℕ) (_ : H₀ ≤ H) : S H ⊆ halfBlockPrimes H :=
    narrowPrimeBand_subset_halfBlock a b le_rfl H
  have hcard (H : ℕ) (hH : H₀ ≤ H) : c*H/Real.log (H : ℝ) ≤ (S H).card :=
    hcount H (hCH₀.trans hH)
  obtain ⟨K,hK,htransfer⟩ := componentwise_harmonic_prefix_prime_subset_transfer
    (A := A) H₀ hH₀ (ε/8) c (by positivity) hc S hS hcard
  have htrans := hD.eventually htransfer
  let H (n : Fin K) := factorialScale H₀ n
  let q (n : Fin K) := linearPrimeEndpoint b (H n)
  have hHH (n : Fin K) : H₀ ≤ H n := factorialScale_ge H₀ n
  have hq (n : Fin K) : 0 < q n := by
    apply Nat.floor_pos.mpr
    dsimp [b]
    have hh : (8 : ℝ) ≤ H n := by exact_mod_cast hH₀.trans (hHH n)
    linarith
  have hnon (n : Fin K) : (S (H n)).Nonempty := by
    apply card_pos.mp
    have hHr : 0 < (H n : ℝ) := by exact_mod_cast (show 0 < H n by have := hHH n; omega)
    have hlog : 0 < Real.log (H n : ℝ) := Real.log_pos (by
      exact_mod_cast (show 1 < H n by have := hHH n; omega))
    exact_mod_cast (div_pos (mul_pos hc hHr) hlog).trans_le (hcard (H n) (hHH n))
  have hP (n : Fin K) (p : ℕ) (hp : p ∈ S (H n)) : 0 < p ∧ p ≤ q n := by
    exact ⟨(mem_halfBlockPrimes.mp (hS (H n) (hHH n) hp)).1.pos,
      (narrowPrimeBand_member_bounds a b (H n) p hp).2⟩
  have hclose (n : Fin K) (p : ℕ) (hp : p ∈ S (H n)) : (1-δ)*(q n : ℝ) ≤ p := by
    have hbq : (q n : ℝ) ≤ b*(H n : ℝ) := Nat.floor_le (by dsimp [b]; positivity)
    have hh := mul_le_mul_of_nonneg_left hbq (by linarith : 0 ≤ 1-δ)
    have hp' := (narrowPrimeBand_member_bounds a b (H n) p hp).1
    dsimp [a,b] at hh hp'
    nlinarith
  have hgapall : ∀ᶠ j : ℕ in atTop, ∀ n : Fin K,
      harmonicPrefixPrimeSkewL1 (D j) L (S (H n)) (fun _ => C) < ε/8 := by
    apply eventually_all.mpr
    intro n
    filter_upwards [hgap (H n) (hGH₀.trans (hHH n))] with j hj
    exact hj (fun _ => C) (fun _ => hC) (fun _ => hCb)
  have herrall : ∀ᶠ j : ℕ in atTop, ∀ n : Fin K,
      mean (harmonicPrefixLaw (D j)) (fun i => |(∑ p ∈ S (H n),
        naturalAdjacentTransferError p (harmonicPrefixLength (D j) i) L C)/((S (H n)).card : ℝ)|) < ε/8 := by
    apply eventually_all.mpr
    intro n
    have ht := (harmonicPrefixAdjacentTransferError_average_zero L hL (S (H n))
      (fun p hp => (hP n p hp).1) C hCb).comp hD
    exact ht.eventually_lt_const (by positivity : (0 : ℝ)<ε/8)
  have htailall : ∀ᶠ j : ℕ in atTop, ∀ n : Fin K,
      (5*(q n : ℝ)+12)/(harmonic (D j+1) : ℝ) < ε/8 := by
    apply eventually_all.mpr
    intro n
    have ht : Tendsto (fun j => (5*(q n : ℝ)+12)/(harmonic (D j+1) : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (harmonic_real_tendsto.comp hD)
    exact ht.eventually_lt_const (by positivity : (0 : ℝ)<ε/8)
  filter_upwards [htrans,hgapall,herrall,htailall] with j htrans hgapall herrall htailall
  obtain ⟨n,hn,hdisc⟩ := htrans L
  let k : Fin K := ⟨n,hn⟩
  have hd := hdisc (fun _ => C) (fun _ => hCb)
  change mean (harmonicPrefixLaw (D j)) (fun i => |(∑ p ∈ S (H k),
    naturalGapDiscrepancy (harmonicPrefixLength (D j) i) p L C)/((S (H k)).card : ℝ)|) < ε/8 at hd
  have hb := harmonicPrefixBias_transfer_bound (D j) (q k) (hq k) L C hCb (S (H k)) (hnon k)
    (hP k) δ hδ.le (hclose k)
  have hnonneg : 0 ≤ harmonicPrefixBias (D j) (fun n => C (L n) (L (n+1))) :=
    mean_nonneg_of_nonneg _ _ (fun i => abs_nonneg _)
  rw [Real.dist_eq,sub_zero,abs_of_nonneg hnonneg]
  have hg := hgapall k
  have he := herrall k
  have ht := htailall k
  linarith

/-- Natural prefix skew vanishes in L1 over logarithmically sampled
endpoints. This is NOT the all-endpoint natural-density assertion. -/
theorem stable_finite_labels_harmonic_prefix_abs_zero
    (L : ℕ → A)
    (hL : ∀ p, 0 < p → Tendsto (fun N => prefixMean N (labelDilationDefect p L)) atTop (𝓝 0))
    (C : A → A → ℝ) (hC : ∀ x y, C y x = -C x y) (hCb : ∀ x y, |C x y| ≤ 1) :
    Tendsto (fun N => harmonicPrefixBias N (fun n => C (L n) (L (n+1)))) atTop (𝓝 0) := by
  apply tendsto_of_subseq_tendsto
  intro D hD
  obtain ⟨μ,φ,hφ,hlim⟩ := exists_harmonicEmpirical_limit (wordOrbit L) D
  refine ⟨φ,?_⟩
  exact harmonicPrefixBias_zero_of_word_limit L hL (D ∘ φ) (hD.comp hφ.tendsto_atTop) μ hlim C hC hCb

#print axioms harmonicPrefixBias_zero_of_word_limit
#print axioms stable_finite_labels_harmonic_prefix_abs_zero
end Erdos371.FiniteInformation
