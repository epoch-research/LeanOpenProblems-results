import Submission.RoughThinEndpoint
import Submission.RoughDivisorEndpoint

/-! A high rough divisor in a logarithmically thin band near N occurs on a
set of density zero. Both consecutive factors are sampled explicitly. -/
namespace Erdos371
open Finset Filter FiniteSieve
open scoped Topology

noncomputable def roughEndpointDivisors (W A N : ℕ) : Finset ℕ := by
  classical
  exact (Icc A N).filter fun d => Squarefree d ∧ ∀ p ∈ d.primeFactors, W < p

lemma roughEndpointDivisors_reciprocals_zero (A W : ℕ → ℕ) (L : ℕ) (hL : 0 < L)
    (hW : ∀ᶠ N : ℕ in atTop, N ≤ (W N)^L)
    (hA : ∀ᶠ N : ℕ in atTop, 1 ≤ A N ∧ A N ≤ N)
    (hlogA : Tendsto (fun N : ℕ => Real.log (A N)/Real.log N) atTop (𝓝 1)) :
    Tendsto (fun N : ℕ => ∑ d ∈ roughEndpointDivisors (W N) (A N) N, (1 : ℝ)/d) atTop (𝓝 0) := by
  apply rough_thin_endpoint_reciprocals_zero _ A W L hL hW hA hlogA
  apply Eventually.of_forall
  intro N d hd
  obtain ⟨hdI,hdSq,hr⟩ := mem_filter.mp hd
  obtain ⟨hdA,hdN⟩ := mem_Icc.mp hdI
  refine ⟨hdA,hdN,?_⟩
  intro p hp hpd
  obtain ⟨hpW,hpp⟩ := Nat.mem_primesBelow.mp hp
  have hpl := hr p (Nat.mem_primeFactors.mpr ⟨hpp,hpd,hdSq.ne_zero⟩)
  omega

noncomputable def highEndpointCount (W A N : ℕ) : ℕ :=
  ((range N).filter fun n => ∃ d ∈ Icc A N, d ∣ roughRadical W ((n+1)*(n+2))).card

lemma highEndpointCount_proportion_le (W A N L : ℕ) (hW : 1 < W) (hWN : N ≤ W^L) :
    (highEndpointCount W A N : ℝ)/N ≤
      (2 : ℝ)^(L+1)*(∑ d ∈ roughEndpointDivisors W A N, (1 : ℝ)/d) := by
  have hc : highEndpointCount W A N ≤
      ((range N).filter fun n => ∃ d ∈ roughEndpointDivisors W A N, d ∣ (n+1)*(n+2)).card := by
    apply card_le_card
    intro n hn
    obtain ⟨hn,d,hdI,hd⟩ := mem_filter.mp hn
    refine mem_filter.mpr ⟨hn,d,?_,hd.trans (roughRadical_dvd W _)⟩
    apply mem_filter.mpr
    refine ⟨hdI,(roughRadical_squarefree W _).squarefree_of_dvd hd,?_⟩
    intro p hp
    exact roughRadical_prime_large W _ p (Nat.prime_of_mem_primeFactors hp) ((Nat.dvd_of_mem_primeFactors hp).trans hd)
  apply (div_le_div_of_nonneg_right (show (highEndpointCount W A N : ℝ) ≤ (((range N).filter fun n => ∃ d ∈ roughEndpointDivisors W A N, d ∣ (n+1)*(n+2)).card : ℝ) by exact_mod_cast hc)
    (Nat.cast_nonneg N)).trans
  apply rough_divisor_event_proportion_le (roughEndpointDivisors W A N) W L N hW hWN
  intro d hd
  obtain ⟨hdI,hdSq,hr⟩ := mem_filter.mp hd
  exact ⟨hdSq,(mem_Icc.mp hdI).2,hr⟩

/-- Thin high endpoint events have zero natural proportion for each fixed L. -/
theorem highEndpointCount_proportion_zero (A W : ℕ → ℕ) (L : ℕ) (hL : 0 < L)
    (hW : ∀ᶠ N : ℕ in atTop, 1 < W N ∧ N ≤ (W N)^L)
    (hA : ∀ᶠ N : ℕ in atTop, 1 ≤ A N ∧ A N ≤ N)
    (hlogA : Tendsto (fun N : ℕ => Real.log (A N)/Real.log N) atTop (𝓝 1)) :
    Tendsto (fun N : ℕ => (highEndpointCount (W N) (A N) N : ℝ)/N) atTop (𝓝 0) := by
  have hr := (roughEndpointDivisors_reciprocals_zero A W L hL (hW.mono fun N h => h.2) hA hlogA).const_mul
    ((2 : ℝ)^(L+1))
  simp only [mul_zero] at hr
  apply squeeze_zero' (Eventually.of_forall fun N => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) _ hr
  exact hW.mono fun N h => highEndpointCount_proportion_le _ _ _ L h.1 h.2

theorem highEndpoint_indicator_mean_zero (A W : ℕ → ℕ) (L : ℕ) (hL : 0 < L)
    (hW : ∀ᶠ N : ℕ in atTop, 1 < W N ∧ N ≤ (W N)^L)
    (hA : ∀ᶠ N : ℕ in atTop, 1 ≤ A N ∧ A N ≤ N)
    (hlogA : Tendsto (fun N : ℕ => Real.log (A N)/Real.log N) atTop (𝓝 1)) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N,
      if ∃ d ∈ Icc (A N) N, d ∣ roughRadical (W N) ((n+1)*(n+2)) then (1 : ℝ) else 0)/N) atTop (𝓝 0) := by
  simpa only [sum_boole,highEndpointCount] using highEndpointCount_proportion_zero A W L hL hW hA hlogA

#print axioms highEndpointCount_proportion_zero
#print axioms highEndpoint_indicator_mean_zero
end Erdos371
