import Submission.ShortPrefixQuantization

/-! A transfer identity involving the actual adjacent largest-prime-factor
comparison sign. The prime-gap term is a finite-label skew correlation, and
the shorter adjacent endpoint remains explicit. -/
namespace Erdos371
open Finset Filter FiniteInformation BlockPrimes EntropyScales

lemma prefixMean_abs_difference_le (T : ℕ) (F G : ℕ → ℝ) :
    |prefixMean T F-prefixMean T G| ≤ prefixMean T (fun n => |F n-G n|) := by
  rw [← prefixMean_sub]
  unfold prefixMean
  rw [abs_div,abs_of_nonneg (Nat.cast_nonneg T : (0 : ℝ) ≤ T)]
  exact div_le_div_of_nonneg_right (abs_sum_le_sum_abs _ _) (Nat.cast_nonneg T)

/-- The true adjacent comparison bias at N/p transfers to a prime-gap skew
correlation of finitely many actual prime-factor labels. No cancellation of
that prime-gap correlation or replacement of N/p by N is assumed. -/
theorem actual_prime_comparison_transfer (H₀ : ℕ) (hH₀ : 8 ≤ H₀) (ε : ℝ) (hε : 0 < ε) :
    ∃ Q > 0, ∃ K > 0, ∀ᶠ N : ℕ in atTop, ∃ n < K,
      |(∑ p ∈ halfBlockPrimes (factorialScale H₀ n),
        (prefixMean (N/p) factorSign -
          prefixMean N (fun m => orderSkew (primeQuantLabel Q N m) (primeQuantLabel Q N (m+p))))) /
            (halfBlockPrimes (factorialScale H₀ n)).card| < ε := by
  obtain ⟨Q,hQ,happrox⟩ := quantFactorSign_short_prefix_approximation (ε/2) (by positivity)
  obtain ⟨K,hK,htrans⟩ := primeQuantLabel_prime_transfer Q H₀ hH₀ (ε/2) (by positivity)
  let B := (range K).sup (factorialScale H₀)
  refine ⟨Q,hQ,K,hK,?_⟩
  filter_upwards [htrans,happrox B] with N htrans happrox
  obtain ⟨n,hn,hskew⟩ := htrans
  refine ⟨n,hn,?_⟩
  have hg := hskew orderSkew orderSkew_abs_le
  let S := halfBlockPrimes (factorialScale H₀ n)
  have hH : factorialScale H₀ n ≤ B := le_sup (mem_range.mpr hn)
  have hS : S.Nonempty := halfBlockPrimes_nonempty _
    (le_trans (by omega : 4 ≤ H₀) (factorialScale_ge H₀ n))
  have he : |(∑ p ∈ S, (prefixMean (N/p) factorSign-prefixMean (N/p) (quantFactorSign Q N))) /
      (S.card : ℝ)| ≤ ε/2 := by
    apply abs_finset_average_le S hS
    intro p hp
    obtain ⟨hpp,hpH⟩ := mem_halfBlockPrimes.mp hp
    exact (prefixMean_abs_difference_le (N/p) factorSign (quantFactorSign Q N)).trans
      (happrox Q le_rfl p hpp.pos (by omega))
  let U : ℝ := (∑ p ∈ S, (prefixMean (N/p) factorSign -
    prefixMean N (fun m => orderSkew (primeQuantLabel Q N m) (primeQuantLabel Q N (m+p)))))/(S.card : ℝ)
  let V : ℝ := (∑ p ∈ S, (prefixMean (N/p) (quantFactorSign Q N) -
    prefixMean N (fun m => orderSkew (primeQuantLabel Q N m) (primeQuantLabel Q N (m+p)))))/(S.card : ℝ)
  have huv : U-V = (∑ p ∈ S,
      (prefixMean (N/p) factorSign-prefixMean (N/p) (quantFactorSign Q N)))/(S.card : ℝ) := by
    dsimp [U,V]
    rw [← sub_div, ← sum_sub_distrib]
    congr 1
    apply sum_congr rfl
    intro p _
    ring
  change |U| < ε
  change |V| < ε/2 at hg
  rw [← huv] at he
  have ht := abs_sub_le U V 0
  simp only [sub_zero] at ht
  linarith

/-- A precise finite-label reformulation of the remaining cancellation task.
The quantization may be arbitrarily fine; a coarse zero-information label is
not sufficient for the reverse implication. -/
theorem density_iff_arbitrarily_fine_quantized_cancellation :
    {n | Nat.maxPrimeFac (n+1) > Nat.maxPrimeFac n}.HasDensity (1/2) ↔
      ∀ ε : ℝ, 0 < ε → ∀ Q₀ : ℕ, ∃ Q ≥ Q₀, 0 < Q ∧
        ∀ᶠ N : ℕ in atTop, |prefixMean N (quantFactorSign Q N)| ≤ ε := by
  rw [density_iff_signed_count]
  simp_rw [← factorSign_sum_eq_count_difference]
  change Tendsto (fun N => prefixMean N factorSign) atTop (nhds 0) ↔ _
  constructor
  · intro hd ε hε Q₀
    obtain ⟨Q₁,hQ₁,ha⟩ := quantFactorSign_uniform_approximation (ε/2) (by positivity)
    let Q := max Q₀ Q₁
    have hQ : 0 < Q := hQ₁.trans_le (le_max_right _ _)
    refine ⟨Q,le_max_left _ _,hQ,?_⟩
    have hs := (Metric.tendsto_nhds.mp hd) (ε/2) (by positivity)
    filter_upwards [ha,hs] with N ha hs
    rw [Real.dist_eq,sub_zero] at hs
    have he := (prefixMean_abs_difference_le N factorSign (quantFactorSign Q N)).trans
      (ha Q (le_max_right _ _))
    have ht := abs_sub_le (prefixMean N (quantFactorSign Q N)) (prefixMean N factorSign) 0
    simp only [sub_zero] at ht
    rw [abs_sub_comm] at he
    linarith
  · intro hc
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨Q₀,hQ₀,ha⟩ := quantFactorSign_uniform_approximation (ε/3) (by positivity)
    obtain ⟨Q,hQ,hQpos,hb⟩ := hc (ε/3) (by positivity) Q₀
    filter_upwards [ha,hb] with N ha hb
    rw [Real.dist_eq,sub_zero]
    have he := (prefixMean_abs_difference_le N factorSign (quantFactorSign Q N)).trans (ha Q hQ)
    have ht := abs_sub_le (prefixMean N factorSign) (prefixMean N (quantFactorSign Q N)) 0
    simp only [sub_zero] at ht
    linarith

#print axioms actual_prime_comparison_transfer
#print axioms density_iff_arbitrarily_fine_quantized_cancellation
end Erdos371
