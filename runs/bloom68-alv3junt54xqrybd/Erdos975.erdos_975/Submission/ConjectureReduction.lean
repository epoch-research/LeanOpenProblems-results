import Submission.RootMeanGeneral

/-!
# The remaining high-degree assertion

All auxiliary limits in the divisor-pairing reduction are established here
from the polynomial hypotheses, rather than assumed. The original universal
assertion is consequently equivalent to existence of finite normalized
balanced-divisor limits in degrees at least three. Neither side of that
universal equivalence is asserted unconditionally.
-/

namespace Erdos975Support

open Filter Polynomial
open scoped Topology

/-- For an admissible high-degree polynomial, the divisor-average limit exists
if and only if its balanced-divisor contribution has a finite limit. -/
theorem high_degree_divisor_average_iff_balanced_limit
    (f : ℤ[X]) (hf : Irreducible f) (hdeg : 3 ≤ f.natDegree)
    (hpos : ∀ᶠ n : ℤ in atTop, 1 ≤ f.eval n) :
    (∃ c > (0 : ℝ), Tendsto
      (fun x : ℝ ↦ flooredPolynomialSum f x / (x * Real.log x)) atTop (𝓝 c)) ↔
      ∃ L : ℝ, Tendsto
        (fun N : ℕ ↦ balancedAlong (polynomialAbsValue f) N /
          ((N : ℝ) * Real.log (N : ℝ))) atTop (𝓝 L) := by
  obtain ⟨κ, hκ, hP⟩ := exists_pos_rootMean_of_irreducible f hf (by omega)
  have hs := tendsto_smallAlong_of_linear_rootCount
    (polynomialAbsValue_pos f hf (by omega)) (polynomialAbsValue_mod_dvd f) hP
  have ho := tendsto_polynomial_overlapAlong_div_mul_log f hdeg
  have he := exists_divisor_limit_iff_exists_balanced_limit hκ hs ho
  constructor
  · rintro ⟨c, hc, ht⟩
    exact he.mp ⟨c, hc, (flooredPolynomialSum_limit_iff f hpos c).mp ht⟩
  · intro hb
    obtain ⟨c, hc, ht⟩ := he.mpr hb
    exact ⟨c, hc, (flooredPolynomialSum_limit_iff f hpos c).mpr ht⟩

/-- Exact reduction of the universal conjecture to the high-degree balanced
limits. This theorem proves an equivalence, not either of its two sides. -/
theorem universal_divisor_average_iff_high_degree_balanced_limits :
    (∀ f : ℤ[X], f.natDegree ≠ 0 → Irreducible f →
      (∀ᶠ n : ℤ in atTop, 1 ≤ f.eval n) →
      ∃ c > (0 : ℝ), Tendsto
        (fun x : ℝ ↦ flooredPolynomialSum f x / (x * Real.log x)) atTop (𝓝 c)) ↔
    (∀ f : ℤ[X], 3 ≤ f.natDegree → Irreducible f →
      (∀ᶠ n : ℤ in atTop, 1 ≤ f.eval n) →
      ∃ L : ℝ, Tendsto
        (fun N : ℕ ↦ balancedAlong (polynomialAbsValue f) N /
          ((N : ℝ) * Real.log (N : ℝ))) atTop (𝓝 L)) := by
  constructor
  · intro h f hdeg hf hpos
    exact (high_degree_divisor_average_iff_balanced_limit f hf hdeg hpos).mp
      (h f (by omega) hf hpos)
  · intro h f hdeg hf hpos
    by_cases hsmall : f.natDegree ≤ 2
    · exact erdos_975_of_natDegree_le_two f hdeg hf hpos hsmall
    · have hlarge : 3 ≤ f.natDegree := by omega
      exact (high_degree_divisor_average_iff_balanced_limit f hf hlarge hpos).mpr
        (h f hlarge hf hpos)

end Erdos975Support
