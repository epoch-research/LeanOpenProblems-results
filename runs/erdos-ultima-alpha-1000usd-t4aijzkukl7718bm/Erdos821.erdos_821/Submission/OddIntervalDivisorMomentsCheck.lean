import Submission.OddIntervalDivisorMoments
/-! Exact-type and axiom checks for the odd interval. -/
open Erdos821.FullRangeError Erdos821.HigherDivisors

example (N e : ℕ) (he : 0 < e) (hoe : Odd e) (heN : 2*e ≤ N) :
    N ≤ 4*e*((oddLargeModuli N).filter (fun d => e ∣ d)).card :=
  odd_multiples_count_lower N e he hoe heN

example (k N T : ℕ) (hNT : 2*T ≤ N) :
    (N : ℝ)*oddHarmonicMoment k T/4 ≤
      ∑ d ∈ oddLargeModuli N, (tau (k+1) d : ℝ) :=
  odd_interval_divisor_weight_lower k N T hNT

#print axioms mem_oddLargeModuli_iff
#print axioms odd_multiples_count_lower
#print axioms divisor_incidence_weight_le
#print axioms odd_interval_divisor_weight_lower
