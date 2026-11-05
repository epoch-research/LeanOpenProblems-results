import FormalConjecturesUtil

/-!
# Erdős Problem 1057

*References:*
- [erdosproblems.com/1057](https://www.erdosproblems.com/1057)
- [AGP94] Alford, W. R. and Granville, Andrew and Pomerance, Carl, There are infinitely many
  Carmichael numbers. Ann. of Math. (2) (1994), 703--722.
- [Er56c] Erdős, P., On pseudoprimes and Carmichael numbers. Publ. Math. Debrecen (1956),
  201--206.
- [Gu04] Guy, Richard K., Unsolved problems in number theory. (2004), xviii+437.
- [Ha08] Harman, Glyn, Watt's mean value theorem and Carmichael numbers. Int. J. Number Theory
  (2008), 241--248.
- [Li22] J. D. Lichtman, Primes in arithmetic progressions to large moduli and shifted primes
  without large prime factors. arXiv:2211.09641 (2022).
- [Po89] Pomerance, Carl, Two methods in elementary analytic number theory. (1989), 135--161.
-/

open Nat Real Filter Set
open scoped Topology Asymptotics

namespace Erdos1057

/--
Let $C(x)$ count the number of Carmichael numbers in the interval $[1,x]$.
-/
noncomputable def carmichaelCounting (x : ℝ) : ℝ :=
  ({n : ℕ | IsCarmichael n ∧ (n : ℝ) ≤ x}.ncard : ℝ)

/--
Is it true that $C(x)=x^{1-o(1)}$?

This is discussed in problem A13 of Guy's collection [Gu04].
-/
theorem erdos_1057 :
    Tendsto (fun x ↦ Real.log (carmichaelCounting x) / Real.log x) atTop (𝓝 1) := by
  sorry

end Erdos1057

theorem Erdos1057.erdos_1057.disproof : ¬ (type_of% @Erdos1057.erdos_1057) := sorry
