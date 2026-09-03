import Submission.PrimeNumberTheoremAP
import Submission.AbelCyclicPrimeSkew
import Submission.BlockPrimeCount

/-! Ordinary prime-average cancellation for fixed periodic odd functions and
fixed cyclic antisymmetric observables. No uniformity in the period or in a
varying process is asserted. -/
namespace Erdos371.AbelPrimes
open Finset Filter
open scoped Topology
set_option autoImplicit false

lemma prime_periodic_indicator_expansion {q : ℕ} [NeZero q] (g : ZMod q → ℝ) (n : ℕ) :
    (if n.Prime then g (n : ZMod q) else 0) = ∑ a : ZMod q, g a*primeResidueIndicator a n := by
  classical
  by_cases hp : n.Prime
  · simp [primeResidueIndicator,hp,eq_comm]
  · simp [primeResidueIndicator,hp]

lemma prime_periodic_sum_expansion {q : ℕ} [NeZero q] (g : ZMod q → ℝ) (N : ℕ) :
    (∑ p ∈ initialPrimes N, g (p : ZMod q)) = ∑ a : ZMod q, g a*(residuePrimeCount a N : ℝ) := by
  classical
  rw [initialPrimes,sum_filter]
  simp_rw [prime_periodic_indicator_expansion]
  rw [sum_comm]
  apply sum_congr rfl
  intro a _
  rw [← mul_sum]
  congr 1
  exact plainSum_primeResidueIndicator a N

lemma prime_periodic_scaled_sum_limit {q : ℕ} [NeZero q] (g : ZMod q → ℝ) :
    Tendsto (fun N : ℕ => (∑ p ∈ initialPrimes N, g (p : ZMod q))*Real.log N/(N : ℝ)) atTop
      (𝓝 (∑ a : ZMod q, g a*(if IsUnit a then (q.totient : ℝ)⁻¹ else 0))) := by
  classical
  have ht := tendsto_finset_sum (univ : Finset (ZMod q))
    (fun a _ => (prime_number_theorem_AP q a).const_mul (g a))
  apply ht.congr'
  apply Eventually.of_forall
  intro N
  simp only [prime_periodic_sum_expansion,sum_mul,sum_div]
  apply sum_congr rfl
  intro a _
  ring

/-- The ordinary prime average of a fixed periodic function is its uniform
average over the invertible residues. -/
theorem prime_periodic_natural_limit {q : ℕ} [NeZero q] (g : ZMod q → ℝ) :
    Tendsto (fun N : ℕ => (∑ p ∈ initialPrimes N, g (p : ZMod q))/((initialPrimes N).card : ℝ)) atTop
      (𝓝 (∑ a : ZMod q, g a*(if IsUnit a then (q.totient : ℝ)⁻¹ else 0))) := by
  classical
  have ht := (prime_periodic_scaled_sum_limit g).div prime_number_theorem_initial one_ne_zero
  simp only [div_one] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  simp only [Pi.div_apply]
  rw [div_div_div_cancel_right₀ hn.ne',mul_div_mul_right _ _ hlog.ne']

/-- In particular, opposite residues cancel for a fixed odd periodic
function. This is now an ordinary prime average, not a Dirichlet--Abel one. -/
theorem prime_periodic_odd_natural_limit {q : ℕ} [NeZero q] (g : ZMod q → ℝ)
    (hg : ∀ a, g (-a) = -g a) :
    Tendsto (fun N : ℕ => (∑ p ∈ initialPrimes N, g (p : ZMod q))/((initialPrimes N).card : ℝ)) atTop
      (𝓝 0) := by
  simpa only [unit_residue_sum_odd g hg] using prime_periodic_natural_limit g

/-- The same assertion for the prime family used in the entropy transfer.
`halfBlockPrimes H` means primes at most `H/2`, not the dyadic band `(H/2,H]`. -/
theorem halfBlock_periodic_odd_natural_limit {q : ℕ} [NeZero q] (g : ZMod q → ℝ)
    (hg : ∀ a, g (-a) = -g a) :
    Tendsto (fun H : ℕ => (∑ p ∈ BlockPrimes.halfBlockPrimes H, g (p : ZMod q))/
      ((BlockPrimes.halfBlockPrimes H).card : ℝ)) atTop (𝓝 0) := by
  have ht := (prime_periodic_odd_natural_limit g hg).comp
    (Nat.tendsto_div_const_atTop (by norm_num : (2 : ℕ) ≠ 0))
  simpa only [Function.comp_def,initialPrimes_eq_primesBelow,BlockPrimes.halfBlockPrimes] using ht

/-- Every fixed cyclic process has zero ordinary prime-average skew for
antisymmetric real pair observables. The cycle is fixed before the limit. -/
theorem fixed_cyclic_prime_skew_natural_limit {q : ℕ} [NeZero q] {A : Type*}
    (L : ZMod q → A) (C : A → A → ℝ) (hC : ∀ a b, C b a = -C a b) :
    Tendsto (fun H : ℕ => (∑ p ∈ BlockPrimes.halfBlockPrimes H, cyclicSkew L C (p : ZMod q))/
      ((BlockPrimes.halfBlockPrimes H).card : ℝ)) atTop (𝓝 0) :=
  halfBlock_periodic_odd_natural_limit _ (cyclicSkew_odd L C hC)

#print axioms prime_periodic_natural_limit
#print axioms fixed_cyclic_prime_skew_natural_limit
end Erdos371.AbelPrimes
