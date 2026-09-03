import Submission.ChebyshevFactorialLower
import Submission.SharpSieveDenominator

/-!
# An elementary bounded-error prime-logarithm sum

The factorial identity and the summable contribution of higher prime powers
show that sum_{p<=N} log(p)/p differs from log N by a bounded amount.
No prime number theorem is used.
-/
open Nat Finset Filter ArithmeticFunction
open scoped Classical BigOperators Topology
namespace Erdos821
open AnalyticSieve
set_option maxHeartbeats 3000000

noncomputable def primeLogMass (N : ℕ) : ℝ :=
  ∑ p ∈ (N+1).primesBelow, Real.log (p : ℝ)/(p : ℝ)

lemma primeLogMass_nonneg (N : ℕ) : 0 ≤ primeLogMass N :=
  sum_nonneg (fun p _ => div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p))

lemma summable_nonprime_mangoldt_div :
    Summable (fun n : ℕ => (if n.Prime then 0 else vonMangoldt n)/(n : ℝ)) := by
  have h := vonMangoldt.summable_residueClass_non_primes_div (0 : ZMod 1)
  have he (n : ℕ) : (n : ZMod 1) = 0 := Subsingleton.elim _ _
  simpa [vonMangoldt.residueClass, he] using h

lemma mangoldt_harmonic_le_primeLogMass_add (N : ℕ) :
    (∑ d ∈ Icc 1 N, vonMangoldt d/(d : ℝ)) ≤ primeLogMass N +
      ∑' n : ℕ, (if n.Prime then 0 else vonMangoldt n)/(n : ℝ) := by
  have hp : (Icc 1 N).filter Nat.Prime = (N+1).primesBelow := by
    ext p
    simp only [mem_filter, mem_Icc, Nat.mem_primesBelow]
    constructor
    · rintro ⟨⟨hp1,hpN⟩,hp⟩; exact ⟨by omega,hp⟩
    · rintro ⟨hpN,hp⟩; exact ⟨⟨hp.pos,by omega⟩,hp⟩
  rw [← sum_filter_add_sum_filter_not (Icc 1 N) Nat.Prime, hp]
  have hprime : (∑ p ∈ (N+1).primesBelow, vonMangoldt p/(p : ℝ)) = primeLogMass N := by
    apply sum_congr rfl
    intro p hp
    rw [vonMangoldt_apply_prime (Nat.mem_primesBelow.mp hp).2]
  rw [hprime]
  apply _root_.add_le_add le_rfl
  have hsum := Summable.sum_le_tsum (Icc 1 N)
    (fun n _ => show 0 ≤ (if n.Prime then 0 else vonMangoldt n)/(n : ℝ) by
      split_ifs <;> positivity [vonMangoldt_nonneg (n := n)])
    summable_nonprime_mangoldt_div
  simpa only [sum_filter, ite_not, ite_div, zero_div] using hsum

lemma log_factorial_div_le_mangoldt_harmonic (N : ℕ) (hN : 0 < N) :
    Real.log (N.factorial : ℝ)/(N : ℝ) ≤
      ∑ d ∈ Icc 1 N, vonMangoldt d/(d : ℝ) := by
  apply (div_le_iff₀ (by exact_mod_cast hN : (0 : ℝ) < N)).mpr
  rw [log_factorial_eq_mangoldt_floor_sum, sum_mul]
  apply sum_le_sum
  intro d hd
  have hh := mul_le_mul_of_nonneg_left (Nat.cast_div_le (α := ℝ) (m := N) (n := d))
    (vonMangoldt_nonneg (n := d))
  convert hh using 1
  ring

lemma eventually_primeLogMass_lower :
    ∀ᶠ N : ℕ in atTop,
      Real.log (N : ℝ) - (2 + ∑' n : ℕ,
        (if n.Prime then 0 else vonMangoldt n)/(n : ℝ)) ≤ primeLogMass N := by
  have hlim := tendsto_log_factorial_multiple_residual 1 (by decide)
  simp only [one_mul, Nat.cast_one, Real.log_one, mul_zero, zero_sub] at hlim
  filter_upwards [hlim.eventually (eventually_ge_nhds (by norm_num : (-2 : ℝ) < -1)),
    eventually_ge_atTop 1] with N hlow hN
  have hh := (log_factorial_div_le_mangoldt_harmonic N (by omega)).trans
    (mangoldt_harmonic_le_primeLogMass_add N)
  linarith only [hlow, hh]

/-- A uniform bounded error, including the finitely many small cutoffs. -/
theorem exists_primeLogMass_log_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      |primeLogMass N - Real.log (N : ℝ)| ≤ C := by
  obtain ⟨K,hK⟩ := eventually_atTop.mp eventually_primeLogMass_lower
  let S : ℝ := ∑' n : ℕ, (if n.Prime then 0 else vonMangoldt n)/(n : ℝ)
  have hS : 0 ≤ S := tsum_nonneg (fun n => by
    split_ifs <;> positivity [vonMangoldt_nonneg (n := n)])
  have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  refine ⟨(K : ℝ)+S+2+Real.log 4, by positivity, ?_⟩
  intro N hN
  apply abs_le.mpr
  constructor
  · by_cases hKN : K ≤ N
    · have hh := hK N hKN
      change Real.log (N : ℝ) - (2+S) ≤ primeLogMass N at hh
      linarith [Nat.cast_nonneg (α := ℝ) K]
    · have hNK : (N : ℝ) ≤ K := by exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge hKN))
      have hlog := Real.log_le_sub_one_of_pos (by exact_mod_cast (show 0 < N by omega) : (0 : ℝ) < N)
      have hp := primeLogMass_nonneg N
      linarith only [hNK,hlog,hp,hS,hl4]
  · have hh := Sieve.sum_prime_log_div_le_log_add N (by omega)
    change primeLogMass N ≤ Real.log (N : ℝ)+Real.log 4 at hh
    linarith [Nat.cast_nonneg (α := ℝ) K]

end Erdos821
