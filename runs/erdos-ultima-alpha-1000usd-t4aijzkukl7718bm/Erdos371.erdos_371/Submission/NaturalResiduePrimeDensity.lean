import Submission.BoundedIkehara
import Submission.AbelResiduePrimeDensity

/-! Natural summatory asymptotics for von Mangoldt and log-weighted primes in
fixed residue classes. Unlike the preceding Abel-density theorem, these are
ordinary initial-interval averages. -/
namespace Erdos371.AbelPrimes
open Finset Filter ArithmeticFunction ArithmeticFunction.vonMangoldt
open scoped Topology
set_option autoImplicit false

lemma nonnegative_mean_zero_of_summable_div (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n)
    (hs : Summable (fun n => c n/n)) :
    Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, c n)/(N : ℝ)) atTop (𝓝 0) := by
  let F := fun N n : ℕ => if n ∈ Icc 1 N then c n/(N : ℝ) else 0
  have hlim (n : ℕ) : Tendsto (fun N => F N n) atTop (𝓝 0) := by
    rcases n.eq_zero_or_pos with rfl | hn
    · simp only [F,mem_Icc,not_le.mpr (by omega : (0 : ℕ) < 1),false_and,if_false]
      exact tendsto_const_nhds
    · apply ((tendsto_const_nhds (x := c n)).div_atTop (tendsto_natCast_atTop_atTop (R := ℝ))).congr'
      filter_upwards [eventually_ge_atTop n] with N hN
      simp only [F,if_pos (mem_Icc.mpr ⟨hn,hN⟩)]
  have hdom : ∀ N n, ‖F N n‖ ≤ c n/n := by
    intro N n
    dsimp only [F]
    split_ifs with hn
    · obtain ⟨hn,hN⟩ := mem_Icc.mp hn
      rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg (hc n) (Nat.cast_nonneg N))]
      exact div_le_div_of_nonneg_left (hc n) (by exact_mod_cast hn : (0 : ℝ) < n)
        (by exact_mod_cast hN)
    · simp only [norm_zero]
      exact div_nonneg (hc n) (Nat.cast_nonneg n)
  have ht := tendsto_tsum_of_dominated_convergence hs hlim (Eventually.of_forall hdom)
  simp only [tsum_zero] at ht
  have he (N : ℕ) : (∑' n, F N n) = (∑ n ∈ Icc 1 N, c n)/(N : ℝ) := by
    rw [tsum_eq_sum (s := Icc 1 N) (fun n hn => by simp only [F,if_neg hn]),sum_div]
    apply sum_congr rfl
    intro n hn
    simp only [F,if_pos hn]
  simpa only [he] using ht

lemma residue_summatory_bound {q : ℕ} (a : ZMod q) (N : ℕ) :
    (∑ n ∈ Icc 1 N, residueClass a n) ≤ (Real.log 4+4)*N := by
  calc
    _ ≤ ∑ n ∈ Icc 1 N, vonMangoldt n := sum_le_sum (fun n _ => residueClass_le a n)
    _ = Chebyshev.psi (N : ℝ) := by
      simp only [Chebyshev.psi,Nat.floor_natCast]
      congr 1
    _ ≤ _ := Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg N)

/-- The fixed-unit-residue prime number theorem with von Mangoldt weights. -/
theorem residue_natural_mangoldt_limit {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a) :
    Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, residueClass a n)/(N : ℝ)) atTop
      (𝓝 ((q.totient : ℝ)⁻¹)) := by
  apply FourierBoundary.bounded_ikehara_nat (residueClass a) (residueClass_nonneg a)
    (Real.log 4+4) (by linarith [Real.log_pos (by norm_num : (1 : ℝ) < 4)])
    (residue_summatory_bound a) ((q.totient : ℝ)⁻¹) (LFunctionResidueClassAux a)
    (continuousOn_LFunctionResidueClassAux a)
  intro s hs
  have he := eqOn_LFunctionResidueClassAux ha hs
  rw [he]
  simp only [Complex.ofReal_inv,Complex.ofReal_natCast,sub_add_cancel]

/-- The higher prime powers have zero ordinary mean, using the already
proved summability of their reciprocal-weighted coefficients. -/
theorem nonprime_residue_natural_mean_zero {q : ℕ} (a : ZMod q) :
    Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, nonprimeResidueCoeff a n)/(N : ℝ)) atTop (𝓝 0) :=
  nonnegative_mean_zero_of_summable_div _ (nonprimeResidueCoeff_nonneg a)
    (summable_residueClass_non_primes_div a)

lemma residue_prime_nonprime_sum {q : ℕ} (a : ZMod q) (N : ℕ) :
    (∑ n ∈ Icc 1 N, primeResidueCoeff a n) =
      (∑ n ∈ Icc 1 N, residueClass a n)-(∑ n ∈ Icc 1 N, nonprimeResidueCoeff a n) := by
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro n _
  unfold primeResidueCoeff nonprimeResidueCoeff
  split_ifs <;> simp

theorem prime_residue_natural_limit_unit {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a) :
    Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, primeResidueCoeff a n)/(N : ℝ)) atTop
      (𝓝 ((q.totient : ℝ)⁻¹)) := by
  have ht := (residue_natural_mangoldt_limit ha).sub (nonprime_residue_natural_mean_zero a)
  simpa only [sub_zero,← sub_div,← residue_prime_nonprime_sum] using ht

theorem prime_residue_natural_limit_nonunit {q : ℕ} [NeZero q] {a : ZMod q} (ha : ¬IsUnit a) :
    Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, primeResidueCoeff a n)/(N : ℝ)) atTop (𝓝 0) := by
  apply nonnegative_mean_zero_of_summable_div _ (primeResidueCoeff_nonneg a)
  apply summable_of_ne_finset_zero (s := range (q+1))
  intro n hn
  rw [primeResidueCoeff_eq_zero_of_gt ha n (by simp only [mem_range] at hn; omega),zero_div]

theorem prime_residue_natural_limit (q : ℕ) [NeZero q] (a : ZMod q) :
    Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, primeResidueCoeff a n)/(N : ℝ)) atTop
      (𝓝 (if IsUnit a then (q.totient : ℝ)⁻¹ else 0)) := by
  classical
  by_cases ha : IsUnit a
  · rw [if_pos ha]
    exact prime_residue_natural_limit_unit ha
  · rw [if_neg ha]
    exact prime_residue_natural_limit_nonunit ha

#print axioms residue_natural_mangoldt_limit
#print axioms prime_residue_natural_limit
end Erdos371.AbelPrimes
