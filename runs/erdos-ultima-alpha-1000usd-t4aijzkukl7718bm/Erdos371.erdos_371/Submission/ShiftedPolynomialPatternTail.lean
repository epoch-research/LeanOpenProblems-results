import Submission.PolynomialPatternTail

/-! The polynomial tail estimate on the shifted sample n+1. Both endpoints
are kept explicit, and the initial nonnegative contribution is discarded. -/
namespace Erdos371.FiniteSieve
open Finset Filter
open scoped Topology

theorem prime_pattern_polynomial_tail_shifted (k : ℕ) (M ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℕ, k+1 < R ∧ ∀ᶠ N : ℕ in atTop, ∀ P : Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ (p : ℝ) ≤ (N : ℝ)^(1/(4*(k+3 : ℝ)))) →
      (2*∑ p ∈ P, (1 : ℝ)/p) ≤ M →
      (∑ n ∈ range N, if R ≤ (activePrimeAtoms P (n+1)).card then
        subsetPolynomial k (activePrimeAtoms P (n+1)).card else 0)/(N : ℝ) < ε := by
  obtain ⟨R,hR,htail⟩ := prime_pattern_polynomial_tail k M (ε/2) (by positivity)
  refine ⟨R,hR,?_⟩
  have hs := (tendsto_add_atTop_nat 1).eventually htail
  filter_upwards [hs,eventually_ge_atTop (1 : ℕ)] with N hN hN1
  intro P hP hmass
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hP' : ∀ p ∈ P, p.Prime ∧ (p : ℝ) ≤ ((N+1 : ℕ) : ℝ)^(1/(4*(k+3 : ℝ))) := by
    intro p hp
    exact ⟨(hP p hp).1,(hP p hp).2.trans
      (Real.rpow_le_rpow hNr.le (by push_cast; linarith) (by positivity))⟩
  have hh := hN P hP' hmass
  let f : ℕ → ℝ := fun n => if R ≤ (activePrimeAtoms P n).card then
    subsetPolynomial k (activePrimeAtoms P n).card else 0
  have hf (n : ℕ) : 0 ≤ f n := by
    dsimp only [f]
    split_ifs
    · exact subsetPolynomial_nonneg _ _
    · rfl
  have he : (∑ n ∈ range N, f (n+1)) ≤ ∑ n ∈ range (N+1), f n := by
    rw [sum_range_succ']
    exact le_add_of_nonneg_right (hf 0)
  have hsum := (div_lt_iff₀ (show (0 : ℝ) < (N+1 : ℕ) by positivity)).mp hh
  have hcast : ((N+1 : ℕ) : ℝ) ≤ 2*N := by
    push_cast
    have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    linarith
  change (∑ n ∈ range N, f (n+1))/(N : ℝ) < ε
  apply (div_lt_iff₀ hNr).mpr
  have hh' : (∑ n ∈ range (N+1), f n) < ε/2*((N+1 : ℕ) : ℝ) := hsum
  have hm := mul_le_mul_of_nonneg_left hcast (show 0 ≤ ε/2 by positivity)
  linarith

#print axioms prime_pattern_polynomial_tail_shifted
end Erdos371.FiniteSieve
