import Submission.FiniteThinningApproximation
import Submission.DyadicLaplaceObstruction

/-! Dyadic submultiplicativity of void probabilities is false for actual
finite prime sets. Large-prime padding transfers the checked three-prime
Laplace counterexample with a proved finite error. This is NOT the negation
of the quadratic Jacobsthal conjecture. -/
namespace Erdos970.GapAverages.FiniteThinning
open Finset Real

lemma laplace_le_one (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (t : ℝ) (ht : 0 ≤ t) (m : ℕ) : countLaplace P t m ≤ 1 := by
  rw [← phaseMean_const P hP 1]
  apply phaseMean_mono
  intro r
  apply exp_le_one_iff.mpr
  have hc : 0 ≤ intervalCount P m r := by
    apply sum_nonneg
    intro x _
    rcases point_eq_zero_or_one P x r with h | h <;> simp [h]
  exact mul_nonpos_of_nonpos_of_nonneg (by linarith) hc

/-- There exists a genuine finite prime set with V(52)>V(26)^2. The added
primes may be extremely large; no unverified finite computation is used. -/
theorem exists_dyadic_void_failure :
    ∃ Q : Finset ℕ, (∀ p ∈ Q, p.Prime) ∧
      coveredFraction Q 26 ^ 2 < coveredFraction Q (2*26) := by
  let P := DyadicExample.primes
  have hP : ∀ p ∈ P, p.Prime := DyadicExample.primes_prime
  let a := countLaplace P (log 64) 26
  let b := countLaplace P (log 64) 52
  have ha0 : 0 ≤ a := countLaplace_nonneg P (log 64) 26
  have ha1 : a ≤ 1 := laplace_le_one P hP (log 64) (log_nonneg (by norm_num)) 26
  have hb1 : b ≤ 1 := laplace_le_one P hP (log 64) (log_nonneg (by norm_num)) 52
  have hgap : 0 < b-a^2 := sub_pos.mpr DyadicExample.dyadic_laplace_failure
  let η : ℝ := (b-a^2)/8
  have hη : 0 < η := div_pos hgap (by norm_num)
  have hη1 : η ≤ 1 := by dsimp [η]; nlinarith [sq_nonneg a]
  obtain ⟨R,hdis,hR,happrox⟩ := exists_padding_approx P hP 52 η hη
  let Q := P ∪ R
  have hQ : ∀ p ∈ Q, p.Prime := by
    intro p hp
    rcases mem_union.mp hp with hp | hp
    · exact hP p hp
    · exact (hR p hp).1
  have hx := happrox 26 (by omega)
  have hy := happrox 52 le_rfl
  change |coveredFraction Q 26-a| < η at hx
  change |coveredFraction Q 52-b| < η at hy
  have hx0 : 0 ≤ coveredFraction Q 26 := by
    unfold coveredFraction phaseMean
    exact div_nonneg (sum_nonneg (fun r _ => by split_ifs <;> norm_num)) (by positivity)
  have hxupper : coveredFraction Q 26 ≤ a+η := by linarith [(abs_lt.mp hx).2]
  have hs := pow_le_pow_left₀ hx0 hxupper 2
  have hm := mul_le_mul_of_nonneg_right ha1 hη.le
  have hηsq := mul_le_mul_of_nonneg_right hη1 hη.le
  have hsq : coveredFraction Q 26 ^ 2 ≤ a^2+3*η := by nlinarith
  have hylo : b-η < coveredFraction Q 52 := by linarith [(abs_lt.mp hy).1]
  refine ⟨Q,hQ,?_⟩
  change coveredFraction Q 26 ^ 2 < coveredFraction Q 52
  dsimp [η] at hsq hylo
  linarith

/-- An unrestricted dyadic void inequality would have implied the refuted
Laplace inequality after dilution. It therefore cannot be used as a lemma
in a proof of Erdős970. -/
theorem not_uniform_dyadic_void :
    ¬∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → ∀ m : ℕ,
      coveredFraction P (2*m) ≤ coveredFraction P m ^ 2 := by
  intro h
  obtain ⟨P,hP,hbad⟩ := exists_dyadic_void_failure
  exact hbad.not_ge (h P hP 26)

#print axioms exists_dyadic_void_failure
#print axioms not_uniform_dyadic_void
end Erdos970.GapAverages.FiniteThinning
