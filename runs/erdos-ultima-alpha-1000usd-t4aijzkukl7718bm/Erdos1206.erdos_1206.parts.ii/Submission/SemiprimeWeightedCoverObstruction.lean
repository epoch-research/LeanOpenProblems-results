import Submission.SmallQuadraticDivisorWeights
import Submission.SquarefreeSummablePrimeObstruction
import Submission.WeightedDivisorCover

/-! Summable nonnegative weights supported on primes and semiprimes cannot
fractionally cover all cubic collisions. Arbitrary composites are not covered. -/
namespace Erdos1206.SemiprimeWeightedCoverObstruction
open Finset SquarefreeConicFamily QuadraticSemiprimeDivisibility
open scoped Classical
set_option maxHeartbeats 2000000

lemma collision_small_total (w : ℕ → ℝ) (hw : ∀ p, 0 ≤ w p)
    (hsupp : ∀ d, ¬LowComplexity d → w d=0)
    (hs : Summable (fun d : ℕ => w d/d))
    {t : ℝ} (ht : 0 < t) :
    ∃ n : Fin 4 → ℕ, (∀ i, 0 < n i) ∧
      n 0 < n 1 ∧ n 1 < n 2 ∧ n 2 < n 3 ∧
      (n 0)^3+(n 3)^3=(n 1)^3+(n 2)^3 ∧ (∑i,divisorWeight w (n i)) < t := by
  obtain ⟨x,hxpos,hx⟩ := SmallQuadraticDivisorWeights.exists_small_total a b c
    (by intro i; fin_cases i <;> norm_num [c])
    SquarefreeSummablePrimeObstruction.anisotropic_reversed
    (by intro i; fin_cases i <;> norm_num [a,b,c])
    SquarefreeSummablePrimeObstruction.local_units_nat w hw hsupp hs ht
  obtain ⟨h0,h01,h12,h23⟩ := SquarefreeSummablePrimeObstruction.ordered_of_first_pos x.1 x.2 hxpos
  refine ⟨fun i => F i x.1 x.2,?_,h01,h12,h23,identity x.1 x.2,hx⟩
  intro i
  fin_cases i <;> dsimp <;> omega

/-- This excludes fractional weights supported on divisors with one or two
prime factors counted with multiplicity, including prime squares. -/
theorem no_summable_low_complexity_weight_cover (w : ℕ → ℝ) (hw : ∀ d, 0 ≤ w d)
    (hsupp : ∀ d : ℕ, ¬LowComplexity d → w d=0)
    (hs : Summable (fun d : ℕ => w d/d)) :
    ¬IsWeightedCubeDivisorCover w := by
  intro hcover
  obtain ⟨n,hn,h01,h12,h23,he,hsmall⟩ := collision_small_total w hw hsupp hs (by norm_num : (0:ℝ)<1)
  have hh := hcover (n 0) (n 3) (n 1) (n 2) (hn 0) (hn 3) (hn 1) (hn 2)
    he h01.ne (h01.trans h12).ne
  simp only [Fin.sum_univ_succ] at hsmall
  change divisorWeight w (n 0)+(divisorWeight w (n 1)+(divisorWeight w (n 2)+(divisorWeight w (n 3)+0))) < 1 at hsmall
  linarith

/-- No positive low-weight band for these summable nonnegative divisor
weights has Sidon cubes. -/
theorem low_divisorWeight_not_sidon (w : ℕ → ℝ) (hw : ∀ p, 0 ≤ w p)
    (hsupp : ∀ d, ¬LowComplexity d → w d=0)
    (hs : Summable (fun d : ℕ => w d/d))
    {t : ℝ} (ht : 0 < t) :
    ¬IsSidon ((fun n : ℕ => n^3) '' {n : ℕ | 0 < n ∧ divisorWeight w n < t}) := by
  intro hsidon
  obtain ⟨n,hn,h01,h12,h23,he,hsmall⟩ := collision_small_total w hw hsupp hs ht
  have hmem (i : Fin 4) : n i∈{n : ℕ | 0 < n ∧ divisorWeight w n < t} := by
    refine ⟨hn i,lt_of_le_of_lt ?_ hsmall⟩
    apply single_le_sum (f := fun j => divisorWeight w (n j)) _ (mem_univ i)
    intro j _
    exact divisorWeight_nonneg hw _
  have hh := hsidon _ ⟨n 0,hmem 0,rfl⟩ _ ⟨n 1,hmem 1,rfl⟩
    _ ⟨n 3,hmem 3,rfl⟩ _ ⟨n 2,hmem 2,rfl⟩ he
  rcases hh with hh | hh
  · have heq := Nat.pow_left_injective (by decide : 3≠0) hh.1
    omega
  · have heq := Nat.pow_left_injective (by decide : 3≠0) hh.1
    omega

#print axioms collision_small_total
#print axioms no_summable_low_complexity_weight_cover
#print axioms low_divisorWeight_not_sidon
end Erdos1206.SemiprimeWeightedCoverObstruction
