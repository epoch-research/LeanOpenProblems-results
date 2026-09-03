import Submission.WideTailMeasure
import Submission.AlmostEverywherePairs

/-! The almost-everywhere version of Erdős 972. The universal conjecture still
requires excluding every exceptional irrational slope individually. -/
namespace Erdos972MetricConjecture

open MeasureTheory Filter
open Erdos972Topology Erdos972RichSlopes Erdos972WideTailMeasure
open Erdos972AlmostEverywherePairs (ae_mem_of_local_measure_lower)

lemma ae_mem_primeTail_bounded (A N : ℕ) (hA : 1 ≤ A) :
    ∀ᵐ α : ℝ, 1 < α → α < A → α ∈ primeTail N := by
  apply ae_mem_of_local_measure_lower (isOpen_primeTail N).measurableSet
    (κ := 1 / 320000) (by norm_num)
  intro a b ha hab hb
  have h := localTail_measure_lower A hA ha hab hb N
  linarith

/-- For almost every real slope above one, there are infinitely many primes `p`
whose floor output is also prime. This is a measure-theoretic result, not the
universal statement in `Spec.lean`. -/
theorem ae_irrational_infinite_prime_pairs :
    ∀ᵐ α : ℝ, 1 < α → Irrational α ∧ (primeSet α).Infinite := by
  have ht : ∀ᵐ α : ℝ, ∀ A N : ℕ, 1 ≤ A → 1 < α → α < A → α ∈ primeTail N := by
    apply ae_all_iff.mpr
    intro A
    apply ae_all_iff.mpr
    intro N
    by_cases hA : 1 ≤ A
    · filter_upwards [ae_mem_primeTail_bounded A N hA] with α hα
      exact fun _ => hα
    · exact Eventually.of_forall fun _ h => (hA h).elim
  filter_upwards [ht, ae_irrational] with α hα hI
  intro hα1
  obtain ⟨A, hAα⟩ := exists_nat_gt α
  have hA : 1 ≤ A := by exact_mod_cast (show (1 : ℝ) ≤ A by linarith)
  refine ⟨hI, (infinite_iff_mem_all_primeTail (by linarith) hI).mpr ?_⟩
  intro N
  exact hα A N hA hα1 hAα

/-- In particular, the set of counterexample slopes has Lebesgue measure zero. -/
theorem counterexampleSlopes_null :
    volume {α : ℝ | 1 < α ∧ Irrational α ∧ (primeSet α).Finite} = 0 := by
  apply measure_mono_null (t := {α : ℝ | ¬ (1 < α → Irrational α ∧ (primeSet α).Infinite)})
    _ (ae_iff.mp ae_irrational_infinite_prime_pairs)
  intro α hα hgood
  exact ((hgood hα.1).2) hα.2.2

#print axioms ae_irrational_infinite_prime_pairs
#print axioms counterexampleSlopes_null

end Erdos972MetricConjecture
