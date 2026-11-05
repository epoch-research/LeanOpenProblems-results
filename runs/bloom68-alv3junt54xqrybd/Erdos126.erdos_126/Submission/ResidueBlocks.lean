import Submission.ResidueBlockColors
import Submission.ResidueBlockDifference

/-!
# Finite paired-residue representation of the prime excess kernel

For any finite family of positive natural labels and any finite set of
primes, this constructs finite weighted paired blocks.  Every block is
valid and each prime owns a coherent family.  The full cross kernel is
exactly `primeExcessKernel`; for distinct labels the same-side kernel is
bounded by the prime-factor valuation of their natural distance, less
the same baseline.

Neither injectivity nor prime-support completeness is assumed.  Those
hypotheses belong to the subsequent off-diagonal sign and cardinal-bound
arguments, not to this representation theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos126Aux.ResidueBlocks

variable {ι : Type*} [Fintype ι]

/-- The canonical cutoff yields the exact excess kernel on every entry,
including diagonal entries and repeated labels. -/
theorem crossSum_eq (a : ι → ℕ) (ha : ∀ i, 0 < a i) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (i j : ι) :
    Paired.crossSum (nodeBlock a S (sumCutoff a S)) i j = primeExcessKernel a S i j := by
  apply crossSum_eq_primeExcessKernel a S (sumCutoff a S) ha hS
  intro p hp i j
  exact factorization_add_le_sumCutoff a S p hp i j

/-- Explicit representation using the occupied-node subtype.  All
finiteness instances and constructors are exported from the imported
modules; the node type is `Node a S (sumCutoff a S)`. -/
theorem representation (a : ι → ℕ) (ha : ∀ i, 0 < a i) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) :
    (∀ t : Node a S (sumCutoff a S), (nodeBlock a S (sumCutoff a S) t).Valid) ∧
    (∀ p : ↥S, Paired.Coherent (nodeBlock a S (sumCutoff a S))
      (Finset.univ.filter (fun t => owner a S (sumCutoff a S) t = p))) ∧
    (∀ i j, Paired.crossSum (nodeBlock a S (sumCutoff a S)) i j = primeExcessKernel a S i j) ∧
    (∀ i j, a i ≠ a j → Paired.diagSum (nodeBlock a S (sumCutoff a S)) i j ≤
      (∑ p ∈ S, Real.log (p : ℝ) * ((Nat.dist (a i) (a j)).factorization p : ℝ)) -
        primeBaselineSum a S i j) := by
  exact ⟨nodeBlock_valid a S (sumCutoff a S), nodeBlock_coherent a S (sumCutoff a S),
    crossSum_eq a ha S hS,
    fun i j hij => diagSum_le_distance_excess a S (sumCutoff a S) ha hS i j hij⟩

/-- A type-independent packaging of `representation`.  The witness
`Fintype` instance is explicit so the result can be unpacked with
`letI := inst` before invoking the paired-matrix APIs. -/
theorem exists_representation (a : ι → ℕ) (ha : ∀ i, 0 < a i) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) :
    ∃ (τ : Type) (inst : Fintype τ) (b : τ → Paired.Block ι) (owner : τ → ↥S),
      (∀ t, (b t).Valid) ∧
      (∀ p : ↥S, Paired.Coherent b
        ((@Finset.univ τ inst).filter (fun t => owner t = p))) ∧
      (∀ i j, @Paired.crossSum ι τ inst b i j = primeExcessKernel a S i j) ∧
      (∀ i j, a i ≠ a j → @Paired.diagSum ι τ inst b i j ≤
        (∑ p ∈ S, Real.log (p : ℝ) * ((Nat.dist (a i) (a j)).factorization p : ℝ)) -
          primeBaselineSum a S i j) := by
  refine ⟨Node a S (sumCutoff a S), inferInstance, nodeBlock a S (sumCutoff a S),
    owner a S (sumCutoff a S), ?_⟩
  exact representation a ha S hS

end Erdos126Aux.ResidueBlocks
