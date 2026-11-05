import Submission.TreeSupply
import Submission.Supply
import Submission.Lift
import Submission.CRT

/-! An unconditional counterexample family for the distinct-subset-sums statement. -/

namespace ErdosDSS

/-- Arbitrarily small ratios of the largest element to the power of two
of the set cardinality, witnessed by positive sum-distinct natural sets. -/
theorem counterFamily :
    ∀ J : ℕ, 0 < J → ∃ (N : ℕ) (A : Finset ℕ),
      (A ⊆ Finset.Icc 1 N ∧
        (fun (⟨S, _⟩ : A.powerset) => S.sum id).Injective) ∧
      N ≠ 0 ∧ 4 ^ J * N < 3 ^ J * 2 ^ A.card :=
  blockSupply_counterFamily
    (codeSupply_blockSupply (treeSupply_codeSupply TreeCode.Construction.treeSupply))

/-- The counterexample family rules out every positive uniform real constant. -/
theorem not_erdosStatement :
    ¬ (∃ C > (0 : ℝ), ∀ (N : ℕ) (A : Finset ℕ),
      (A ⊆ Finset.Icc 1 N ∧
        (fun (⟨S, _⟩ : A.powerset) => S.sum id).Injective) →
      N ≠ 0 → C * 2 ^ A.card < N) :=
  blockSupply_not_erdosStatement
    (codeSupply_blockSupply (treeSupply_codeSupply TreeCode.Construction.treeSupply))

end ErdosDSS
