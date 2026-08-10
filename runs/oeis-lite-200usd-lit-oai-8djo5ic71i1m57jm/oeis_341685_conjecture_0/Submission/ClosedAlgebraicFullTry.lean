import FormalConjectures.Util.ProblemImports
open Nat BigOperators Algebra Set
instance : Fact (Nat.Prime 3) := by constructor; norm_num
noncomputable def xi_3 : Padic 3 := tsum (fun k : ℕ => (Nat.factorial k : Padic 3))

#check isClosed_setOf_isAlgebraic
#print axioms isClosed_setOf_isAlgebraic
#check Padic.denseRange_ratCast
#check Padic.denseRange_algebraMap
#check DenseRange.closure_eq
#check DenseRange.closure_range
#check IsClosed.closure_subset_iff

example : IsAlgebraic ℚ xi_3 := by
  let S : Set (Padic 3) := {x | IsAlgebraic ℚ x}
  have hclosed : IsClosed S := by
    exact isClosed_setOf_isAlgebraic ℚ (Padic 3)
  have hrange : Set.range (algebraMap ℚ (Padic 3)) ⊆ S := by
    intro x hx
    rcases hx with ⟨q, rfl⟩
    exact isAlgebraic_algebraMap q
  have hdense : DenseRange (algebraMap ℚ (Padic 3)) := by
    exact Padic.denseRange_ratCast (p := 3)
  have hclosure : closure (Set.range (algebraMap ℚ (Padic 3))) ⊆ S := by
    exact hclosed.closure_subset_iff.mpr hrange
  have hxmem : xi_3 ∈ closure (Set.range (algebraMap ℚ (Padic 3))) := by
    rw [hdense.closure_range]
    exact trivial
  exact hclosure hxmem

#print axioms ClosedAlgebraicFullTry._example_1
