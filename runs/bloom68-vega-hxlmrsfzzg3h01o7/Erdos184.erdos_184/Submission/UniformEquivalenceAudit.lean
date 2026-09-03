import Submission.UniformEquivalence

/-!
# Audit of the uniform-bound equivalences

The references to `erdos_184` below occur only inside `type_of%`: we read its
proposition, never its admitted proof. The main converse and both target
equivalences are checked against that exact type, universe-polymorphically.
An additional check covers the canonical decomposition when the vertex count
is zero, without requiring a positive linear constant.

The axiom reports cover every declaration in `UniformEquivalence.lean` and
every check here. These are logical equivalences, not a proof or disproof of
the target. In the even-graph statement, the pieces are still cycles or edges,
not necessarily pure cycles.
-/

open SimpleGraph

namespace Erdos184.UniformEquivalence.Audit

universe u

/-- The explicitly copied proposition is definitionally the original target type. -/
theorem exactTarget_type :
    ExactTarget.{u} = (type_of% @Erdos184.erdos_184.{u}) := rfl

open scoped Classical in
/-- The converse takes a hypothesis of exactly the original proposition. -/
theorem exactTarget_implies_uniformBound (h : type_of% @Erdos184.erdos_184.{u}) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧
        IsDecomposition G D ∧
        (D.card : ℝ) ≤ K * (Fintype.card V : ℝ) := by
  exact uniform_linear_bound_of_asymptotic h

open scoped Classical in
/-- The all-graph equivalence, with both propositions written out exactly. -/
theorem exactTarget_iff_uniformBound :
    (type_of% @Erdos184.erdos_184.{u}) ↔
      ∃ K : ℝ, 0 ≤ K ∧
        ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
        ∃ D : Finset G.Subgraph,
          (∀ H ∈ D, IsCycleOrEdge H.coe) ∧
          IsDecomposition G D ∧
          (D.card : ℝ) ≤ K * (Fintype.card V : ℝ) := by
  exact asymptotic_iff_uniform_linear_bound

open scoped Classical in
/-- The even-graph equivalence also has exactly the original target on the left. -/
theorem exactTarget_iff_uniformEvenBound :
    (type_of% @Erdos184.erdos_184.{u}) ↔
      ∃ K : ℝ, 0 ≤ K ∧
        ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
        (∀ v, Even (G.degree v)) →
        ∃ D : Finset G.Subgraph,
          (∀ H ∈ D, IsCycleOrEdge H.coe) ∧
          IsDecomposition G D ∧
          (D.card : ℝ) ≤ K * (Fintype.card V : ℝ) := by
  exact asymptotic_iff_uniform_even_linear_bound

/-- At zero vertices the canonical decomposition meets `K * n` for any real `K`. -/
theorem canonical_bound_at_zero {V : Type u} [Fintype V] (G : SimpleGraph V)
    (hV : Fintype.card V = 0) (K : ℝ) :
    ((Infrastructure.singletonEdgeDecomposition G).card : ℝ) ≤
      K * (Fintype.card V : ℝ) := by
  have hcount := Infrastructure.singletonEdgeDecomposition_card_le (G := G)
  have hzero : (Infrastructure.singletonEdgeDecomposition G).card = 0 := by
    simpa [hV] using hcount
  simp [hzero, hV]

end Erdos184.UniformEquivalence.Audit

#print axioms Erdos184.UniformEquivalence.ExactTarget
#print axioms Erdos184.UniformEquivalence.UniformLinearBound
#print axioms Erdos184.UniformEquivalence.UniformEvenLinearBound
#print axioms Erdos184.UniformEquivalence.uniform_linear_bound_of_asymptotic
#print axioms Erdos184.UniformEquivalence.asymptotic_iff_uniform_linear_bound
#print axioms Erdos184.UniformEquivalence.uniform_even_linear_bound_of_asymptotic
#print axioms Erdos184.UniformEquivalence.asymptotic_iff_uniform_even_linear_bound
#print axioms Erdos184.UniformEquivalence.uniform_linear_bound_iff_uniform_even_linear_bound
#print axioms Erdos184.UniformEquivalence.Audit.exactTarget_type
#print axioms Erdos184.UniformEquivalence.Audit.exactTarget_implies_uniformBound
#print axioms Erdos184.UniformEquivalence.Audit.exactTarget_iff_uniformBound
#print axioms Erdos184.UniformEquivalence.Audit.exactTarget_iff_uniformEvenBound
#print axioms Erdos184.UniformEquivalence.Audit.canonical_bound_at_zero

#check @Erdos184.UniformEquivalence.uniform_linear_bound_of_asymptotic
#check @Erdos184.UniformEquivalence.asymptotic_iff_uniform_linear_bound
#check @Erdos184.UniformEquivalence.asymptotic_iff_uniform_even_linear_bound
#check @Erdos184.UniformEquivalence.uniform_linear_bound_iff_uniform_even_linear_bound
#check @Erdos184.UniformEquivalence.Audit.exactTarget_type
#check @Erdos184.UniformEquivalence.Audit.exactTarget_implies_uniformBound
#check @Erdos184.UniformEquivalence.Audit.exactTarget_iff_uniformBound
#check @Erdos184.UniformEquivalence.Audit.exactTarget_iff_uniformEvenBound
#check @Erdos184.UniformEquivalence.Audit.canonical_bound_at_zero
