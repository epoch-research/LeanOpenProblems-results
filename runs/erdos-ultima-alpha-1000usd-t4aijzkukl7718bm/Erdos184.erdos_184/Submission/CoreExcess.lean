import Submission.RigidityDegree

/-! A quantitative alternative to full core rigidity.
The edge-excess hypothesis in the conditional reductions remains unproved. -/

open Filter SimpleGraph
open scoped Classical
namespace Erdos184Work.CoreExcess
open Critical EvenCore Rigidity
set_option maxHeartbeats 1500000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

lemma three_mul_number_le_edges (heven : ∀ v, Even (G.degree v)) :
    3 * number G ≤ G.edgeFinset.card := by
  obtain ⟨D,hD,hdec,hc⟩ := exists_cycle_decomposition G heven
  have hn := number_le D (fun H hH => Or.inl (by
    simpa only [SimpleGraph.IsRegularOfDegree,
      ← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using hD H hH)) hdec
  omega

/-- This is a sufficient structural hypothesis, not an established property
of arbitrary minimal cores. -/
lemma even_bound_of_core_edge_excess (C : ℕ)
    (hcore : ∀ R : SimpleGraph V, (∀ v, Even (R.degree v)) → EvenMinimal R →
      R.edgeFinset.card ≤ C * Fintype.card V + 2 * number R)
    (heven : ∀ v, Even (G.degree v)) :
    number G ≤ C * Fintype.card V := by
  obtain ⟨R,_,hR,hn,hmin,_⟩ := exists_even_minimal_core G heven
  have hR' : ∀ v, Even (R.degree v) := by
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using hR
  have hlo := three_mul_number_le_edges hR'
  have hhi := hcore R hR' hmin
  omega

/-- A hypothetical counterexample has an even-minimal core with large
edge excess. No existence of such a counterexample is asserted. -/
lemma excess_core_of_large_number (C : ℕ)
    (heven : ∀ v, Even (G.degree v))
    (hlarge : C * Fintype.card V < number G) :
    ∃ R : SimpleGraph V, R ≤ G ∧ (∀ v, Even (R.degree v)) ∧
      EvenMinimal R ∧ number R = number G ∧
      C * Fintype.card V + 2 * number R < R.edgeFinset.card := by
  obtain ⟨R,hRG,hR,hn,hmin,_⟩ := exists_even_minimal_core G heven
  have hR' : ∀ v, Even (R.degree v) := by
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using hR
  have hlo := three_mul_number_le_edges hR'
  refine ⟨R,hRG,hR',hmin,hn,?_⟩
  omega

universe u
/-- The original asymptotic proposition follows from the explicitly stated
edge-excess bound on cores. The structural hypothesis remains open here. -/
lemma asymptotic_of_core_edge_excess (C : ℕ)
    (hcore : ∀ {W : Type u} [Fintype W] (R : SimpleGraph W),
      (∀ v, Even (R.degree v)) → EvenMinimal R →
      R.edgeFinset.card ≤ C * Fintype.card W + 2 * number R) :
    ∃ f : ℕ → ℝ,
      (f =O[atTop] fun n : ℕ => (n : ℝ)) ∧
      ∀ {W : Type u} [Fintype W] [DecidableEq W] (R : SimpleGraph W),
      ∃ D : Finset R.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition R D ∧
        (D.card : ℝ) ≤ f (Fintype.card W) := by
  apply asymptotic_iff_even_cycle_uniform.mpr
  refine ⟨C,?_⟩
  intro W _ _ R hR
  obtain ⟨D,hD,hdec,hcard⟩ := minimum_cycles hR
  refine ⟨D,hD,hdec,?_⟩
  have hn := even_bound_of_core_edge_excess C (fun S hS hm => hcore S hS hm) hR
  have hDcard : D.card ≤ C * Fintype.card W := by omega
  exact_mod_cast hDcard

#print axioms three_mul_number_le_edges
#print axioms excess_core_of_large_number
#print axioms asymptotic_of_core_edge_excess
end Erdos184Work.CoreExcess
