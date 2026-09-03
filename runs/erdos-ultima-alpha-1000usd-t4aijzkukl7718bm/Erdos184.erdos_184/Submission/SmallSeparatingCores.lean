import Submission.SeparatingCycleReduction
import Submission.SmallCoreRigidity

/-! Small even-minimal cores satisfy the separating-cycle criterion.
The assertion for arbitrary cores remains unproved. -/
open Filter SimpleGraph
open scoped Classical
namespace Erdos184Work.SeparatingCycleReduction
open Critical EvenCore Rigidity
set_option maxHeartbeats 1000000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

lemma separating_of_small_core (he : ∀ v, Even (G.degree v))
    (hm : EvenMinimal G) (hne : G ≠ ⊥) (hk : number G ≤ 3) :
    HasSeparatingCycle G := by
  obtain ⟨v,hv⟩ := SmallCoreRigidity.degree_two_of_number_le_three he hm hk hne
  exact separating_of_even_degree_two he hv

lemma no_separating_core_number_ge_four (he : ∀ v, Even (G.degree v))
    (hm : EvenMinimal G) (hne : G ≠ ⊥) (hs : ¬ HasSeparatingCycle G) :
    4 ≤ number G := by
  by_contra h
  exact hs (separating_of_small_core he hm hne (by omega))

lemma no_separating_cycle_preserves_reachability (hs : ¬ HasSeparatingCycle G)
    {u : V} {p : G.Walk u u} (hp : p.IsCycle) (a b : V) :
    (G \ p.toSubgraph.spanningCoe).Reachable a b ↔ G.Reachable a b := by
  constructor
  · exact SimpleGraph.Reachable.mono sdiff_le
  · intro hab
    by_contra hn
    exact hs ⟨u,p,hp,component_count_lt_of_lost_reachability sdiff_le hab hn⟩

lemma no_separating_even_degree_ge_four (he : ∀ v, Even (G.degree v))
    (hs : ¬ HasSeparatingCycle G) (v : V) (hv : v ∈ G.support) :
    4 ≤ G.degree v := by
  have hp : 0 < G.degree v := (SimpleGraph.degree_pos_iff_mem_support _ _).mpr hv
  have ht : G.degree v ≠ 2 := fun ht => hs (separating_of_even_degree_two he ht)
  have he' := Nat.even_iff.mp (he v)
  omega

universe u
/-- A failure of the original asymptotic statement would force a nonempty
nonseparating even-minimal core. This does not assert that such a core exists. -/
lemma obstruction_of_asymptotic_failure
    (hbad : ¬ (∃ f : ℕ → ℝ,
      (f =O[atTop] fun n : ℕ => (n : ℝ)) ∧
      ∀ {W : Type u} [Fintype W] [DecidableEq W] (R : SimpleGraph W),
      ∃ D : Finset R.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition R D ∧
        (D.card : ℝ) ≤ f (Fintype.card W))) :
    ∃ (W : Type u) (_ : Fintype W) (R : SimpleGraph W),
      (∀ v, Even (R.degree v)) ∧ EvenMinimal R ∧ R ≠ ⊥ ∧
      4 ≤ number R ∧ ¬ HasSeparatingCycle R ∧
      (∀ v ∈ R.support, 4 ≤ R.degree v) ∧
      (∀ u (p : R.Walk u u), p.IsCycle → ∀ a b,
        (R \ p.toSubgraph.spanningCoe).Reachable a b ↔ R.Reachable a b) := by
  classical
  have hn : ¬ (∀ {W : Type u} [Fintype W] (R : SimpleGraph W),
      (∀ v, Even (R.degree v)) → EvenMinimal R → R ≠ ⊥ → HasSeparatingCycle R) := by
    intro hs
    exact hbad (asymptotic_of_separating_cores hs)
  push_neg at hn
  obtain ⟨W,iW,R,he,hm,hne,hs⟩ := hn
  letI := iW
  refine ⟨W,iW,R,he,hm,hne,no_separating_core_number_ge_four he hm hne hs,hs,?_,?_⟩
  · exact no_separating_even_degree_ge_four he hs
  · intro u p hp a b
    exact no_separating_cycle_preserves_reachability hs hp a b

end Erdos184Work.SeparatingCycleReduction
#print axioms Erdos184Work.SeparatingCycleReduction.separating_of_small_core
#print axioms Erdos184Work.SeparatingCycleReduction.obstruction_of_asymptotic_failure
