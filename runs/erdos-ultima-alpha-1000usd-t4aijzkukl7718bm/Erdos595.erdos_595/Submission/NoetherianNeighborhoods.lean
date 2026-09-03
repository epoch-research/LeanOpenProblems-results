import Submission.MiddleCornerObstruction

/-!
Finite determination of common neighborhoods in the shift-square graph.
This is an auxiliary structural result, not a settlement of Erdős 595.
-/

set_option autoImplicit false
open Set Filter Topology SimpleGraph

namespace Erdos595Noetherian

/-- Finite products of cofinite spaces are Noetherian. -/
theorem noetherian_pi_cofinite {ι : Type*} [Finite ι] (A : ι → Type*) :
    TopologicalSpace.NoetherianSpace ((i : ι) → CofiniteTopology (A i)) := by
  rw [TopologicalSpace.noetherianSpace_iff_isCompact]
  intro s
  rw [isCompact_iff_ultrafilter_le_nhds']
  intro U hU
  have he : ∀ᶠ x in (U : Filter ((i : ι) → CofiniteTopology (A i))), ∀ i,
      (Ultrafilter.map (fun f => f i) U : Filter _) ≤ 𝓝 (x i) := by
    rw [Filter.eventually_all]
    intro i
    rcases (Ultrafilter.map (fun f => f i) U).le_cofinite_or_eq_pure with h | ⟨a, h⟩
    · exact Filter.Eventually.of_forall fun x => by
        rw [CofiniteTopology.nhds_eq]
        exact h.trans le_sup_right
    · have ha : ∀ᶠ x in (U : Filter ((i : ι) → CofiniteTopology (A i))), x i = a := by
        have hh : ({a} : Set (CofiniteTopology (A i))) ∈
            Ultrafilter.map (fun f => f i) U := by simp [h]
        exact hh
      filter_upwards [ha] with x hx
      rw [h, hx]
      exact pure_le_nhds a
  obtain ⟨x, hxs, hx⟩ := Ultrafilter.nonempty_of_mem (Filter.inter_mem hU he)
  refine ⟨x, hxs, ?_⟩
  have ht : Tendsto id (U : Filter ((i : ι) → CofiniteTopology (A i))) (𝓝 x) :=
    tendsto_pi_nhds.mpr fun i => hx i
  simpa using ht

/-- In a Noetherian space every intersection of closed sets has a finite
subfamily with the same intersection. -/
theorem finite_closed_intersection {X ι : Type*} [TopologicalSpace X]
    [TopologicalSpace.NoetherianSpace X] (S : ι → Set X)
    (hS : ∀ i, IsClosed (S i)) :
    ∃ t : Finset ι, (⋂ i ∈ t, S i) = ⋂ i, S i := by
  classical
  obtain ⟨t, ht⟩ := (TopologicalSpace.NoetherianSpace.isCompact (⋂ i, S i)ᶜ).elim_finite_subcover (fun i => (S i)ᶜ) (fun i => (hS i).isOpen_compl)
      (by simp)
  refine ⟨t, ?_⟩
  ext x
  simp only [mem_iInter]
  constructor
  · intro hx i
    by_contra hn
    have hxc : x ∈ (⋂ i, S i)ᶜ := by
      simp only [mem_compl_iff, mem_iInter]
      exact fun h => hn (h i)
    obtain ⟨j, hj, hjx⟩ := mem_iUnion₂.mp (ht hxc)
    exact hjx (hx j hj)
  · exact fun hx i _ => hx i

/-- Common neighborhoods are determined by finitely many of their defining
vertices. The finite set is indexed by the original set to retain inclusion. -/
def FiniteCommonNeighbors {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ S : Set V, ∃ t : Finset S, ∀ w : V,
    (∀ v ∈ t, G.Adj v w) ↔ ∀ v ∈ S, G.Adj v w

theorem finiteCommonNeighbors_of_noetherian {V : Type*} [TopologicalSpace V]
    [TopologicalSpace.NoetherianSpace V] (G : SimpleGraph V)
    (hG : ∀ v, IsClosed (G.neighborSet v)) : FiniteCommonNeighbors G := by
  intro S
  obtain ⟨t, ht⟩ := finite_closed_intersection (fun v : S => G.neighborSet v)
    (fun v => hG v)
  refine ⟨t, fun w => ?_⟩
  have h := Set.ext_iff.mp ht w
  simpa only [mem_iInter, SimpleGraph.mem_neighborSet, Subtype.forall] using h

/-- Finite neighborhood determination realizes every ultrafilter trace by a
common neighbor in the original graph. -/
theorem trace_has_common_neighbor {V : Type*} (G : SimpleGraph V)
    (hG : FiniteCommonNeighbors G) (p : Ultrafilter V) :
    ∃ w : V, ∀ v : V, G.neighborSet v ∈ p → G.Adj v w := by
  let S : Set V := {v | G.neighborSet v ∈ p}
  obtain ⟨t, ht⟩ := hG S
  have he : ∀ᶠ w in (p : Filter V), ∀ v ∈ t, G.Adj v w := by
    rw [Filter.eventually_all_finset]
    exact fun v _ => v.2
  obtain ⟨w, hw⟩ := Ultrafilter.nonempty_of_mem he
  exact ⟨w, (ht w).mp hw⟩

/-- Under finite neighborhood determination, the mutual-ultrafilter extension
folds homomorphically back to its base. -/
noncomputable def ultrafilterFold {V : Type*} (G : SimpleGraph V)
    (hG : G.CliqueFree 4) (hfin : FiniteCommonNeighbors G) :
    Erdos595Work.ultrafilterGraph G hG →g G where
  toFun p := (trace_has_common_neighbor G hfin p).choose
  map_rel' := by
    intro p q hpq
    let w := fun p => (trace_has_common_neighbor G hfin p).choose
    have hw : ∀ p v, G.neighborSet v ∈ p → G.Adj v (w p) :=
      fun p => (trace_has_common_neighbor G hfin p).choose_spec
    have hwp : G.neighborSet (w p) ∈ q := by
      apply Filter.mem_of_superset hpq.2
      intro v hv
      exact (hw p v hv).symm
    exact hw q (w p) hwp

/-- In particular, this extension cannot destroy a countable triangle-free
cover of a graph with finitely determined common neighborhoods. -/
theorem ultrafilter_cover {V : Type*} (G : SimpleGraph V) (hG : G.CliqueFree 4)
    (hfin : FiniteCommonNeighbors G)
    (hcov : Erdos595Work.IsCountableUnionOfTriangleFree G) :
    Erdos595Work.IsCountableUnionOfTriangleFree (Erdos595Work.ultrafilterGraph G hG) :=
  Erdos595Work.countable_union_of_hom (ultrafilterFold G hG hfin) hcov

open Erdos595MiddleCorner

private def tripleCoordinates {A : Type*} [LinearOrder A] (x : Triple A) :
    Fin 3 → CofiniteTopology A := ![x.a, x.b, x.c]

private def tripleTopology (A : Type*) [LinearOrder A] : TopologicalSpace (Triple A) :=
  TopologicalSpace.induced tripleCoordinates inferInstance

/-- All common neighborhoods of the shift-square graph have finite defining
subfamilies, independently of the cardinality of the underlying order. -/
theorem shift_finiteCommonNeighbors (A : Type*) [LinearOrder A] :
    FiniteCommonNeighbors (graph A) := by
  letI : TopologicalSpace (Triple A) := tripleTopology A
  letI : TopologicalSpace.NoetherianSpace (Fin 3 → CofiniteTopology A) :=
    noetherian_pi_cofinite (fun _ : Fin 3 => A)
  letI : TopologicalSpace.NoetherianSpace (Triple A) :=
    (show IsInducing (tripleCoordinates (A := A)) from ⟨rfl⟩).noetherianSpace
  have hc : Continuous (tripleCoordinates (A := A)) := continuous_induced_dom
  have he (i : Fin 3) (a : A) :
      IsClosed {x : Triple A | tripleCoordinates x i = (a : CofiniteTopology A)} := by
    exact (CofiniteTopology.isClosed_iff.mpr (Or.inr (Set.finite_singleton a))).preimage
      ((continuous_apply i).comp hc)
  apply finiteCommonNeighbors_of_noetherian
  intro x
  convert ((he 0 x.b).inter (he 1 x.c)).union
    ((he 0 x.c).union (((he 1 x.a).inter (he 2 x.b)).union (he 2 x.a))) using 1
  ext y
  simp [SimpleGraph.mem_neighborSet, graph, Forward, Erdos595MiddleCorner.One, Two,
    tripleCoordinates, or_assoc, eq_comm]

#print axioms trace_has_common_neighbor
#print axioms ultrafilterFold
#print axioms ultrafilter_cover
#print axioms noetherian_pi_cofinite
#print axioms finite_closed_intersection
#print axioms shift_finiteCommonNeighbors
end Erdos595Noetherian
