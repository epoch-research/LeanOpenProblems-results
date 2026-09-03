import Submission.MinimalSingletons
import Submission.MaximizerReachability

/-! Removing a forest from an even graph cannot decrease its minimum
cycle-and-edge decomposition number. This gives vertex deletion for even
graphs, but does not supply a linear bound for arbitrary graphs. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.AcyclicDeletion
open Critical
set_option maxHeartbeats 1000000
variable {V : Type*} [Fintype V]

lemma number_le_delete_forest (G M : SimpleGraph V)
    (heven : ∀ v, Even (Nat.card (G.neighborSet v))) (hM : M.IsAcyclic) :
    number G ≤ number (G \ M) := by
  obtain ⟨D,hD,hdec,hcard⟩ := exists_minimum (G \ M)
  obtain ⟨E,F,hER,hE,hunion,hnum,hFcard⟩ :=
    MinimalSingletons.minimum_split D hD hdec hcard
  have hEG : E ≤ G := hER.trans sdiff_le
  have hNe : ∀ v, Even ((G \ E).degree v) := by
    intro v
    have hd := degree_sdiff_add G E hEG v
    have hg := Nat.even_iff.mp (heven v)
    have he := Nat.even_iff.mp (hE v)
    simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hd ⊢
    rw [Nat.even_iff]
    omega
  have hNF : (G \ E) \ M ≤ F := by
    intro x y hxy
    have hR : (G \ M).Adj x y := ⟨hxy.1.1,hxy.2⟩
    have hEF : (E ⊔ F).Adj x y := hunion.symm ▸ hR
    exact hEF.elim (fun h => (hxy.1.2 h).elim) id
  obtain ⟨A,hA,hdecA,hcA⟩ := SingleAddition.even_feedback_decomposition
    (G \ E) M (by
      simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hNe) hM
  have hN := number_le A (fun H hH => Or.inl (by
    simpa only [SimpleGraph.IsRegularOfDegree,← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using hA H hH)) hdecA
  have hF := Finset.card_le_card (SimpleGraph.edgeFinset_mono hNF)
  have hG := number_sdiff_add_le G E hEG
  simp only [SimpleGraph.edgeFinset_card,← Nat.card_eq_fintype_card] at hcA hF hFcard
  omega

/-- The same deletion bounds every even subgraph of the host, not merely
an even host itself. -/
lemma even_subgraph_le_deleted_hull {G R M : SimpleGraph V} (hRG : R ≤ G)
    (heven : ∀ v, Even (Nat.card (R.neighborSet v))) (hM : M.IsAcyclic) :
    number R ≤ EdgeHull.value (G \ M) := by
  apply (number_le_delete_forest R M heven hM).trans
  exact EdgeHull.le_value (sdiff_le_sdiff_right hRG)

lemma incidence_forest (G : SimpleGraph V) (v : V) :
    (SimpleGraph.fromEdgeSet (G.incidenceSet v)).IsAcyclic := by
  let r : V → ℕ := fun x => if x = v then 0 else 1
  let p : V → Option V := fun _ => some v
  have h : CycleForestCertificate.ForestValid (G.incidenceFinset v) r p := by
    intro x y hxy
    have he : s(x,y) ∈ G.incidenceSet v := by
      exact (G.mem_incidenceFinset v s(x,y)).mp hxy.1
    have hv : v = x ∨ v = y := by
      simpa only [Sym2.mem_iff] using he.2
    rcases hv with rfl | rfl
    · exact Or.inl ⟨by simp [r,Ne.symm hxy.2],rfl⟩
    · exact Or.inr ⟨by simp [r,hxy.2],rfl⟩
  simpa only [CycleForestCertificate.graph,SimpleGraph.coe_incidenceFinset] using
    CycleForestCertificate.forest_acyclic h

lemma number_le_delete_vertex (G : SimpleGraph V)
    (heven : ∀ v, Even (Nat.card (G.neighborSet v))) (v : V) :
    number G ≤ number (G.deleteIncidenceSet v) :=
  number_le_delete_forest G (SimpleGraph.fromEdgeSet (G.incidenceSet v))
    heven (incidence_forest G v)

private noncomputable def stableNumber {W : Type*} [Finite W] (H : SimpleGraph W) : ℕ :=
  @number W (Fintype.ofFinite W) H

private lemma number_stable {W : Type*} [Fintype W] (H : SimpleGraph W) :
    number H = stableNumber H :=
  congrArg (fun i : Fintype W => @number W i H) (Subsingleton.elim _ _)

lemma number_le_induce_compl_vertex (G : SimpleGraph V)
    (heven : ∀ v, Even (Nat.card (G.neighborSet v))) (v : V) :
    number G ≤ number (G.induce {v}ᶜ) := by
  have h := VertexSeparators.number_induce_support (G.deleteIncidenceSet v)
    ({v}ᶜ : Set V) (by
      intro x hx
      exact (G.support_deleteIncidenceSet_subset v hx).2)
  have h₀ := number_le_delete_vertex G heven v
  simp only [number_stable] at h h₀ ⊢
  rw [G.induce_deleteIncidenceSet_of_notMem (by simp)] at h
  exact h₀.trans h

end Erdos184Work.AcyclicDeletion
#print axioms Erdos184Work.AcyclicDeletion.number_le_induce_compl_vertex
#print axioms Erdos184Work.AcyclicDeletion.number_le_delete_forest
#print axioms Erdos184Work.AcyclicDeletion.even_subgraph_le_deleted_hull
