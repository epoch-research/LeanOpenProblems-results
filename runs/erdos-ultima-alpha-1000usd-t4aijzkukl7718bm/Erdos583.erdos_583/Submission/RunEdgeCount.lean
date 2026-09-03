import Submission.RunCompressionData

/-! Exact edge counts for private run compression. -/
namespace Erdos583RunEdgeCountDevelopment
open SimpleGraph Erdos583Work Erdos583Work.BridgeGlue
open Erdos583CycleRunIntervalsDevelopment Erdos583PathIntervalsDevelopment
open Erdos583RunCompressionDataDevelopment Erdos583PrivatePathExpansionDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false
variable {V I : Type*} [Fintype V]

lemma sup_finset_edge_ncard (A : Finset I) (f : I → SimpleGraph V)
    (hd : ∀ i ∈ A, ∀ j ∈ A, i ≠ j → Disjoint (f i).edgeSet (f j).edgeSet) :
    (A.sup f).edgeSet.ncard=∑ i ∈ A, (f i).edgeSet.ncard := by
  induction A using Finset.induction_on with
  | empty => simp
  | @insert i A hi ih =>
    have hh : Disjoint (f i).edgeSet (A.sup f).edgeSet := by
      apply Set.disjoint_left.mpr
      intro e he hf
      induction e using Sym2.ind with
      | h x y =>
        obtain ⟨j,hj,hxy⟩ := (adj_sup_finset A f x y).mp hf
        exact Set.disjoint_left.mp (hd i (by simp) j (by simp [hj]) (fun he ↦ hi (he ▸ hj))) he hxy
    rw [Finset.sup_insert,edgeSet_sup,Set.ncard_union_eq hh,Finset.sum_insert hi]
    rw [ih (fun j hj l hl ↦ hd j (by simp [hj]) l (by simp [hl]))]

variable {G : SimpleGraph V} {a b : V}

omit [Fintype V] in
lemma RunConditions.edge_touches (W : G.Walk a b) (S : Set V) (h : RunConditions W S)
    (p : RunIndex W) (hp : p ∈ runs W S) {x y : V} (hxy : (runPath W p).toSubgraph.Adj x y) :
    x ∈ S ∨ y ∈ S := by
  have hr := (mem_runs W S p).mp hp
  by_contra hn
  have hx : x ∉ S := fun hx ↦ hn (Or.inl hx)
  have hy : y ∉ S := fun hy ↦ hn (Or.inr hy)
  have hend (z : V) (hz : z ∈ (runPath W p).support) (hzS : z ∉ S) :
      z=runStart W p ∨ z=runFinish W p := by
    by_contra hzN
    exact hzS (hr.internal_mem W S hz (fun he ↦ hzN (Or.inl he)) (fun he ↦ hzN (Or.inr he)))
  rcases hend x (Walk.mem_support_of_adj_toSubgraph hxy) hx with rfl|rfl <;>
    rcases hend y (Walk.mem_support_of_adj_toSubgraph hxy.symm) hy with rfl|rfl
  · exact hxy.ne rfl
  · exact h.no_arc W S p hp p ((runPath W p).mem_edges_toSubgraph.mp hxy)
  · exact h.no_arc W S p hp p ((runPath W p).mem_edges_toSubgraph.mp hxy.symm)
  · exact hxy.ne rfl

omit [Fintype V] in
lemma RunConditions.arc_edge_disjoint (W : G.Walk a b) (S : Set V) (h : RunConditions W S)
    (p : RunIndex W) (hp : p ∈ runs W S) (q : RunIndex W) (hq : q ∈ runs W S) (hpq : p ≠ q) :
    Disjoint (runPath W p).toSubgraph.edgeSet (runPath W q).toSubgraph.edgeSet := by
  apply Set.disjoint_left.mpr
  intro e he hf
  induction e using Sym2.ind with
  | h x y =>
    have hr := (mem_runs W S p).mp hp
    have ex {z v : V} (hz : z ∈ S) (he : (runPath W p).toSubgraph.Adj z v)
        (hf : (runPath W q).toSubgraph.Adj z v) : False := by
      exact h.privacy p hp q hq hpq z (Walk.mem_support_of_adj_toSubgraph he)
        (fun hh ↦ hr.2.2.1 (show runStart W p ∈ S from hh ▸ hz))
        (fun hh ↦ hr.2.2.2.1 (show runFinish W p ∈ S from hh ▸ hz))
        (Walk.mem_support_of_adj_toSubgraph hf)
    rcases RunConditions.edge_touches W S h p hp he with hx|hy
    · exact ex hx he hf
    · exact ex hy (show (runPath W p).toSubgraph.Adj x y from he).symm
        (show (runPath W q).toSubgraph.Adj x y from hf).symm

lemma RunConditions.arcs_ncard (W : G.Walk a b) (S : Set V) (h : RunConditions W S) :
    (arcs (runs W S) (runPath W)).edgeSet.ncard=∑ p ∈ runs W S, (runPath W p).length := by
  rw [arcs,sup_finset_edge_ncard _ _ (RunConditions.arc_edge_disjoint W S h)]
  apply Finset.sum_congr rfl
  intro p hp
  exact path_edgeSet_ncard (h.path p hp)

lemma RunConditions.chords_ncard (W : G.Walk a b) (S : Set V) (h : RunConditions W S) :
    (chords (runs W S) (runStart W) (runFinish W)).edgeSet.ncard=(runs W S).card := by
  have hd : ∀ p ∈ runs W S, ∀ q ∈ runs W S, p ≠ q →
      Disjoint (edge (runStart W p) (runFinish W p)).edgeSet
        (edge (runStart W q) (runFinish W q)).edgeSet := by
    intro p hp q hq hpq
    rw [edge_edgeSet_of_ne (h.ne p hp),edge_edgeSet_of_ne (h.ne q hq)]
    exact Set.disjoint_singleton.mpr (fun he ↦ hpq (h.injective p hp q hq he))
  rw [chords,sup_finset_edge_ncard _ _ hd]
  calc
    _ = ∑ p ∈ runs W S, 1 := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [edge_edgeSet_of_ne (h.ne p hp),Set.ncard_singleton]
    _ = _ := by simp

lemma RunConditions.arcs_at_least_twice (W : G.Walk a b) (S : Set V) (h : RunConditions W S) :
    2*(runs W S).card ≤ (arcs (runs W S) (runPath W)).edgeSet.ncard := by
  rw [RunConditions.arcs_ncard W S h]
  have hh := Finset.sum_le_sum (s := runs W S) (f := fun _ ↦ 2)
    (g := fun p ↦ (runPath W p).length) (by
      intro p hp
      simp only [runPath]
      rw [interval_length W _ ((mem_runs W S p).mp hp).2.1]
      have := p.property
      omega)
  simpa only [Finset.sum_const_nat,mul_comm] using hh

omit [Fintype V] in
lemma RunConditions.base_arcs_disjoint (W : G.Walk a b) (S : Set V) (h : RunConditions W S)
    (H : SimpleGraph V) (hH : H.support ⊆ Sᶜ) :
    Disjoint H.edgeSet (arcs (runs W S) (runPath W)).edgeSet := by
  apply Set.disjoint_left.mpr
  intro e he hf
  induction e using Sym2.ind with
  | h x y =>
    obtain ⟨p,hp,hxy⟩ := (arcs_adj _ _ _ _).mp hf
    rcases RunConditions.edge_touches W S h p hp hxy with hx|hy
    · exact hH ⟨y,he⟩ hx
    · exact hH ⟨x,(show H.Adj x y from he).symm⟩ hy

lemma RunConditions.compression_edge_saving (W : G.Walk a b) (S : Set V) (h : RunConditions W S)
    (H : SimpleGraph V) (hH : H.support ⊆ Sᶜ) :
    (H ⊔ chords (runs W S) (runStart W) (runFinish W)).edgeSet.ncard+(runs W S).card ≤
      (H ⊔ arcs (runs W S) (runPath W)).edgeSet.ncard := by
  rw [edgeSet_sup,edgeSet_sup,Set.ncard_union_eq (RunConditions.base_arcs_disjoint W S h H hH)]
  have hh := Set.ncard_union_le H.edgeSet (chords (runs W S) (runStart W) (runFinish W)).edgeSet
  rw [RunConditions.chords_ncard W S h] at hh
  have hl := RunConditions.arcs_at_least_twice W S h
  omega

end Erdos583RunEdgeCountDevelopment
