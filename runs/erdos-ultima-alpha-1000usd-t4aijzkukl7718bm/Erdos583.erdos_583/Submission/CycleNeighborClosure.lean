import Submission.MatchingIntegrated

/-! Short-cycle closure and fresh shortcut edges at a shortest whole-cycle defect. -/
namespace Erdos583CycleNeighborClosureDevelopment
open SimpleGraph Erdos583Work Erdos583Work.QuotaTrails Erdos583Work.CycleEar
open scoped Classical
set_option maxHeartbeats 2400000
variable {V : Type*} {G : SimpleGraph V} {a : V}

lemma cycle_neighbor_pair [Fintype V] (C : G.Walk a a) (hC : C.IsCycle) {r u v : V}
    (hru : C.toSubgraph.Adj r u) (hrv : C.toSubgraph.Adj r v) (huv : u ≠ v) :
    C.toSubgraph.neighborSet r={u,v} := by
  have hn := hC.ncard_neighborSet_toSubgraph_eq_two (Walk.mem_support_of_adj_toSubgraph hru)
  apply (Set.eq_of_subset_of_ncard_le (show ({u,v} : Set V) ⊆ C.toSubgraph.neighborSet r from
    by intro x hx; rcases hx with rfl|rfl <;> assumption) ?_).symm
  rw [hn,Set.ncard_pair huv]

lemma cycle_support_of_closed (C : G.Walk a a) (S : Set V)
    {r : V} (hr : r ∈ C.support) (hrS : r ∈ S)
    (hclosed : ∀ x ∈ S, ∀ y, C.toSubgraph.Adj x y → y ∈ S) : C.toSubgraph.verts ⊆ S := by
  have step {x y : C.toSubgraph.verts} (P : C.toSubgraph.coe.Walk x y) : x.val ∈ S → y.val ∈ S := by
    induction P with
    | nil => exact id
    | @cons x y z h P ih => exact fun hx ↦ ih (hclosed x.val hx y.val h)
  intro x hx
  obtain ⟨P⟩ := C.toSubgraph_connected ⟨r,C.mem_verts_toSubgraph.mpr hr⟩ ⟨x,hx⟩
  exact step P hrS

lemma cycle_length_le_three_of_triangle [Fintype V] (C : G.Walk a a) (hC : C.IsCycle)
    {r u v : V} (hru : C.toSubgraph.Adj r u) (huv : C.toSubgraph.Adj u v)
    (hvr : C.toSubgraph.Adj v r) : C.length ≤ 3 := by
  have hN₁ := cycle_neighbor_pair C hC hru hvr.symm huv.ne
  have hN₂ := cycle_neighbor_pair C hC hru.symm huv hvr.ne.symm
  have hN₃ := cycle_neighbor_pair C hC hvr huv.symm hru.ne
  have hsub : C.toSubgraph.verts ⊆ ({r,u,v} : Set V) := by
    apply cycle_support_of_closed C _ (Walk.mem_support_of_adj_toSubgraph hru) (Or.inl rfl)
    intro x hx y hy
    rcases hx with hx|hx|hx
    · rw [hx] at hy
      change y ∈ C.toSubgraph.neighborSet r at hy
      rw [hN₁] at hy
      exact Or.inr hy
    · rw [hx] at hy
      change y ∈ C.toSubgraph.neighborSet u at hy
      rw [hN₂] at hy
      rcases hy with hy|hy
      · exact Or.inl hy
      · exact Or.inr (Or.inr hy)
    · rw [hx] at hy
      change y ∈ C.toSubgraph.neighborSet v at hy
      rw [hN₃] at hy
      rcases hy with hy|hy
      · exact Or.inl hy
      · exact Or.inr (Or.inl hy)
  have hb := Set.ncard_le_ncard hsub
  have hv : C.toSubgraph.verts.ncard=C.length := by rw [Walk.verts_toSubgraph,cycle_support_ncard hC]
  have hs := Set.ncard_insert_le r ({u,v} : Set V)
  have ht := Set.ncard_pair huv.ne
  omega

lemma cycle_length_le_four_of_common_neighbors [Fintype V] (C : G.Walk a a) (hC : C.IsCycle)
    {r s u v : V} (hrs : r ≠ s) (huv : u ≠ v)
    (hru : C.toSubgraph.Adj r u) (hrv : C.toSubgraph.Adj r v)
    (hsu : C.toSubgraph.Adj s u) (hsv : C.toSubgraph.Adj s v) : C.length ≤ 4 := by
  have hN₁ := cycle_neighbor_pair C hC hru hrv huv
  have hN₂ := cycle_neighbor_pair C hC hsu hsv huv
  have hN₃ := cycle_neighbor_pair C hC hru.symm hsu.symm hrs
  have hN₄ := cycle_neighbor_pair C hC hrv.symm hsv.symm hrs
  have hsub : C.toSubgraph.verts ⊆ ({r,s,u,v} : Set V) := by
    apply cycle_support_of_closed C _ (Walk.mem_support_of_adj_toSubgraph hru) (Or.inl rfl)
    intro x hx y hy
    rcases hx with hx|hx|hx|hx
    · rw [hx] at hy
      change y ∈ C.toSubgraph.neighborSet r at hy
      rw [hN₁] at hy
      exact Or.inr (Or.inr hy)
    · rw [hx] at hy
      change y ∈ C.toSubgraph.neighborSet s at hy
      rw [hN₂] at hy
      exact Or.inr (Or.inr hy)
    · rw [hx] at hy
      change y ∈ C.toSubgraph.neighborSet u at hy
      rw [hN₃] at hy
      rcases hy with hy|hy
      · exact Or.inl hy
      · exact Or.inr (Or.inl hy)
    · rw [hx] at hy
      change y ∈ C.toSubgraph.neighborSet v at hy
      rw [hN₄] at hy
      rcases hy with hy|hy
      · exact Or.inl hy
      · exact Or.inr (Or.inl hy)
  have hb := Set.ncard_le_ncard hsub
  have hv : C.toSubgraph.verts.ncard=C.length := by rw [Walk.verts_toSubgraph,cycle_support_ncard hC]
  have hs₁ := Set.ncard_insert_le r ({s,u,v} : Set V)
  have hs₂ := Set.ncard_insert_le s ({u,v} : Set V)
  have hs₃ := Set.ncard_pair huv
  omega

lemma shortest_cycle_avoider_no_chord [Fintype V] {k : ℕ}
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (i j : Fin k) (hij : i ≠ j) (C : G.Walk a a) (hC : C.IsCycle)
    (hi : (T.walk i).toSubgraph=C.toSubgraph) (hmin : ShortestCycle T C.length)
    {r u v : V} (hru : C.toSubgraph.Adj r u) (hrv : C.toSubgraph.Adj r v) (huv : u ≠ v)
    (hrP : r ∉ (T.walk j).support) : s(u,v) ∉ (T.walk j).edges := by
  intro he
  have hrC := Walk.mem_support_of_adj_toSubgraph hru
  let D := C.rotate hrC
  have hD : D.IsCycle := hC.rotate hrC
  have hDi : (T.walk i).toSubgraph=D.toSubgraph := hi.trans (C.toSubgraph_rotate hrC).symm
  have hDl : D.length=C.length := by
    have hh := congrArg Walk.length (C.take_spec hrC)
    simpa only [D,Walk.rotate,Walk.length_append,Nat.add_comm] using hh
  obtain ⟨x,y,hrx,hyr,R,hform⟩ := cycle_two_spokes D hD
  have hCf : (Walk.cons hrx (R.concat hyr)).IsCycle := hform ▸ hD
  have hif : (T.walk i).toSubgraph=(Walk.cons hrx (R.concat hyr)).toSubgraph := by rw [←hform]; exact hDi
  have hxC : C.toSubgraph.Adj r x := by
    rw [←C.toSubgraph_rotate hrC]
    change D.toSubgraph.Adj r x
    rw [hform]
    change s(r,x) ∈ (Walk.cons hrx (R.concat hyr)).toSubgraph.edgeSet
    rw [Walk.mem_edges_toSubgraph]
    simp
  have hyC : C.toSubgraph.Adj r y := by
    apply Subgraph.Adj.symm
    rw [←C.toSubgraph_rotate hrC]
    change D.toSubgraph.Adj y r
    rw [hform]
    change s(y,r) ∈ (Walk.cons hrx (R.concat hyr)).toSubgraph.edgeSet
    rw [Walk.mem_edges_toSubgraph]
    simp [Walk.concat_eq_append]
  have hRp : R.IsPath := ((Walk.cons_isCycle_iff _ _).mp hCf).1.of_append_left
  have hxy : x ≠ y := by
    intro heq
    subst y
    have hnil := (Walk.isPath_iff_eq_nil R).mp hRp
    have hl := hCf.three_le_length
    simp only [hnil,Walk.length_cons,Walk.length_concat,Walk.length_nil] at hl
    omega
  have hN := cycle_neighbor_pair C hC hru hrv huv
  have hx : x ∈ ({u,v} : Set V) := hN ▸ hxC
  have hy : y ∈ ({u,v} : Set V) := hN ▸ hyC
  have hpair : s(x,y)=s(u,v) := by
    rcases hx with rfl|rfl <;> rcases hy with rfl|rfl
    · exact (hxy rfl).elim
    · rfl
    · exact Sym2.eq_swap
    · exact (hxy rfl).elim
  have hedge : s(x,y) ∈ (T.walk j).edges := hpair.symm ▸ he
  have hxyG : G.Adj x y := (T.walk j).edges_subset_edgeSet hedge
  obtain ⟨U,E,hUs,hE,hUi,hlen⟩ := shorten_cycle_member T hs i j hij hrx hyr R hCf hif hxyG hedge hrP
  have hbound := hmin U hUs i x E hE hUi
  rw [←hform,hDl] at hlen
  omega

end Erdos583CycleNeighborClosureDevelopment
