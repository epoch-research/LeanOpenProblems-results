import Submission.CriticalPetals

/-! Cutting one edge from each of a family of cycles preserves the reachability
relation of every subfamily. In particular a rainbow spanning-tree selection
has a connected complement, and the same rank hypotheses allow a second,
edge-disjoint rainbow spanning-tree selection. This is not an absorption rule. -/
open SimpleGraph
open scoped Classical
namespace Erdos184.RainbowComplements
open RankCritical RankCycleFamilies RainbowForests CriticalRainbowTrees
variable {V : Type*} [Fintype V]
set_option maxHeartbeats 800000

omit [Fintype V] in
lemma reachable_of_adj_reachable {G A : SimpleGraph V}
    (h : ∀ u v, G.Adj u v → A.Reachable u v) {u v : V} (huv : G.Reachable u v) :
    A.Reachable u v := by
  obtain ⟨p⟩ := huv
  induction p with
  | nil => exact .refl _
  | @cons u v w huv p ih => exact (h u v huv).trans ih

lemma rank_eq_of_adj_reachable {G A : SimpleGraph V} (hAG : A ≤ G)
    (h : ∀ u v, G.Adj u v → A.Reachable u v) : graphRank A = graphRank G := by
  let f := ConnectedComponent.map (Hom.ofLE hAG)
  have hi : Function.Injective f := by
    intro c d hcd
    induction c using ConnectedComponent.ind with
    | _ u =>
      induction d using ConnectedComponent.ind with
      | _ v =>
        apply ConnectedComponent.sound
        apply reachable_of_adj_reachable h
        exact ConnectedComponent.exact hcd
  have hs : Function.Surjective f := ConnectedComponent.surjective_map_ofLE hAG
  have hh := Nat.card_congr (Equiv.ofBijective f ⟨hi,hs⟩)
  simp only [graphRank,hh]

lemma cycle_spanning_isCycles {G : SimpleGraph V} (H : G.Subgraph)
    (hc : H.coe.Connected) (hr : H.coe.IsRegularOfDegree 2) :
    H.spanningCoe.IsCycles := by
  obtain ⟨v,hv⟩ := hc.nonempty
  obtain ⟨p,hp,hpH⟩ := CycleRing.cycle_piece_walk_at H hc hr v hv
  rw [← hpH]
  exact hp.isCycles_spanningCoe_toSubgraph

lemma cycle_cut_edge_reachable {G : SimpleGraph V} (H : G.Subgraph)
    (hc : H.coe.Connected) (hr : H.coe.IsRegularOfDegree 2) (e : Sym2 V)
    {u v : V} (huv : H.Adj u v) : (H.spanningCoe.deleteEdges {e}).Reachable u v := by
  by_cases he : s(u,v) = e
  · rw [← he]
    exact (cycle_spanning_isCycles H hc hr).reachable_deleteEdges huv
  · exact (deleteEdges_adj.mpr ⟨huv,by simpa only [Set.mem_singleton_iff] using he⟩).reachable

/-- Every subfamily retains its spanning-forest rank after independently
cutting any one edge from each of its cycles. The edge need not be present. -/
lemma cut_family_rank {J : Type*} {G : SimpleGraph V} (H : J → G.Subgraph)
    (hc : ∀ j, (H j).coe.Connected ∧ (H j).coe.IsRegularOfDegree 2)
    (e : J → Sym2 V) (S : Finset J) :
    graphRank (S.sup (fun j => (H j).spanningCoe.deleteEdges {e j})) =
      graphRank (S.sup (fun j => (H j).spanningCoe)) := by
  apply rank_eq_of_adj_reachable
  · apply Finset.sup_le
    intro j hj
    exact (deleteEdges_le _).trans (Finset.le_sup (f := fun j => (H j).spanningCoe) hj)
  · intro u v huv
    simp only [Finset.sup_eq_iSup, iSup_adj] at huv
    obtain ⟨j,hj,huv⟩ := huv
    exact (cycle_cut_edge_reachable (H j) (hc j).1 (hc j).2 (e j) huv).mono
      (Finset.le_sup (f := fun j => (H j).spanningCoe.deleteEdges {e j}) hj)

/-- Any marked set meeting each cycle in at most one edge can be deleted
without changing reachability. This statement does not require the marked
set itself to be a forest. -/
lemma delete_sparse_mark_reachable (G : SimpleGraph V) (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hcover : (⋃ H ∈ D, H.edgeSet) = G.edgeSet) (R : SimpleGraph V)
    (hR : ∀ H ∈ D, (H.edgeSet ∩ R.edgeSet).Subsingleton) (u v : V) :
    (G \ R).Reachable u v ↔ G.Reachable u v := by
  refine ⟨fun h => h.mono sdiff_le, reachable_of_adj_reachable ?_⟩
  intro a b hab
  by_cases hr : R.Adj a b
  · have he : s(a,b) ∈ G.edgeSet := hab
    rw [← hcover] at he
    obtain ⟨H,hH,heH⟩ := Set.mem_iUnion₂.mp he
    have hle : H.spanningCoe.deleteEdges {s(a,b)} ≤ G \ R := by
      intro x y hxy
      obtain ⟨hxy,hn⟩ := deleteEdges_adj.mp hxy
      refine ⟨H.adj_sub hxy,?_⟩
      intro hRxy
      exact hn (Set.mem_singleton_iff.mpr ((hR H hH) ⟨hxy,hRxy⟩ ⟨heH,hr⟩))
    exact (cycle_cut_edge_reachable H (hc H hH).1 (hc H hH).2 (s(a,b)) heH).mono hle
  · exact (show (G \ R).Adj a b from ⟨hab,hr⟩).reachable

lemma delete_sparse_mark_connected (G : SimpleGraph V) (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D) (R : SimpleGraph V)
    (hR : ∀ H ∈ D, (H.edgeSet ∩ R.edgeSet).Subsingleton) (hG : G.Connected) :
    (G \ R).Connected := by
  haveI := hG.nonempty
  exact ⟨fun u v => (delete_sparse_mark_reachable G D hc hd.2 R hR u v).mpr (hG.preconnected u v)⟩

/-- Even after a prescribed edge is forbidden separately in every cycle,
the reserved critical family still has a rainbow C-fold spanning-tree
selection. The forbidden edges are not allowed to vary during the proof. -/
theorem exists_rainbow_trees_avoiding_representatives {G : SimpleGraph V} {C : ℕ}
    (hG : IsCritical C G) (hconn : G.Connected) (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D) (hsize : D.card = C * graphRank G + 1)
    (H₀ : G.Subgraph) (hH₀ : H₀ ∈ D) (e : D.erase H₀ → Sym2 V) :
    ∃ (c : D.erase H₀ → Fin C) (u v : D.erase H₀ → V),
      (∀ H : D.erase H₀, H.val.Adj (u H) (v H) ∧ s(u H,v H) ≠ e H) ∧
      Function.Injective (fun H => s(u H,v H)) ∧
      (∀ i, (selected c u v i).IsTree ∧ selected c u v i ≤ G \ H₀.spanningCoe) ∧
      Pairwise (fun i j => Disjoint (selected c u v i).edgeSet (selected c u v j).edgeSet) := by
  let S := D.erase H₀
  let F : S → SimpleGraph V := fun H => H.val.spanningCoe.deleteEdges {e H}
  have hb := reserved_subfamily_rank_bound hG D hc hd hsize H₀ hH₀
  have hhall : ∀ t : Finset S, t.card ≤ Fintype.card (Fin C) *
      (Fintype.card V - Fintype.card (t.sup F).ConnectedComponent) := by
    intro t
    have ht : t.image Subtype.val ⊆ S := by
      intro H hH
      obtain ⟨J,_,rfl⟩ := Finset.mem_image.mp hH
      exact J.property
    have hh := hb (t.image Subtype.val) ht
    rw [Finset.card_image_of_injective _ Subtype.val_injective] at hh
    have hr := cut_family_rank (fun H : S => H.val)
      (fun H => hc H.val (Finset.mem_erase.mp H.property).2) e t
    rw [subfamily_sup_eq] at hr
    rw [← hr] at hh
    simpa only [F, graphRank, Nat.card_eq_fintype_card, Fintype.card_fin] using hh
  obtain ⟨c,u,v,ha,hf⟩ := exists_rainbow_forests (I := Fin C) F hhall
  have ha' : ∀ H : S, H.val.Adj (u H) (v H) ∧ s(u H,v H) ≠ e H := by
    intro H
    have hh := deleteEdges_adj.mp (ha H)
    exact ⟨hh.1,by simpa only [Set.mem_singleton_iff] using hh.2⟩
  have hi := distinct_representatives D S (Finset.erase_subset H₀ D) hd u v (fun H => (ha' H).1)
  have hne : ∀ H, u H ≠ v H := fun H => (ha' H).1.ne
  haveI : Nonempty V := hconn.nonempty
  have hr : graphRank G = Fintype.card V - 1 := by have := RankCriticalPartitions.connected_rank hconn; omega
  have hs : Fintype.card S = Fintype.card (Fin C) * (Fintype.card V - 1) := by
    rw [Fintype.card_coe, Fintype.card_fin]
    have he := Finset.card_erase_add_one hH₀
    rw [hsize,hr] at he
    change S.card = _
    dsimp only [S]
    omega
  have ht := selected_isTree_of_card c u v hne hi hf hs
  refine ⟨c,u,v,ha',hi,?_,selected_disjoint c u v hi⟩
  intro i
  refine ⟨ht i,selected_le c u v _ ?_ i⟩
  intro H
  refine ⟨H.val.adj_sub (ha' H).1,?_⟩
  intro hbad
  exact Set.disjoint_left.mp
    (hd.1 (Finset.mem_erase.mp H.property).2 hH₀ (Finset.mem_erase.mp H.property).1)
    (show s(u H,v H) ∈ H.val.edgeSet from (ha' H).1) hbad

/-- Two edge selections from the same edge-disjoint cycle family are
edge-disjoint whenever they choose different edges in every piece. -/
lemma selections_disjoint {I J : Type*} [Fintype I] [Fintype J]
    {G : SimpleGraph V} (D S : Finset G.Subgraph) (hSD : S ⊆ D)
    (hd : IsDecomposition G D) (c : S → I) (d : S → J)
    (u v x y : S → V) (ha : ∀ H : S, H.val.Adj (u H) (v H))
    (hb : ∀ H : S, H.val.Adj (x H) (y H))
    (hne : ∀ H : S, s(x H,y H) ≠ s(u H,v H)) (i : I) (j : J) :
    Disjoint (selected c u v i).edgeSet (selected d x y j).edgeSet := by
  apply Set.disjoint_left.mpr
  intro e he he'
  induction e using Sym2.ind with
  | h a b =>
    obtain ⟨⟨H,_,hH⟩,_⟩ := (selected_adj c u v i a b).mp he
    obtain ⟨⟨K,_,hK⟩,_⟩ := (selected_adj d x y j a b).mp he'
    have heH : s(a,b) ∈ H.val.edgeSet := hH.symm ▸ (show s(u H,v H) ∈ H.val.edgeSet from ha H)
    have heK : s(a,b) ∈ K.val.edgeSet := hK.symm ▸ (show s(x K,y K) ∈ K.val.edgeSet from hb K)
    have heq : H = K := by
      apply Subtype.ext
      by_contra hn
      exact Set.disjoint_left.mp (hd.1 (hSD H.property) (hSD K.property) hn) heH heK
    subst K
    exact hne H (hK.symm.trans hH)

/-- A connected C-rank-critical optimum, with any one cycle reserved,
supplies two edge-disjoint C-fold rainbow spanning-tree selections.
The second selection may assign the pieces to different tree colors. -/
theorem exists_two_reserved_rainbow_selections {G : SimpleGraph V} {C : ℕ}
    (hG : IsCritical C G) (hconn : G.Connected) (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D) (hsize : D.card = C * graphRank G + 1)
    (H₀ : G.Subgraph) (hH₀ : H₀ ∈ D) :
    ∃ (c d : D.erase H₀ → Fin C) (u v x y : D.erase H₀ → V),
      (∀ H : D.erase H₀, H.val.Adj (u H) (v H) ∧ H.val.Adj (x H) (y H) ∧
        s(x H,y H) ≠ s(u H,v H)) ∧
      (∀ i, (selected c u v i).IsTree ∧ selected c u v i ≤ G \ H₀.spanningCoe ∧
        (selected d x y i).IsTree ∧ selected d x y i ≤ G \ H₀.spanningCoe) ∧
      Pairwise (fun i j => Disjoint (selected c u v i).edgeSet (selected c u v j).edgeSet) ∧
      Pairwise (fun i j => Disjoint (selected d x y i).edgeSet (selected d x y j).edgeSet) ∧
      ∀ i j, Disjoint (selected c u v i).edgeSet (selected d x y j).edgeSet := by
  obtain ⟨c,u,v,ha,_,ht,hdis⟩ :=
    exists_reserved_rainbow_trees hG hconn D hc hd hsize H₀ hH₀
  obtain ⟨d,x,y,hb,_,ht',hdis'⟩ :=
    exists_rainbow_trees_avoiding_representatives hG hconn D hc hd hsize H₀ hH₀
      (fun H => s(u H,v H))
  refine ⟨c,d,u,v,x,y,fun H => ⟨ha H,(hb H).1,(hb H).2⟩,
    fun i => ⟨(ht i).1,(ht i).2,(ht' i).1,(ht' i).2⟩,hdis,hdis',?_⟩
  exact selections_disjoint D (D.erase H₀) (Finset.erase_subset H₀ D) hd c d u v x y ha
    (fun H => (hb H).1) (fun H => (hb H).2)

end Erdos184.RainbowComplements
