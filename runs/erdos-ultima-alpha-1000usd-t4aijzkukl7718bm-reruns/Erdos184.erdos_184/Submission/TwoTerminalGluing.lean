import Submission.ShiftedPackingConnectivity
import Submission.EraseCyclePiece

/-!
Exact gluing at a two-vertex separation. Only one path from each side is
joined; arbitrary collections of intersecting paths are not rerouted.
-/
open SimpleGraph
open scoped Classical
namespace Erdos184.TwoTerminalGluing

variable {V : Type*} [Fintype V]

lemma cycle_verts_subset_support {G : SimpleGraph V} (H : G.Subgraph)
    (hr : H.coe.IsRegularOfDegree 2) : H.verts ⊆ G.support := by
  intro v hv
  have hp : 0 < H.coe.degree ⟨v,hv⟩ := by
    have h := hr ⟨v,hv⟩
    simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at h ⊢
    omega
  obtain ⟨w,hw⟩ := (H.coe.degree_pos_iff_exists_adj ⟨v,hv⟩).mp hp
  exact ⟨w.val,H.adj_sub hw⟩

/-- Deleting a specified edge of a cycle leaves its entire complementary path. -/
lemma cycle_complementary_path {G : SimpleGraph V} (H : G.Subgraph)
    (hc : H.coe.Connected) (hr : H.coe.IsRegularOfDegree 2)
    {a b : V} (hab : H.Adj a b) :
    ∃ p : G.Walk b a, p.IsPath ∧
      (∀ e, e ∈ p.edges ↔ e ∈ H.edgeSet ∧ e ≠ s(a,b)) ∧
      (∀ x ∈ p.support, x ∈ H.verts) := by
  obtain ⟨q,hq,hqH⟩ := CycleRing.cycle_piece_walk_at H hc hr a (H.edge_vert hab)
  have hmem : b ∈ q.toSubgraph.neighborSet a := by rw [hqH]; exact hab
  rw [hq.neighborSet_toSubgraph_endpoint] at hmem
  have hor : ∃ q : G.Walk a a, q.IsCycle ∧ q.snd = b ∧ q.toSubgraph = H := by
    rcases hmem with h | h
    · exact ⟨q,hq,h.symm,hqH⟩
    · have h' : b = q.penultimate := Set.mem_singleton_iff.mp h
      exact ⟨q.reverse,hq.reverse,by simpa using h'.symm,by simpa using hqH⟩
  obtain ⟨q,hq,hqb,hqH⟩ := hor
  cases q with
  | nil => exact (hq.not_nil (by simp)).elim
  | @cons a c a hac p =>
    have hcb : c = b := by simpa only [Walk.snd_cons] using hqb
    subst c
    obtain ⟨hp,he⟩ := (Walk.cons_isCycle_iff _ _).mp hq
    refine ⟨p,hp,?_,?_⟩
    · intro e
      have hh : e ∈ H.edgeSet ↔ e = s(a,b) ∨ e ∈ p.edges := by
        rw [← hqH,Walk.mem_edges_toSubgraph,Walk.edges_cons,List.mem_cons]
      rw [hh]
      constructor
      · intro h
        exact ⟨Or.inr h,fun heq => he (heq ▸ h)⟩
      · rintro ⟨h,hn⟩
        exact h.resolve_left hn
    · intro x hx
      rw [← hqH,Walk.mem_verts_toSubgraph,Walk.support_cons]
      exact List.mem_cons_of_mem _ hx

omit [Fintype V] in
/-- Two edge-disjoint paths with only their endpoints in common form one cycle. -/
lemma append_isCycle_of_paths {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) (q : G.Walk b a) (hp : p.IsPath) (hq : q.IsPath)
    (hab : a ≠ b) (hedge : p.edges.Disjoint q.edges)
    (hinter : ∀ x, x ∈ p.support → x ∈ q.support → x = a ∨ x = b) :
    (p.append q).IsCycle := by
  have hpa : a ∉ p.support.tail := by
    have h := hp.support_nodup
    rw [Walk.support_eq_cons,List.nodup_cons] at h
    exact h.1
  have hqb : b ∉ q.support.tail := by
    have h := hq.support_nodup
    rw [Walk.support_eq_cons,List.nodup_cons] at h
    exact h.1
  refine ⟨⟨?_,?_⟩,?_⟩
  · rw [Walk.isTrail_def,Walk.edges_append,List.nodup_append']
    exact ⟨hp.isTrail.edges_nodup,hq.isTrail.edges_nodup,hedge⟩
  · intro hn
    have hlen := congrArg Walk.length hn
    have hp0 := Walk.not_nil_of_ne hab (p := p)
    have hpos := Walk.not_nil_iff_lt_length.mp hp0
    simp only [Walk.length_append,Walk.length_nil] at hlen
    omega
  · rw [Walk.tail_support_append,List.nodup_append']
    refine ⟨hp.support_nodup.tail,hq.support_nodup.tail,?_⟩
    intro x hx hy
    rcases hinter x (List.mem_of_mem_tail hx) (List.mem_of_mem_tail hy) with h | h
    · exact hpa (h ▸ hx)
    · exact hqb (h ▸ hy)

/-- Cancel the common edge of two cycles whose remaining interiors are disjoint. -/
lemma glue_cycle_pieces {G A B : SimpleGraph V}
    (H : A.Subgraph) (K : B.Subgraph)
    (hH : H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hK : K.coe.Connected ∧ K.coe.IsRegularOfDegree 2) {a b : V}
    (habH : H.Adj a b) (habK : K.Adj a b)
    (hinter : H.verts ∩ K.verts ⊆ {a,b})
    (hedge : H.edgeSet ∩ K.edgeSet ⊆ {s(a,b)})
    (hG : (H.edgeSet ∪ K.edgeSet) \ {s(a,b)} ⊆ G.edgeSet) :
    ∃ J : G.Subgraph, (J.coe.Connected ∧ J.coe.IsRegularOfDegree 2) ∧
      J.edgeSet = (H.edgeSet ∪ K.edgeSet) \ {s(a,b)} := by
  obtain ⟨p,hp,hpe,hpv⟩ := cycle_complementary_path H hH.1 hH.2 habH
  obtain ⟨q,hq,hqe,hqv⟩ := cycle_complementary_path K hK.1 hK.2 habK
  have hpG : ∀ e ∈ p.edges, e ∈ G.edgeSet := by
    intro e he
    have hh := (hpe e).mp he
    exact hG ⟨Or.inl hh.1,hh.2⟩
  have hqG : ∀ e ∈ q.edges, e ∈ G.edgeSet := by
    intro e he
    have hh := (hqe e).mp he
    exact hG ⟨Or.inr hh.1,hh.2⟩
  let p' := p.transfer G hpG
  let q' := (q.transfer G hqG).reverse
  have hpp : p'.IsPath := hp.transfer hpG
  have hqq : q'.IsPath := (hq.transfer hqG).reverse
  have hd : p'.edges.Disjoint q'.edges := by
    simp only [p',q',Walk.edges_reverse,Walk.edges_transfer,List.disjoint_reverse_right]
    intro e he hf
    have ha := (hpe e).mp he
    have hb := (hqe e).mp hf
    exact ha.2 (hedge ⟨ha.1,hb.1⟩)
  have hi : ∀ x, x ∈ p'.support → x ∈ q'.support → x = b ∨ x = a := by
    intro x hx hy
    have hx' : x ∈ H.verts := hpv x (by simpa [p'] using hx)
    have hy' : x ∈ K.verts := hqv x (by simpa [q'] using hy)
    have hh := hinter ⟨hx',hy'⟩
    simpa only [Set.mem_insert_iff,Set.mem_singleton_iff,or_comm] using hh
  have hc := append_isCycle_of_paths p' q' hpp hqq (A.ne_of_adj habH.adj_sub).symm hd hi
  refine ⟨(p'.append q').toSubgraph,cycle_subgraph_regular G hc,?_⟩
  ext e
  simp only [Walk.mem_edges_toSubgraph,Walk.edges_append,List.mem_append,p',q',
    Walk.edges_transfer,Walk.edges_reverse,List.mem_reverse,hpe,hqe,
    Set.mem_diff,Set.mem_union,Set.mem_singleton_iff]
  tauto

set_option maxHeartbeats 800000 in
/-- Two decompositions with one common artificial terminal edge glue with a
one-piece saving, provided the side interiors are disjoint. -/
lemma glue_decompositions {G A B : SimpleGraph V} {a b : V}
    (ha : A.Adj a b) (hb : B.Adj a b)
    (hinter : A.support ∩ B.support ⊆ {a,b})
    (hedge : A.edgeSet ∩ B.edgeSet ⊆ {s(a,b)})
    (hcover : G.edgeSet = (A.edgeSet ∪ B.edgeSet) \ {s(a,b)})
    (DA : Finset A.Subgraph) (DB : Finset B.Subgraph)
    (hca : ∀ H ∈ DA, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hcb : ∀ H ∈ DB, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hda : IsDecomposition A DA) (hdb : IsDecomposition B DB) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G D ∧ D.card + 1 ≤ DA.card + DB.card := by
  have hea : s(a,b) ∈ A.edgeSet := ha
  have heb : s(a,b) ∈ B.edgeSet := hb
  rw [← hda.2] at hea
  rw [← hdb.2] at heb
  obtain ⟨H,hHD,heH⟩ := Set.mem_iUnion₂.mp hea
  obtain ⟨K,hKD,heK⟩ := Set.mem_iUnion₂.mp heb
  have hv : H.verts ∩ K.verts ⊆ {a,b} := by
    intro x hx
    exact hinter ⟨cycle_verts_subset_support H (hca H hHD).2 hx.1,
      cycle_verts_subset_support K (hcb K hKD).2 hx.2⟩
  have he : H.edgeSet ∩ K.edgeSet ⊆ {s(a,b)} := by
    intro e hh
    exact hedge ⟨H.edgeSet_subset hh.1,K.edgeSet_subset hh.2⟩
  obtain ⟨J,hJ,hJe⟩ := glue_cycle_pieces H K (hca H hHD) (hcb K hKD) heH heK hv he (by
    intro e he
    rw [hcover]
    exact ⟨he.1.elim (fun h => Or.inl (H.edgeSet_subset h))
      (fun h => Or.inr (K.edgeSet_subset h)),he.2⟩)
  obtain ⟨EA,hcEA,hdEA,hbEA⟩ := erase_cycle_piece DA hca hda H hHD
  obtain ⟨EB,hcEB,hdEB,hbEB⟩ := erase_cycle_piece DB hcb hdb K hKD
  let RA := A \ H.spanningCoe
  let RB := B \ K.spanningCoe
  let R := G \ unionPieces G {J}
  have hRA : RA ≤ R := by
    dsimp only [R]
    rw [show unionPieces G {J} = J.spanningCoe by simp [unionPieces]]
    intro x y hxy
    have hn : s(x,y) ≠ s(a,b) := fun heq => hxy.2 (show s(x,y) ∈ H.edgeSet from heq.symm ▸ heH)
    have hxyG : G.Adj x y := by
      change s(x,y) ∈ G.edgeSet
      rw [hcover]
      exact ⟨Or.inl hxy.1,hn⟩
    refine ⟨hxyG,?_⟩
    intro hxyJ
    have hh : s(x,y) ∈ (H.edgeSet ∪ K.edgeSet) \ {s(a,b)} := hJe ▸ hxyJ
    rcases hh.1 with hh | hh
    · exact hxy.2 hh
    · exact hn (hedge ⟨hxy.1,K.edgeSet_subset hh⟩)
  have hRB : RB ≤ R := by
    dsimp only [R]
    rw [show unionPieces G {J} = J.spanningCoe by simp [unionPieces]]
    intro x y hxy
    have hn : s(x,y) ≠ s(a,b) := fun heq => hxy.2 (show s(x,y) ∈ K.edgeSet from heq.symm ▸ heK)
    have hxyG : G.Adj x y := by
      change s(x,y) ∈ G.edgeSet
      rw [hcover]
      exact ⟨Or.inr hxy.1,hn⟩
    refine ⟨hxyG,?_⟩
    intro hxyJ
    have hh : s(x,y) ∈ (H.edgeSet ∪ K.edgeSet) \ {s(a,b)} := hJe ▸ hxyJ
    rcases hh.1 with hh | hh
    · exact hn (hedge ⟨H.edgeSet_subset hh,hxy.1⟩)
    · exact hxy.2 hh
  have hdis : Disjoint RA.edgeSet RB.edgeSet := by
    apply Set.disjoint_left.mpr
    intro e heA heB
    simp only [RA,edgeSet_sdiff] at heA
    simp only [RB,edgeSet_sdiff] at heB
    have hh : e = s(a,b) := hedge ⟨heA.1,heB.1⟩
    exact heA.2 (hh.symm ▸ heH)
  have hcov : RA.edgeSet ∪ RB.edgeSet = R.edgeSet := by
    apply Set.Subset.antisymm
    · exact Set.union_subset (edgeSet_mono hRA) (edgeSet_mono hRB)
    · intro e heR
      simp only [R,unionPieces,Finset.sup_singleton,edgeSet_sdiff] at heR
      have heG := heR.1
      rw [hcover] at heG
      have hn : e ∉ H.edgeSet ∪ K.edgeSet := by
        intro he
        apply heR.2
        change e ∈ J.edgeSet
        rw [hJe]
        exact ⟨he,heG.2⟩
      rcases heG.1 with heA | heB
      · left
        simp only [RA,edgeSet_sdiff]
        exact ⟨heA,fun he => hn (Or.inl he)⟩
      · right
        simp only [RB,edgeSet_sdiff]
        exact ⟨heB,fun he => hn (Or.inr he)⟩
  obtain ⟨E,hcE,hdE,hbE⟩ := combine_pure_decompositions hRA hRB hdis hcov EA EB
    (by
      intro L hL
      refine ⟨(hcEA L hL).1,?_⟩
      intro x
      simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using (hcEA L hL).2 x)
    (by
      intro L hL
      refine ⟨(hcEB L hL).1,?_⟩
      intro x
      simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using (hcEB L hL).2 x)
    hdEA hdEB
  have hcycles : ∀ L ∈ ({J} : Finset G.Subgraph),
      L.coe.Connected ∧ L.coe.IsRegularOfDegree 2 := by
    intro L hL
    obtain rfl := Finset.mem_singleton.mp hL
    exact hJ
  have hdP : Set.PairwiseDisjoint (({J} : Finset G.Subgraph) : Set G.Subgraph)
      (fun L => L.edgeSet) := by simp
  obtain ⟨D,hcD,hdD,hbD⟩ := complete_cycle_packing G {J} hcycles hdP E (by
    intro L hL
    refine ⟨(hcE L hL).1,?_⟩
    intro x
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using (hcE L hL).2 x) hdE
  refine ⟨D,hcD,hdD,?_⟩
  simp only [Finset.card_singleton] at hbD
  omega

end Erdos184.TwoTerminalGluing
