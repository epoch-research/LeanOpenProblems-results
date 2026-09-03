import Submission.TwoTerminalGluing

/-!
Cancelling one common edge when the side supports share at most three
vertices.  Only one complementary path on each side is used.  This does
not assert bounded-cost rerouting for arbitrary path families.
-/
open SimpleGraph
open scoped Classical
namespace Erdos184.ThreeTerminalGluing
open TwoTerminalGluing

variable {V : Type*} {G : SimpleGraph V}

/-- Split two paths at their only possible common interior vertex. -/
lemma split_paths_at_common_vertex {a b c : V}
    (p : G.Walk a b) (q : G.Walk b a) (hp : p.IsPath) (hq : q.IsPath)
    (hac : a ≠ c) (hbc : b ≠ c)
    (hpc : c ∈ p.support) (hqc : c ∈ q.support)
    (hedge : p.edges.Disjoint q.edges)
    (hinter : ∀ x, x ∈ p.support → x ∈ q.support → x = a ∨ x = b ∨ x = c) :
    ∃ P : G.Walk a a, ∃ Q : G.Walk b b,
      P.IsCycle ∧ Q.IsCycle ∧ P.edges.Disjoint Q.edges ∧
      ∀ e, e ∈ P.edges ∨ e ∈ Q.edges ↔ e ∈ p.edges ∨ e ∈ q.edges := by
  let p₁ := p.takeUntil c hpc
  let p₂ := p.dropUntil c hpc
  let q₁ := q.takeUntil c hqc
  let q₂ := q.dropUntil c hqc
  have hp₁ : p₁.IsPath := hp.takeUntil hpc
  have hp₂ : p₂.IsPath := hp.dropUntil hpc
  have hq₁ : q₁.IsPath := hq.takeUntil hqc
  have hq₂ : q₂.IsPath := hq.dropUntil hqc
  have ep₁ : p₁.edges ⊆ p.edges := p.edges_takeUntil_subset hpc
  have ep₂ : p₂.edges ⊆ p.edges := p.edges_dropUntil_subset hpc
  have eq₁ : q₁.edges ⊆ q.edges := q.edges_takeUntil_subset hqc
  have eq₂ : q₂.edges ⊆ q.edges := q.edges_dropUntil_subset hqc
  have hpq : p₁.edges.Disjoint q₂.edges := fun _ he hf => hedge (ep₁ he) (eq₂ hf)
  have hqp : q₁.edges.Disjoint p₂.edges := fun _ he hf => hedge (ep₂ hf) (eq₁ he)
  have hiP : ∀ x, x ∈ p₁.support → x ∈ q₂.support → x = a ∨ x = c := by
    intro x hx hy
    rcases hinter x (p.support_takeUntil_subset hpc hx)
      (q.support_dropUntil_subset hqc hy) with h | h | h
    · exact Or.inl h
    · subst x
      exact (Walk.endpoint_notMem_support_takeUntil hp hpc hbc hx).elim
    · exact Or.inr h
  have hiQ : ∀ x, x ∈ q₁.support → x ∈ p₂.support → x = b ∨ x = c := by
    intro x hx hy
    rcases hinter x (p.support_dropUntil_subset hpc hy)
      (q.support_takeUntil_subset hqc hx) with h | h | h
    · subst x
      exact (Walk.endpoint_notMem_support_takeUntil hq hqc hac hx).elim
    · exact Or.inl h
    · exact Or.inr h
  have hP := append_isCycle_of_paths p₁ q₂ hp₁ hq₂ hac hpq hiP
  have hQ := append_isCycle_of_paths q₁ p₂ hq₁ hp₂ hbc hqp hiQ
  refine ⟨p₁.append q₂,q₁.append p₂,hP,hQ,?_,?_⟩
  · intro e he hf
    simp only [Walk.edges_append,List.mem_append] at he hf
    rcases he with he | he <;> rcases hf with hf | hf
    · exact hedge (ep₁ he) (eq₁ hf)
    · exact hp.isTrail.disjoint_edges_takeUntil_dropUntil hpc he hf
    · exact hq.isTrail.disjoint_edges_takeUntil_dropUntil hqc hf he
    · exact hedge (ep₂ hf) (eq₂ he)
  · intro e
    have hep : e ∈ p₁.edges ∨ e ∈ p₂.edges ↔ e ∈ p.edges := by
      simp only [p₁,p₂,← List.mem_append,← Walk.edges_append,Walk.take_spec]
    have heq : e ∈ q₁.edges ∨ e ∈ q₂.edges ↔ e ∈ q.edges := by
      simp only [q₁,q₂,← List.mem_append,← Walk.edges_append,Walk.take_spec]
    simp only [Walk.edges_append,List.mem_append]
    tauto

variable [Fintype V]

/-- The union of two edge-disjoint paths with at most one common interior
vertex has a pure-cycle packing of at most two pieces, with exactly its edges. -/
lemma paths_to_packing {a b c : V}
    (p : G.Walk a b) (q : G.Walk b a) (hp : p.IsPath) (hq : q.IsPath)
    (hab : a ≠ b) (hedge : p.edges.Disjoint q.edges)
    (hinter : ∀ x, x ∈ p.support → x ∈ q.support → x = a ∨ x = b ∨ x = c) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      Set.PairwiseDisjoint (D : Set G.Subgraph) (fun H => H.edgeSet) ∧
      (∀ e, e ∈ ⋃ H ∈ D, H.edgeSet ↔ e ∈ p.edges ∨ e ∈ q.edges) ∧
      D.card ≤ 2 := by
  by_cases hi : ∀ x, x ∈ p.support → x ∈ q.support → x = a ∨ x = b
  · have hc := append_isCycle_of_paths p q hp hq hab hedge hi
    refine ⟨{(p.append q).toSubgraph},?_,by simp,?_,by simp⟩
    · intro H hH
      obtain rfl := Finset.mem_singleton.mp hH
      exact cycle_subgraph_regular G hc
    · intro e
      simp only [Finset.mem_singleton,Set.iUnion_iUnion_eq_left,
        Walk.mem_edges_toSubgraph,Walk.edges_append,List.mem_append]
  · push_neg at hi
    obtain ⟨x,hxp,hxq,hxa,hxb⟩ := hi
    have hxc : x = c := (hinter x hxp hxq).resolve_left hxa |>.resolve_left hxb
    subst x
    obtain ⟨P,Q,hP,hQ,hPQ,hcov⟩ := split_paths_at_common_vertex p q hp hq
      hxa.symm hxb.symm hxp hxq hedge hinter
    let D : Finset G.Subgraph := {P.toSubgraph,Q.toSubgraph}
    have hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2 := by
      intro H hH
      have hh : H = P.toSubgraph ∨ H = Q.toSubgraph := by simpa [D] using hH
      rcases hh with rfl | rfl
      · exact cycle_subgraph_regular G hP
      · exact cycle_subgraph_regular G hQ
    have hd : Disjoint P.toSubgraph.edgeSet Q.toSubgraph.edgeSet := by
      apply Set.disjoint_left.mpr
      intro e he hf
      exact hPQ (P.mem_edges_toSubgraph.mp he) (Q.mem_edges_toSubgraph.mp hf)
    refine ⟨D,hc,?_,?_,by simpa only [D,Finset.card_singleton] using
      (Finset.card_insert_le P.toSubgraph {Q.toSubgraph})⟩
    · intro H hH K hK hHK
      have hh : H = P.toSubgraph ∨ H = Q.toSubgraph := by simpa [D] using hH
      have hk : K = P.toSubgraph ∨ K = Q.toSubgraph := by simpa [D] using hK
      rcases hh with rfl | rfl <;> rcases hk with rfl | rfl
      · exact (hHK rfl).elim
      · exact hd
      · exact hd.symm
      · exact (hHK rfl).elim
    · intro e
      simpa only [D,Finset.set_biUnion_insert,Finset.set_biUnion_singleton,
        Set.mem_union,Walk.mem_edges_toSubgraph] using hcov e

/-- Cancel a common edge of two cycle pieces whose supports meet in at most
three vertices.  The replacement uses at most two cycles, not necessarily one. -/
lemma glue_cycle_pieces {A B : SimpleGraph V}
    (H : A.Subgraph) (K : B.Subgraph)
    (hH : H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hK : K.coe.Connected ∧ K.coe.IsRegularOfDegree 2) {a b c : V}
    (habH : H.Adj a b) (habK : K.Adj a b)
    (hinter : H.verts ∩ K.verts ⊆ {a,b,c})
    (hedge : H.edgeSet ∩ K.edgeSet ⊆ {s(a,b)})
    (hG : (H.edgeSet ∪ K.edgeSet) \ {s(a,b)} ⊆ G.edgeSet) :
    ∃ D : Finset G.Subgraph,
      (∀ J ∈ D, J.coe.Connected ∧ J.coe.IsRegularOfDegree 2) ∧
      Set.PairwiseDisjoint (D : Set G.Subgraph) (fun J => J.edgeSet) ∧
      (⋃ J ∈ D, J.edgeSet) = (H.edgeSet ∪ K.edgeSet) \ {s(a,b)} ∧ D.card ≤ 2 := by
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
  have hi : ∀ x, x ∈ p'.support → x ∈ q'.support → x = b ∨ x = a ∨ x = c := by
    intro x hx hy
    have hx' : x ∈ H.verts := hpv x (by simpa [p'] using hx)
    have hy' : x ∈ K.verts := hqv x (by simpa [q'] using hy)
    have hh := hinter ⟨hx',hy'⟩
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hh
    tauto
  obtain ⟨D,hcD,hdD,hcov,hcard⟩ := paths_to_packing p' q' hpp hqq
    (A.ne_of_adj habH.adj_sub).symm hd hi
  refine ⟨D,hcD,hdD,?_,hcard⟩
  ext e
  rw [hcov]
  simp only [p',q',Walk.edges_transfer,Walk.edges_reverse,List.mem_reverse,hpe,hqe,
    Set.mem_diff,Set.mem_union,Set.mem_singleton_iff]
  tauto

set_option maxHeartbeats 800000 in
/-- Two decompositions with one common artificial terminal edge glue without
increasing their total size, when the side supports meet in at most three vertices. -/
lemma glue_decompositions {G A B : SimpleGraph V} {a b c : V}
    (ha : A.Adj a b) (hb : B.Adj a b)
    (hinter : A.support ∩ B.support ⊆ {a,b,c})
    (hedge : A.edgeSet ∩ B.edgeSet ⊆ {s(a,b)})
    (hcover : G.edgeSet = (A.edgeSet ∪ B.edgeSet) \ {s(a,b)})
    (DA : Finset A.Subgraph) (DB : Finset B.Subgraph)
    (hca : ∀ H ∈ DA, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hcb : ∀ H ∈ DB, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hda : IsDecomposition A DA) (hdb : IsDecomposition B DB) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G D ∧ D.card ≤ DA.card + DB.card := by
  have hea : s(a,b) ∈ A.edgeSet := ha
  have heb : s(a,b) ∈ B.edgeSet := hb
  rw [← hda.2] at hea
  rw [← hdb.2] at heb
  obtain ⟨H,hHD,heH⟩ := Set.mem_iUnion₂.mp hea
  obtain ⟨K,hKD,heK⟩ := Set.mem_iUnion₂.mp heb
  have hv : H.verts ∩ K.verts ⊆ {a,b,c} := by
    intro x hx
    exact hinter ⟨cycle_verts_subset_support H (hca H hHD).2 hx.1,
      cycle_verts_subset_support K (hcb K hKD).2 hx.2⟩
  have he : H.edgeSet ∩ K.edgeSet ⊆ {s(a,b)} := by
    intro e hh
    exact hedge ⟨H.edgeSet_subset hh.1,K.edgeSet_subset hh.2⟩
  obtain ⟨P,hcycles,hdP,hPe,hbP⟩ := glue_cycle_pieces H K (hca H hHD) (hcb K hKD) heH heK hv he (by
    intro e he
    rw [hcover]
    exact ⟨he.1.elim (fun h => Or.inl (H.edgeSet_subset h))
      (fun h => Or.inr (K.edgeSet_subset h)),he.2⟩)
  obtain ⟨EA,hcEA,hdEA,hbEA⟩ := erase_cycle_piece DA hca hda H hHD
  obtain ⟨EB,hcEB,hdEB,hbEB⟩ := erase_cycle_piece DB hcb hdb K hKD
  let RA := A \ H.spanningCoe
  let RB := B \ K.spanningCoe
  have hJe : (unionPieces G P).edgeSet = (H.edgeSet ∪ K.edgeSet) \ {s(a,b)} :=
    (unionPieces_edgeSet G P).trans hPe
  let R := G \ unionPieces G P
  have hRA : RA ≤ R := by
    dsimp only [R]
    intro x y hxy
    have hn : s(x,y) ≠ s(a,b) := fun heq => hxy.2 (show s(x,y) ∈ H.edgeSet from heq.symm ▸ heH)
    have hxyG : G.Adj x y := by
      change s(x,y) ∈ G.edgeSet
      rw [hcover]
      exact ⟨Or.inl hxy.1,hn⟩
    refine ⟨hxyG,?_⟩
    intro hxyJ
    have hh : s(x,y) ∈ (H.edgeSet ∪ K.edgeSet) \ {s(a,b)} := hJe ▸ (show s(x,y) ∈ (unionPieces G P).edgeSet from hxyJ)
    rcases hh.1 with hh | hh
    · exact hxy.2 hh
    · exact hn (hedge ⟨hxy.1,K.edgeSet_subset hh⟩)
  have hRB : RB ≤ R := by
    dsimp only [R]
    intro x y hxy
    have hn : s(x,y) ≠ s(a,b) := fun heq => hxy.2 (show s(x,y) ∈ K.edgeSet from heq.symm ▸ heK)
    have hxyG : G.Adj x y := by
      change s(x,y) ∈ G.edgeSet
      rw [hcover]
      exact ⟨Or.inr hxy.1,hn⟩
    refine ⟨hxyG,?_⟩
    intro hxyJ
    have hh : s(x,y) ∈ (H.edgeSet ∪ K.edgeSet) \ {s(a,b)} := hJe ▸ (show s(x,y) ∈ (unionPieces G P).edgeSet from hxyJ)
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
      simp only [R,edgeSet_sdiff] at heR
      have heG := heR.1
      rw [hcover] at heG
      have hn : e ∉ H.edgeSet ∪ K.edgeSet := by
        intro he
        apply heR.2
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
  obtain ⟨D,hcD,hdD,hbD⟩ := complete_cycle_packing G P hcycles hdP E (by
    intro L hL
    refine ⟨(hcE L hL).1,?_⟩
    intro x
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using (hcE L hL).2 x) hdE
  refine ⟨D,hcD,hdD,?_⟩
  omega

end Erdos184.ThreeTerminalGluing
