import Submission.Work

/-! Excluding degree four from a smallest odd-order failure.  Suppress one
pair of spokes and restore the other pair as a path; in a complete neighborhood,
delete an additional neighbor edge so that the suppressed edge is fresh. -/
open SimpleGraph Erdos583Work
open Erdos583Work.BridgeGlue Erdos583Work.VertexCritical
open Erdos583Work.DegreeTwoReduction Erdos583Work.DegreeThreeReduction
namespace Erdos583DegreeFourReductionDevelopment
open scoped Classical
set_option maxHeartbeats 1200000

lemma connected_of_neighbor_cover {V : Type*} {G F : SimpleGraph V}
    (hG : G.Connected) {u a b : V} (ha : F.Adj u a) (hb : F.Adj u b)
    (hwithin : within G ({u}ᶜ : Set V) ≤ F)
    (hcover : ∀ x, G.Adj u x →
      (within G ({u}ᶜ : Set V)).Reachable a x ∨
      (within G ({u}ᶜ : Set V)).Reachable b x) : F.Connected := by
  have hux (x : V) (hx : G.Adj u x) : F.Reachable u x := by
    rcases hcover x hx with h | h
    · exact ha.reachable.trans (h.mono hwithin)
    · exact hb.reachable.trans (h.mono hwithin)
  have hedge (x y : V) (hxy : G.Adj x y) : F.Reachable x y := by
    by_cases hx : x=u
    · subst x; exact hux y hxy
    by_cases hy : y=u
    · subst y; exact (hux x hxy.symm).symm
    exact (hwithin ⟨hxy,hx,hy⟩).reachable
  letI := hG.nonempty
  exact ⟨fun x y ↦ reachable_map_to_reachable id hedge (hG.preconnected x y)⟩

lemma connected_of_delete_vertex {V : Type*} {G : SimpleGraph V}
    {u a : V} (ha : G.Adj u a)
    (hconn : (G.induce ({u}ᶜ : Set V)).Connected) : G.Connected := by
  let S : Set V := {u}ᶜ
  have hlink (x : S) : G.Reachable a x.val :=
    (hconn.preconnected (⟨a,ha.ne.symm⟩ : S) x).map (Embedding.induce S).toHom
  have hreach (x : V) : G.Reachable u x := by
    by_cases hx : x=u
    · subst x; exact Reachable.rfl
    exact ha.reachable.trans (hlink ⟨x,hx⟩)
  letI : Nonempty V := ⟨u⟩
  exact ⟨fun x y ↦ (hreach x).symm.trans (hreach y)⟩

lemma suppress_after_path {n : ℕ} (hsmall : SmallerOrders n) (hn : Odd n)
    {G : SimpleGraph (Fin n)} {s t u a b : Fin n}
    (P : G.Walk s t) (hp : P.IsPath)
    (ha : (G.deleteEdges P.toSubgraph.edgeSet).Adj u a)
    (hb : (G.deleteEdges P.toSubgraph.edgeSet).Adj u b) (hab : a ≠ b)
    (hN : ∀ x, (G.deleteEdges P.toSubgraph.edgeSet).Adj u x → x=a ∨ x=b)
    (hnon : ¬(G.deleteEdges P.toSubgraph.edgeSet).Adj a b)
    (hconn : ((bypass (G.deleteEdges P.toSubgraph.edgeSet) u a b).induce
      ({u}ᶜ : Set (Fin n))).Connected) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ := by
  classical
  have hc : ({u}ᶜ : Set (Fin n)).ncard=n-1 := by
    rw [Set.ncard_compl,Set.ncard_singleton,Nat.card_eq_fintype_card,Fintype.card_fin]
  obtain ⟨D,hD,hDc⟩ := hsmall.on_induce
    (bypass (G.deleteEdges P.toSubgraph.edgeSet) u a b) ({u}ᶜ : Set (Fin n))
    (by rw [hc]; have := Fin.pos u; omega) hconn
  obtain ⟨E,hE,hEc⟩ := restore_bypass ha hb hab hN D hD
  simp only [if_neg hnon,add_zero] at hEc
  obtain ⟨F,hF,hFc⟩ := restore_path_subgraph
    (show IsPathSubgraph P.toSubgraph from ⟨_,_,P,hp,rfl⟩) hE
  rw [hc,ceil_half] at hDc
  obtain ⟨k,hk⟩ := hn
  exact ⟨F,hF,by simp only [Fintype.card_fin,ceil_half]; omega⟩

lemma delete_spoke_pair_within {V : Type*} {G : SimpleGraph V} {u c d : V}
    (hc : G.Adj u c) (hd : G.Adj u d) :
    within (G.deleteEdges (Walk.cons hc.symm (Walk.cons hd Walk.nil)).toSubgraph.edgeSet)
      ({u}ᶜ : Set V)=within G ({u}ᶜ : Set V) := by
  ext x y
  simp only [within,deleteEdges_adj,Set.mem_compl_iff,Set.mem_singleton_iff]
  simp only [Walk.mem_edges_toSubgraph,Walk.edges_cons,Walk.edges_nil,List.mem_cons,List.not_mem_nil,or_false]
  constructor
  · tauto
  · rintro ⟨hxy,hx,hy⟩
    refine ⟨⟨hxy,?_⟩,hx,hy⟩
    rintro (he|he) <;> rcases Sym2.eq_iff.mp he with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> contradiction

lemma within_induce {V : Type*} (G : SimpleGraph V) (S : Set V) :
    (within G S).induce S=G.induce S := by
  ext x y
  exact and_iff_left (And.intro x.property y.property)

lemma degree_four_other_neighbors {V : Type*} [Fintype V] {G : SimpleGraph V}
    {u a b : V} (ha : G.Adj u a) (hb : G.Adj u b) (hab : a ≠ b)
    (hd : Nat.card (G.neighborSet u)=4) :
    ∃ c d, G.Adj u c ∧ G.Adj u d ∧ c ≠ d ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧
      ∀ x, G.Adj u x → x=a ∨ x=b ∨ x=c ∨ x=d := by
  classical
  have hcard : ((G.neighborFinset u).erase a |>.erase b).card=2 := by
    rw [Finset.card_erase_of_mem (by simp [mem_neighborFinset,hb,hab.symm]),
      Finset.card_erase_of_mem (by simpa using ha),card_neighborFinset_eq_degree]
    have hdeg : G.degree u=4 := by simpa only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree] using hd
    omega
  obtain ⟨c,d,hcd,heq⟩ := Finset.card_eq_two.mp hcard
  have hc : c ∈ ((G.neighborFinset u).erase a).erase b := by rw [heq]; simp
  have hd : d ∈ ((G.neighborFinset u).erase a).erase b := by rw [heq]; simp
  simp only [Finset.mem_erase,mem_neighborFinset] at hc hd
  refine ⟨c,d,hc.2.2,hd.2.2,hcd,hc.2.1.symm,hd.2.1.symm,hc.1.symm,hd.1.symm,?_⟩
  intro x hx
  by_cases hxa : x=a
  · exact Or.inl hxa
  by_cases hxb : x=b
  · exact Or.inr (Or.inl hxb)
  have hmem : x ∈ ((G.neighborFinset u).erase a).erase b := by simp [hx,hxa,hxb]
  rw [heq] at hmem
  exact Or.inr (Or.inr (by simpa using hmem))

lemma degree_four_nonedge {n : ℕ} (hsmall : SmallerOrders n) (hn : Odd n)
    {G : SimpleGraph (Fin n)} {u a b c d : Fin n}
    (ha : G.Adj u a) (hb : G.Adj u b) (hc : G.Adj u c) (hd : G.Adj u d)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hN : ∀ x, G.Adj u x → x=a ∨ x=b ∨ x=c ∨ x=d)
    (hnon : ¬G.Adj a b)
    (hconn : ((bypass G u a b).induce ({u}ᶜ : Set (Fin n))).Connected) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ := by
  classical
  let P : G.Walk c d := Walk.cons hc.symm (Walk.cons hd Walk.nil)
  have hp : P.IsPath := by simp [P,Walk.cons_isPath_iff,hc.ne.symm,hd.ne,hcd]
  let F := G.deleteEdges P.toSubgraph.edgeSet
  have haF : F.Adj u a := by
    simp only [F,deleteEdges_adj,P,Walk.mem_edges_toSubgraph,Walk.edges_cons,Walk.edges_nil,List.mem_cons,List.not_mem_nil,or_false]
    exact ⟨ha,by simp [hc.ne,hd.ne,hac,had]⟩
  have hbF : F.Adj u b := by
    simp only [F,deleteEdges_adj,P,Walk.mem_edges_toSubgraph,Walk.edges_cons,Walk.edges_nil,List.mem_cons,List.not_mem_nil,or_false]
    exact ⟨hb,by simp [hc.ne,hd.ne,hbc,hbd]⟩
  have hNF : ∀ x, F.Adj u x → x=a ∨ x=b := by
    intro x hx
    have hh := deleteEdges_adj.mp hx
    rcases hN x hh.1 with hxa|hxb|rfl|rfl
    · exact Or.inl hxa
    · exact Or.inr hxb
    · exact (hh.2 (by simp [P,Sym2.eq_swap])).elim
    · exact (hh.2 (by simp [P])).elim
  have hBy : bypass F u a b=bypass G u a b := by
    unfold bypass
    rw [show within F ({u}ᶜ : Set (Fin n))=within G ({u}ᶜ : Set (Fin n)) from delete_spoke_pair_within hc hd]
  apply suppress_after_path hsmall hn P hp haF hbF hab hNF
    (fun h ↦ hnon h.1)
  simpa only [←hBy] using hconn


lemma degree_four_pair_adj_of_connected_delete {n : ℕ} (hsmall : SmallerOrders n) (hn : Odd n)
    {G : SimpleGraph (Fin n)}
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    {u a b : Fin n} (hconn : (G.induce ({u}ᶜ : Set (Fin n))).Connected)
    (hd : Nat.card (G.neighborSet u)=4)
    (ha : G.Adj u a) (hb : G.Adj u b) (hab : a ≠ b) : G.Adj a b := by
  by_contra hnon
  obtain ⟨c,d,hc,hd,hcd,hac,had,hbc,hbd,hN⟩ := degree_four_other_neighbors ha hb hab hd
  exact hfail (degree_four_nonedge hsmall hn ha hb hc hd hab hac had hbc hbd hcd hN hnon
    (hconn.mono (by intro x y h; exact Or.inl ⟨h,x.property,y.property⟩)))

lemma bypass_four_path {V : Type*} {G : SimpleGraph V} {u a b c d : V}
    (hab : G.Adj a b) (hac : G.Adj a c) (hc : G.Adj u c) (hd : G.Adj u d)
    (hau : a ≠ u) (hbu : b ≠ u) (hbc : b ≠ c) :
    bypass (G.deleteEdges
      (Walk.cons hab.symm (Walk.cons hac (Walk.cons hc.symm (Walk.cons hd Walk.nil)))).toSubgraph.edgeSet)
      u a b = within (G.deleteEdges {s(a,c)}) ({u}ᶜ : Set V) := by
  ext x y
  simp only [bypass,sup_adj,within,deleteEdges_adj,Walk.mem_edges_toSubgraph,
    Walk.edges_cons,Walk.edges_nil,List.mem_cons,List.not_mem_nil,or_false,
    Set.mem_compl_iff,Set.mem_singleton_iff,fromEdgeSet_adj]
  constructor
  · rintro (⟨⟨hxy,hn⟩,hx,hy⟩ | ⟨he,hxy⟩)
    · exact ⟨⟨hxy,fun h ↦ hn (Or.inr (Or.inl h))⟩,hx,hy⟩
    · rcases Sym2.eq_iff.mp he with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · exact ⟨⟨hab,by simp [hbc,hab.ne.symm]⟩,hau,hbu⟩
      · exact ⟨⟨hab.symm,by simp [hbc,hxy]⟩,hbu,hau⟩
  · rintro ⟨⟨hxy,hac'⟩,hx,hy⟩
    by_cases he : s(x,y)=s(a,b)
    · exact Or.inr ⟨he,hxy.ne⟩
    refine Or.inl ⟨⟨hxy,?_⟩,hx,hy⟩
    rintro (hab'|hac'|hcu|hud)
    · exact he (hab'.trans Sym2.eq_swap)
    · contradiction
    · rcases Sym2.eq_iff.mp hcu with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> contradiction
    · rcases Sym2.eq_iff.mp hud with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> contradiction

lemma degree_four_clique {n : ℕ} (hsmall : SmallerOrders n) (hn : Odd n)
    {G : SimpleGraph (Fin n)} {u a b c d : Fin n}
    (ha : G.Adj u a) (hb : G.Adj u b) (hc : G.Adj u c) (hd : G.Adj u d)
    (hab : a ≠ b) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (habG : G.Adj a b) (hacG : G.Adj a c) (hbcG : G.Adj b c)
    (hN : ∀ x, G.Adj u x → x=a ∨ x=b ∨ x=c ∨ x=d)
    (hconn : (G.induce ({u}ᶜ : Set (Fin n))).Connected) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ := by
  classical
  let P : G.Walk b d := Walk.cons habG.symm (Walk.cons hacG (Walk.cons hc.symm (Walk.cons hd Walk.nil)))
  have hp : P.IsPath := by simp [P,Walk.cons_isPath_iff,hab.symm,hb.ne.symm,hbc,hbd,hacG.ne,ha.ne.symm,had,hc.ne.symm,hcd,hd.ne]
  let F := G.deleteEdges P.toSubgraph.edgeSet
  have haF : F.Adj u a := by
    simp only [F,deleteEdges_adj,P,Walk.mem_edges_toSubgraph,Walk.edges_cons,Walk.edges_nil,List.mem_cons,List.not_mem_nil,or_false]
    exact ⟨ha,by simp [ha.ne,hb.ne,hc.ne,hd.ne,hacG.ne,had]⟩
  have hbF : F.Adj u b := by
    simp only [F,deleteEdges_adj,P,Walk.mem_edges_toSubgraph,Walk.edges_cons,Walk.edges_nil,List.mem_cons,List.not_mem_nil,or_false]
    exact ⟨hb,by simp [ha.ne,hb.ne,hc.ne,hd.ne,hbc,hbd]⟩
  have hNF : ∀ x, F.Adj u x → x=a ∨ x=b := by
    intro x hx
    have hh := deleteEdges_adj.mp hx
    rcases hN x hh.1 with hxa|hxb|rfl|rfl
    · exact Or.inl hxa
    · exact Or.inr hxb
    · exact (hh.2 (by simp [P,Sym2.eq_swap])).elim
    · exact (hh.2 (by simp [P])).elim
  have hnon : ¬F.Adj a b := by
    intro h
    exact (deleteEdges_adj.mp h).2 (by simp [P,Sym2.eq_swap])
  have hBy : bypass F u a b=within (G.deleteEdges {s(a,c)}) ({u}ᶜ : Set (Fin n)) :=
    bypass_four_path habG hacG hc hd ha.ne.symm hb.ne.symm hbc
  apply suppress_after_path hsmall hn P hp haF hbF hab hNF hnon
  rw [hBy,within_induce,induce_delete_edge ({u}ᶜ : Set (Fin n)) ha.ne.symm hc.ne.symm]
  apply hconn.connected_delete_edge_of_not_isBridge
  exact edge_with_common_neighbor_not_bridge
    (show (G.induce ({u}ᶜ : Set (Fin n))).Adj ⟨a,ha.ne.symm⟩ ⟨b,hb.ne.symm⟩ from habG)
    (show (G.induce ({u}ᶜ : Set (Fin n))).Adj ⟨b,hb.ne.symm⟩ ⟨c,hc.ne.symm⟩ from hbcG)

lemma no_degree_four_of_connected_delete {n : ℕ} (hsmall : SmallerOrders n) (hn : Odd n)
    {G : SimpleGraph (Fin n)}
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    {u : Fin n} (hconn : (G.induce ({u}ᶜ : Set (Fin n))).Connected) :
    Nat.card (G.neighborSet u) ≠ 4 := by
  intro hdeg
  obtain ⟨a,b,ha,hb,hab⟩ := (Set.one_lt_ncard_iff (Set.toFinite _)).mp
    (show 1 < (G.neighborSet u).ncard by rw [←Nat.card_coe_set_eq,hdeg]; decide)
  obtain ⟨c,d,hc,hd,hcd,hac,had,hbc,hbd,hN⟩ := degree_four_other_neighbors ha hb hab hdeg
  have hcl {x y : Fin n} (hx : G.Adj u x) (hy : G.Adj u y) (hxy : x ≠ y) :=
    degree_four_pair_adj_of_connected_delete hsmall hn hfail hconn hdeg hx hy hxy
  exact hfail (degree_four_clique hsmall hn ha hb hc hd hab had hbc hbd hcd
    (hcl ha hb hab) (hcl ha hc hac) (hcl hb hc hbc) hN hconn)


lemma bypass_connected_of_neighbor_cover {V : Type*} {G : SimpleGraph V}
    (hG : G.Connected) {u a b : V} (ha : G.Adj u a) (hb : G.Adj u b) (hab : a ≠ b)
    (hcover : ∀ x, G.Adj u x →
      (within G ({u}ᶜ : Set V)).Reachable a x ∨
      (within G ({u}ᶜ : Set V)).Reachable b x) :
    ((bypass G u a b).induce ({u}ᶜ : Set V)).Connected := by
  let S : Set V := {u}ᶜ
  let J := bypass G u a b
  have hwithin : within G S ≤ within J S := by
    intro x y h
    exact ⟨Or.inl h,h.2⟩
  let a' : S := ⟨a,ha.ne.symm⟩
  let b' : S := ⟨b,hb.ne.symm⟩
  have habJ : (J.induce S).Adj a' b' := Or.inr ⟨rfl,hab⟩
  have hax (x : S) (hx : G.Adj u x.val) : (J.induce S).Reachable a' x := by
    rcases hcover x.val hx with h | h
    · exact within_reachable_induce a' x (h.mono hwithin)
    · exact habJ.reachable.trans (within_reachable_induce b' x (h.mono hwithin))
  let f : V → S := fun x ↦ if hx : x=u then a' else ⟨x,hx⟩
  have hf (x y : V) (hxy : G.Adj x y) : (J.induce S).Reachable (f x) (f y) := by
    by_cases hx : x=u
    · subst x
      simpa only [f,dif_pos rfl,dif_neg hxy.ne.symm] using hax ⟨y,hxy.ne.symm⟩ hxy
    by_cases hy : y=u
    · subst y
      simpa only [f,dif_pos rfl,dif_neg hxy.ne] using (hax ⟨x,hxy.ne⟩ hxy.symm).symm
    apply Adj.reachable
    change J.Adj (f x).val (f y).val
    simp only [f,dif_neg hx,dif_neg hy]
    exact Or.inl ⟨hxy,hx,hy⟩
  have hfx (x : S) : f x.val=x := by
    apply Subtype.ext
    have hx : x.val ≠ u := x.property
    simp [f,hx]
  letI : Nonempty S := ⟨a'⟩
  refine ⟨fun x y ↦ ?_⟩
  have hh := reachable_map_to_reachable f hf (hG.preconnected x.val y.val)
  simpa only [hfx] using hh

lemma disconnected_four_neighbors {V : Type*} [Fintype V] {G : SimpleGraph V}
    {u a b : V} (ha : G.Adj u a) (hb : G.Adj u b)
    (hdeg : Nat.card (G.neighborSet u)=4)
    (hnon : ¬(within G ({u}ᶜ : Set V)).Reachable a b)
    (hnb : ∀ x, G.Adj u x → ¬G.IsBridge s(u,x)) :
    ∃ c d, G.Adj u c ∧ G.Adj u d ∧ a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      (∀ x, G.Adj u x → x=a ∨ x=b ∨ x=c ∨ x=d) ∧
      (∀ x, G.Adj u x → (within G ({u}ᶜ : Set V)).Reachable a x ∨
        (within G ({u}ᶜ : Set V)).Reachable b x) := by
  classical
  obtain ⟨c,hc,hca,hac⟩ := nonbridge_neighbor_link ha (hnb a ha)
  obtain ⟨d,hd,hdb,hbd⟩ := nonbridge_neighbor_link hb (hnb b hb)
  have hab : a ≠ b := fun he ↦ hnon (he ▸ Reachable.rfl)
  have had : a ≠ d := by rintro rfl; exact hnon hbd.symm
  have hbc : b ≠ c := by rintro rfl; exact hnon hac
  have hcd : c ≠ d := by rintro rfl; exact hnon (hac.trans hbd.symm)
  have hsub : ({a,b,c,d} : Finset V) ⊆ G.neighborFinset u := by
    intro x hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rw [mem_neighborFinset]
    rcases hx with rfl|rfl|rfl|rfl <;> assumption
  have hc4 : ({a,b,c,d} : Finset V).card=4 := by
    simp [hab,hca.symm,had,hbc,hdb.symm,hcd]
  have heq : ({a,b,c,d} : Finset V)=G.neighborFinset u := by
    apply Finset.eq_of_subset_of_card_le hsub
    rw [hc4,card_neighborFinset_eq_degree]
    simpa only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree] using hdeg.le
  have hN : ∀ x, G.Adj u x → x=a ∨ x=b ∨ x=c ∨ x=d := by
    intro x hx
    have hh : x ∈ G.neighborFinset u := by simpa using hx
    rw [←heq] at hh
    simpa only [Finset.mem_insert,Finset.mem_singleton] using hh
  refine ⟨c,d,hc,hd,hab,hca.symm,had,hbc,hdb.symm,hcd,hN,?_⟩
  intro x hx
  rcases hN x hx with rfl|rfl|rfl|rfl
  · exact Or.inl Reachable.rfl
  · exact Or.inr Reachable.rfl
  · exact Or.inl hac
  · exact Or.inr hbd

lemma no_degree_four_of_odd_failure {n : ℕ} (hsmall : SmallerOrders n) (hn : Odd n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊) (u : Fin n) :
    Nat.card (G.neighborSet u) ≠ 4 := by
  classical
  intro hdeg
  by_cases hconn : (G.induce ({u}ᶜ : Set (Fin n))).Connected
  · exact no_degree_four_of_connected_delete hsmall hn hfail hconn hdeg
  obtain ⟨a,ha⟩ := (Set.ncard_pos (Set.toFinite _)).mp
    (show 0 < (G.neighborSet u).ncard by rw [←Nat.card_coe_set_eq,hdeg]; decide)
  obtain ⟨b,hb,hnon⟩ : ∃ b, G.Adj u b ∧ ¬(within G ({u}ᶜ : Set (Fin n))).Reachable a b := by
    by_contra! hh
    exact hconn (delete_vertex_connected_of_neighbor_links hG ha hh)
  obtain ⟨c,d,hc,hd,hab,hac,had,hbc,hbd,hcd,hN,hcover⟩ :=
    disconnected_four_neighbors ha hb hdeg hnon
      (fun x _ ↦ LeafReduction.bridgeless_of_odd_failure hsmall hn hG hfail s(u,x))
  have hnab : ¬G.Adj a b := fun h ↦ hnon (show (within G ({u}ᶜ : Set (Fin n))).Adj a b from
    ⟨h,ha.ne.symm,hb.ne.symm⟩).reachable
  exact hfail (degree_four_nonedge hsmall hn ha hb hc hd hab hac had hbc hbd hcd hN hnab
    (bypass_connected_of_neighbor_cover hG ha hb hab hcover))

lemma min_degree_five_of_odd_failure {n : ℕ} (hsmall : SmallerOrders n) (hn : Odd n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊) (u : Fin n) :
    5 ≤ Nat.card (G.neighborSet u) := by
  have h4 := min_degree_four_of_odd_failure hsmall hn hG hfail u
  have hne := no_degree_four_of_odd_failure hsmall hn hG hfail u
  omega

end Erdos583DegreeFourReductionDevelopment
