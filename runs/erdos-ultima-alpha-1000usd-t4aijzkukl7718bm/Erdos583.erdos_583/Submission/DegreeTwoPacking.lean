import Submission.Work

/-! Two degree-two vertices sharing a neighbor are reducible in a smallest
failure. In the twin case the existing common-neighbor edge is split through
a diamond; no unrestricted endpoint flexibility is used. -/
namespace Erdos583DegreeTwoPackingDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.VertexCritical Erdos583Work.BridgeGlue
open scoped Classical
set_option maxHeartbeats 1600000

lemma diamond_path_exchange {V : Type*} [Fintype V] {G : SimpleGraph V}
    {x y a b u v : V} (hab : G.Adj a b)
    (p : G.Walk x a) (q : G.Walk b y)
    (hp : (p.append (Walk.cons hab q)).IsPath)
    (hau : G.Adj a u) (hub : G.Adj u b) (hav : G.Adj a v) (hvb : G.Adj v b)
    (huv : u ≠ v) (hu : u ∉ (p.append (Walk.cons hab q)).support)
    (hv : v ∉ (p.append (Walk.cons hab q)).support) :
    ∃ A B : G.Subgraph, IsPathSubgraph A ∧ IsPathSubgraph B ∧
      Disjoint A.edgeSet B.edgeSet ∧
      A.edgeSet ∪ B.edgeSet = (p.append (Walk.cons hab q)).toSubgraph.edgeSet ∪
        {s(a,u),s(u,b),s(a,v),s(v,b)} := by
  classical
  let P := p.append (Walk.cons hab q)
  let R : G.Walk a v := .cons hau (.cons hub (.cons hvb.symm .nil))
  let A := p.append R
  let B := Walk.cons hav.symm (Walk.cons hab q)
  have hup : u ∉ p.support := fun h ↦ hu (by simp [h])
  have hvp : v ∉ p.support := fun h ↦ hv (by simp [h])
  have hbp : b ∉ p.support := fun h ↦
    TriangleAbsorption.append_cons_support_disjoint p hab q hp b h q.start_mem_support
  have hR : R.IsPath := by
    simp [R,Walk.cons_isPath_iff,hau.ne,hab.ne,hav.ne,hub.ne,huv,hvb.ne.symm]
  have hA : A.IsPath := by
    apply path_append_of_support_intersection hp.of_append_left hR
    intro z hz hzr
    have hz' : z=a ∨ z=u ∨ z=b ∨ z=v := by simpa [R] using hzr
    rcases hz' with rfl|rfl|rfl|rfl
    · rfl
    · exact (hup hz).elim
    · exact (hbp hz).elim
    · exact (hvp hz).elim
  have hB : B.IsPath := by
    apply (Walk.cons_isPath_iff _ _).mpr
    exact ⟨hp.of_append_right,fun hh ↦ hv ((Walk.mem_support_append_iff _ _).mpr (Or.inr hh))⟩
  let F : Set (Sym2 V) := {s(a,u),s(u,b),s(a,v),s(v,b)}
  have hc : A.toSubgraph.edgeSet ∪ B.toSubgraph.edgeSet=P.toSubgraph.edgeSet ∪ F := by
    ext e
    simp only [A,B,R,P,F,Walk.mem_edges_toSubgraph,Walk.edges_append,Walk.edges_cons,
      Walk.edges_nil,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,
      Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff,
      Sym2.eq_swap (a := b) (b := v),Sym2.eq_swap (a := v) (b := a)]
    tauto
  have hFP : Disjoint P.toSubgraph.edgeSet F := by
    apply Set.disjoint_left.mpr
    intro e he heF
    rcases heF with rfl|rfl|rfl|rfl
    · exact hu (Walk.mem_support_of_mem_edges (P.mem_edges_toSubgraph.mp he) (by simp))
    · exact hu (Walk.mem_support_of_mem_edges (P.mem_edges_toSubgraph.mp he) (by simp))
    · exact hv (Walk.mem_support_of_mem_edges (P.mem_edges_toSubgraph.mp he) (by simp))
    · exact hv (Walk.mem_support_of_mem_edges (P.mem_edges_toSubgraph.mp he) (by simp))
  have hF : F.ncard=4 := by
    simp [F,Set.ncard_insert_of_notMem,hau.ne,hub.ne,hav.ne,hvb.ne,
      huv,hab.ne,Ne.symm hau.ne,Ne.symm hvb.ne,
      Ne.symm hab.ne]
  refine ⟨A.toSubgraph,B.toSubgraph,⟨_,_,A,hA,rfl⟩,⟨_,_,B,hB,rfl⟩,?_,hc⟩
  apply TriangleAbsorption.disjoint_of_cover_length A B hA.isTrail hB.isTrail _ hc
  rw [Set.ncard_union_eq hFP,path_edgeSet_ncard hp,hF]
  simp [A,B,R]
  omega

lemma induce_dominated_boundary_connected {V : Type*} {G : SimpleGraph V}
    (hG : G.Connected) (T : Set V) {a : V} (ha : a ∉ T)
    (hbdy : ∀ x ∈ T, ∀ y ∉ T, G.Adj x y → y=a ∨ G.Adj a y) :
    (G.induce Tᶜ).Connected := by
  classical
  let f : V → ↥(Tᶜ) := fun x ↦ if hx : x ∈ T then ⟨a,ha⟩ else ⟨x,hx⟩
  have hf : ∀ x y, G.Adj x y → (G.induce Tᶜ).Reachable (f x) (f y) := by
    intro x y hxy
    by_cases hx : x ∈ T <;> by_cases hy : y ∈ T
    · simp only [f,dif_pos hx,dif_pos hy]; exact Reachable.rfl
    · simp only [f,dif_pos hx,dif_neg hy]
      rcases hbdy x hx y hy hxy with rfl|h
      · exact Reachable.rfl
      · exact Adj.reachable h
    · simp only [f,dif_neg hx,dif_pos hy]
      rcases hbdy y hy x hx hxy.symm with rfl|h
      · exact Reachable.rfl
      · exact (Adj.reachable (show (G.induce Tᶜ).Adj ⟨a,ha⟩ ⟨x,hx⟩ from h)).symm
    · simp only [f,dif_neg hx,dif_neg hy]
      exact Adj.reachable hxy
  have hfx (x : ↥(Tᶜ)) : f x.val=x := by
    apply Subtype.ext
    simp only [f,dif_neg x.property]
  letI : Nonempty ↥(Tᶜ) := ⟨⟨a,ha⟩⟩
  refine ⟨fun x y ↦ ?_⟩
  have h := reachable_map_to_reachable f hf (hG.preconnected x.val y.val)
  simpa only [hfx] using h

lemma two_triangular_tips_connected {V : Type*} {G : SimpleGraph V}
    (hG : G.Connected) {u v a b c : V}
    (hua : G.Adj u a) (hva : G.Adj v a) (hab : G.Adj a b) (hac : G.Adj a c)
    (hNu : ∀ z, G.Adj u z → z=a ∨ z=b)
    (hNv : ∀ z, G.Adj v z → z=a ∨ z=c) :
    (G.induce ({u,v}ᶜ : Set V)).Connected := by
  apply induce_dominated_boundary_connected hG {u,v} (a := a)
    (by simp [hua.ne.symm,hva.ne.symm])
  intro x hx y _ hxy
  rcases hx with rfl|rfl
  · rcases hNu y hxy with rfl|rfl
    · exact Or.inl rfl
    · exact Or.inr hab
  · rcases hNv y hxy with rfl|rfl
    · exact Or.inl rfl
    · exact Or.inr hac

lemma two_tips_edge_diff {V : Type*} {G : SimpleGraph V} {u v a b c : V}
    (hua : G.Adj u a) (hub : G.Adj u b) (hva : G.Adj v a) (hvc : G.Adj v c)
    (hNu : ∀ z, G.Adj u z → z=a ∨ z=b)
    (hNv : ∀ z, G.Adj v z → z=a ∨ z=c) :
    G.edgeSet \ (within G ({u,v}ᶜ : Set V)).edgeSet =
      {s(u,a),s(u,b),s(v,a),s(v,c)} := by
  ext e
  induction e using Sym2.ind with
  | h x y =>
    constructor
    · rintro ⟨hxy,hn⟩
      by_cases hx : x=u
      · subst x
        rcases hNu y hxy with rfl|rfl <;> simp
      by_cases hxv : x=v
      · subst x
        rcases hNv y hxy with rfl|rfl <;> simp
      by_cases hy : y=u
      · subst y
        rcases hNu x hxy.symm with rfl|rfl <;> simp [Sym2.eq_swap]
      by_cases hyv : y=v
      · subst y
        rcases hNv x hxy.symm with rfl|rfl <;> simp [Sym2.eq_swap]
      exact (hn ⟨hxy,by simp [hx,hxv],by simp [hy,hyv]⟩).elim
    · intro he
      have he' : s(x,y)=s(u,a) ∨ s(x,y)=s(u,b) ∨ s(x,y)=s(v,a) ∨ s(x,y)=s(v,c) := he
      rcases he' with he|he|he|he <;> rw [he]
      · exact ⟨hua,fun h ↦ h.2.1 (Or.inl rfl)⟩
      · exact ⟨hub,fun h ↦ h.2.1 (Or.inl rfl)⟩
      · exact ⟨hva,fun h ↦ h.2.1 (Or.inr rfl)⟩
      · exact ⟨hvc,fun h ↦ h.2.1 (Or.inr rfl)⟩

lemma distinct_tips_reduction {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected) {u v a b c : Fin n}
    (huv : u ≠ v) (hua : G.Adj u a) (hub : G.Adj u b)
    (hva : G.Adj v a) (hvc : G.Adj v c) (hab : G.Adj a b) (hac : G.Adj a c)
    (hbv : b ≠ v) (hcu : c ≠ u) (hbc : b ≠ c)
    (hNu : ∀ z, G.Adj u z → z=a ∨ z=b)
    (hNv : ∀ z, G.Adj v z → z=a ∨ z=c) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ := by
  classical
  let P : G.Walk b c := .cons hub.symm (.cons hua (.cons hva.symm (.cons hvc .nil)))
  have hp : P.IsPath := by
    simp [P,Walk.cons_isPath_iff,hub.ne.symm,hab.ne.symm,hbv,hbc,hua.ne,huv,
      hcu.symm,hva.ne.symm,hac.ne,hvc.ne]
  have hpe : P.toSubgraph.edgeSet=G.edgeSet \ (within G ({u,v}ᶜ : Set (Fin n))).edgeSet := by
    rw [two_tips_edge_diff hua hub hva hvc hNu hNv]
    ext e
    simp only [P,Walk.mem_edges_toSubgraph,Walk.edges_cons,Walk.edges_nil,
      List.mem_cons,List.not_mem_nil,or_false,Set.mem_insert_iff,Set.mem_singleton_iff,
      Sym2.eq_swap (a := b) (b := u),Sym2.eq_swap (a := a) (b := v)]
    tauto
  have hdel : G.deleteEdges P.toSubgraph.edgeSet=within G ({u,v}ᶜ : Set (Fin n)) := by
    apply edgeSet_injective
    rw [edgeSet_deleteEdges,hpe]
    ext e
    have hsub := edgeSet_mono (within_le G ({u,v}ᶜ : Set (Fin n)))
    simp only [Set.mem_diff]
    constructor
    · tauto
    · intro h
      exact ⟨hsub h,fun hn ↦ hn.2 h⟩
  obtain ⟨D,hD,hDc⟩ := hsmall.on_induce G ({u,v}ᶜ : Set (Fin n))
    (LeafPairReduction.two_removed_lt huv)
    (two_triangular_tips_connected hG hua hva hab hac hNu hNv)
  have hex := lift_induce_within ({u,v}ᶜ : Set (Fin n)) D hD
  rw [←hdel] at hex
  obtain ⟨E,hE,hEc⟩ := hex
  obtain ⟨F,hF,hFc⟩ := restore_path_subgraph ⟨_,_,P,hp,rfl⟩ hE
  exact ⟨F,hF,LeafPairReduction.two_removed_budget huv hDc (by omega)⟩

lemma restore_diamond {V : Type*} [Fintype V] {G : SimpleGraph V} {u v a b : V}
    (huv : u ≠ v) (hua : G.Adj u a) (hub : G.Adj u b)
    (hva : G.Adj v a) (hvb : G.Adj v b) (hab : G.Adj a b)
    (hNu : ∀ z, G.Adj u z → z=a ∨ z=b)
    (hNv : ∀ z, G.Adj v z → z=a ∨ z=b)
    (D : Finset (within G ({u,v}ᶜ : Set V)).Subgraph)
    (hD : GoodDecomposition (within G ({u,v}ᶜ : Set V)) D) :
    ∃ E : Finset G.Subgraph, GoodDecomposition G E ∧ E.card ≤ D.card+1 := by
  classical
  let H := within G ({u,v}ᶜ : Set V)
  have hle : H ≤ G := within_le _ _
  have habH : s(a,b) ∈ H.edgeSet := ⟨hab,by simp [hua.ne.symm,hva.ne.symm],by simp [hub.ne.symm,hvb.ne.symm]⟩
  have heD : s(a,b) ∈ ⋃ K ∈ D, K.edgeSet := hD.2.2.symm ▸ habH
  simp only [Set.mem_iUnion] at heD
  obtain ⟨K,hKD,heK⟩ := heD
  obtain ⟨x,y,p,hp,hKp⟩ := hD.1 K hKD
  let P := p.mapLe hle
  have hP : P.IsPath := hp.mapLe hle
  have hPe : P.toSubgraph.edgeSet=K.edgeSet := by simp [P,Walk.mapLe,hKp]
  have hPn : ¬p.Nil := by
    intro hn
    rw [hKp] at heK
    simp [Walk.edges_eq_nil.mpr hn] at heK
  have hf (z : V) (hz : z=u ∨ z=v) : z ∉ P.support := by
    intro hzp
    have hz' : z ∈ p.support := by simpa [P,Walk.mapLe] using hzp
    have hzs := path_support_subset_graph_support hp hPn z hz'
    exact (within_support G ({u,v}ᶜ : Set V) hzs) hz
  have heP : s(a,b) ∈ P.edges := P.mem_edges_toSubgraph.mp (hPe.symm ▸ heK)
  obtain ⟨c,d,hcd,L,R,hecd,hLR⟩ := walk_split_at_edge P s(a,b) heP
  have hpLR : (L.append (Walk.cons hcd R)).IsPath := hLR ▸ hP
  have huLR : u ∉ (L.append (Walk.cons hcd R)).support := hLR ▸ hf u (Or.inl rfl)
  have hvLR : v ∉ (L.append (Walk.cons hcd R)).support := hLR ▸ hf v (Or.inr rfl)
  have hex : ∃ A B : G.Subgraph, IsPathSubgraph A ∧ IsPathSubgraph B ∧
      Disjoint A.edgeSet B.edgeSet ∧
      A.edgeSet ∪ B.edgeSet=K.edgeSet ∪ (G.edgeSet \ H.edgeSet) := by
    rcases Sym2.eq_iff.mp hecd with ⟨hca,hdb⟩|⟨hda,hcb⟩
    · subst c; subst d
      obtain ⟨A,B,hA,hB,hd,hcov⟩ := diamond_path_exchange hcd L R hpLR
        hua.symm hub hva.symm hvb huv huLR hvLR
      refine ⟨A,B,hA,hB,hd,?_⟩
      rw [←hLR,hPe] at hcov
      rw [show G.edgeSet \ H.edgeSet={s(u,a),s(u,b),s(v,a),s(v,b)} from
        two_tips_edge_diff hua hub hva hvb hNu hNv]
      simpa only [Sym2.eq_swap (a := a) (b := u),Sym2.eq_swap (a := a) (b := v)] using hcov
    · subst d; subst c
      obtain ⟨A,B,hA,hB,hd,hcov⟩ := diamond_path_exchange hcd L R hpLR
        hub.symm hua hvb.symm hva huv huLR hvLR
      refine ⟨A,B,hA,hB,hd,?_⟩
      rw [←hLR,hPe] at hcov
      rw [show G.edgeSet \ H.edgeSet={s(u,a),s(u,b),s(v,a),s(v,b)} from
        two_tips_edge_diff hua hub hva hvb hNu hNv]
      rw [hcov]
      ext e
      simp only [Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff,
        Sym2.eq_swap (a := b) (b := u),Sym2.eq_swap (a := b) (b := v)]
      tauto
  obtain ⟨A,B,hA,hB,hd,hcover⟩ := hex
  exact hD.extend_replace_one hle hKD hA hB hd hcover

lemma twin_tips_reduction {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected) {u v a b : Fin n}
    (huv : u ≠ v) (hua : G.Adj u a) (hub : G.Adj u b)
    (hva : G.Adj v a) (hvb : G.Adj v b) (hab : G.Adj a b)
    (hNu : ∀ z, G.Adj u z → z=a ∨ z=b)
    (hNv : ∀ z, G.Adj v z → z=a ∨ z=b) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ := by
  obtain ⟨D,hD,hDc⟩ := hsmall.on_induce G ({u,v}ᶜ : Set (Fin n))
    (LeafPairReduction.two_removed_lt huv)
    (two_triangular_tips_connected hG hua hva hab hab hNu hNv)
  obtain ⟨E,hE,hEc⟩ := lift_induce_within ({u,v}ᶜ : Set (Fin n)) D hD
  obtain ⟨F,hF,hFc⟩ := restore_diamond huv hua hub hva hvb hab hNu hNv E hE
  exact ⟨F,hF,LeafPairReduction.two_removed_budget huv hDc (by omega)⟩

lemma degree_two_triangle_at_neighbor {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    {u a : Fin n} (hua : G.Adj u a) (hu : Nat.card (G.neighborSet u)=2) :
    ∃ b, G.Adj u b ∧ G.Adj a b ∧ ∀ z, G.Adj u z → z=a ∨ z=b := by
  obtain ⟨_,b,c,hbc,hN,hbcG⟩ := DegreeTwoReduction.degree_two_triangle hsmall hG hfail hu
  have ha : a=b ∨ a=c := (show a ∈ ({b,c} : Set (Fin n)) from hN ▸ hua)
  rcases ha with rfl|rfl
  · refine ⟨c,?_,hbcG,?_⟩
    · change c ∈ G.neighborSet u; rw [hN]; exact Or.inr rfl
    · intro z hz; exact (show z ∈ ({a,c} : Set (Fin n)) from hN ▸ hz)
  · refine ⟨b,?_,hbcG.symm,?_⟩
    · change b ∈ G.neighborSet u; rw [hN]; exact Or.inl rfl
    · intro z hz
      exact (show z ∈ ({b,a} : Set (Fin n)) from hN ▸ hz).symm

/-- Distinct degree-two vertices in a smallest failure cannot share a
neighbor, whether their other neighbors are equal or different. -/
lemma degree_two_neighbors_disjoint {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    {u v : Fin n} (huv : u ≠ v)
    (hu : Nat.card (G.neighborSet u)=2) (hv : Nat.card (G.neighborSet v)=2) :
    Disjoint (G.neighborSet u) (G.neighborSet v) := by
  apply Set.disjoint_left.mpr
  intro a hua hva
  obtain ⟨b,hub,hab,hNu⟩ := degree_two_triangle_at_neighbor hsmall hG hfail hua hu
  obtain ⟨c,hvc,hac,hNv⟩ := degree_two_triangle_at_neighbor hsmall hG hfail hva hv
  by_cases hbc : b=c
  · subst c
    exact hfail (twin_tips_reduction hsmall hG huv hua hub hva hvc hab hNu hNv)
  · have hbv : b ≠ v := by
      rintro rfl
      exact LowDegreeAdjacency.degree_two_not_adjacent_degree_two hsmall hG hfail hub hu hv
    have hcu : c ≠ u := by
      rintro rfl
      exact LowDegreeAdjacency.degree_two_not_adjacent_degree_two hsmall hG hfail hvc hv hu
    exact hfail (distinct_tips_reduction hsmall hG huv hua hub hva hvc hab hac hbv hcu hbc hNu hNv)

lemma degree_two_closed_neighbors_disjoint {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    {u v : Fin n} (huv : u ≠ v)
    (hu : Nat.card (G.neighborSet u)=2) (hv : Nat.card (G.neighborSet v)=2) :
    Disjoint (insert u (G.neighborSet u)) (insert v (G.neighborSet v)) := by
  apply Set.disjoint_left.mpr
  intro a hau hav
  rcases hau with rfl|hau <;> rcases hav with hav|hav
  · exact huv hav
  · exact LowDegreeAdjacency.degree_two_not_adjacent_degree_two hsmall hG hfail hav hv hu
  · subst a
    exact LowDegreeAdjacency.degree_two_not_adjacent_degree_two hsmall hG hfail hau hu hv
  · exact Set.disjoint_left.mp (degree_two_neighbors_disjoint hsmall hG hfail huv hu hv) hau hav

/-- Degree-two vertices occupy disjoint closed-neighborhood triples. -/
lemma degree_two_card_bound {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊) :
    3*{u | Nat.card (G.neighborSet u)=2}.ncard ≤ n := by
  classical
  let I := {u | Nat.card (G.neighborSet u)=2}.toFinset
  let B := fun u ↦ (insert u (G.neighborSet u)).toFinset
  have hI : I.card={u | Nat.card (G.neighborSet u)=2}.ncard := by
    simp only [I,Set.toFinset_card,←Nat.card_eq_fintype_card,Nat.card_coe_set_eq]
  have hB : ∀ u ∈ I, (B u).card=3 := by
    intro u hu
    have hu' : Nat.card (G.neighborSet u)=2 := by simpa [I] using hu
    have hnot : u ∉ G.neighborSet u := G.irrefl
    change (insert u (G.neighborSet u)).toFinset.card=3
    rw [Set.toFinset_insert,Finset.card_insert_of_notMem (fun h ↦ hnot (Set.mem_toFinset.mp h)),Set.toFinset_card]
    rw [←Nat.card_eq_fintype_card,hu']
  have hdis : (I : Set (Fin n)).PairwiseDisjoint B := by
    intro u hu v hv huv
    have hu' : Nat.card (G.neighborSet u)=2 := by simpa [I] using hu
    have hv' : Nat.card (G.neighborSet v)=2 := by simpa [I] using hv
    apply Finset.disjoint_left.mpr
    intro a hau hav
    exact Set.disjoint_left.mp (degree_two_closed_neighbors_disjoint hsmall hG hfail huv hu' hv')
      (Set.mem_toFinset.mp hau) (Set.mem_toFinset.mp hav)
  have hc := (I.biUnion B).card_le_univ
  rw [Finset.card_biUnion hdis,Finset.sum_const_nat hB,hI,Fintype.card_fin] at hc
  omega

end Erdos583DegreeTwoPackingDevelopment
