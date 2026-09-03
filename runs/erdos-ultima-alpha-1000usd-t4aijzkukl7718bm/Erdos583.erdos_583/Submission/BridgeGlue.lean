import Submission.Work

/-! Exact path-decomposition gluing across a bridge, with a pendant copy of
that bridge in each side. This is a conditional gluing theorem, not a
reduction to bridgeless graphs. -/
open SimpleGraph Erdos583Work
namespace Erdos583BridgeGlueDevelopment
open scoped Classical
set_option maxHeartbeats 1200000

lemma union_path_shared_edge {V : Type*} {G : SimpleGraph V} {u v : V}
    (h : G.Adj u v) {a b : V} (p : G.Walk u a) (q : G.Walk v b)
    (hp : (Walk.cons h.symm p).IsPath) (hq : (Walk.cons h q).IsPath)
    (hi : ∀ x ∈ p.support, x ∈ q.support → x=u ∨ x=v) :
    IsPathSubgraph ((Walk.cons h.symm p).toSubgraph ⊔ (Walk.cons h q).toSubgraph) := by
  have hpp := (Walk.cons_isPath_iff h.symm p).mp hp
  have hpath : (p.reverse.append (Walk.cons h q)).IsPath := by
    apply path_append_of_support_intersection hpp.1.reverse hq
    intro x hx hy
    have hxp : x ∈ p.support := by simpa using hx
    rcases List.mem_cons.mp hy with rfl | hy
    · rfl
    · rcases hi x hxp hy with rfl | rfl
      · rfl
      · exact (hpp.2 hxp).elim
  refine ⟨a,b,p.reverse.append (Walk.cons h q),hpath,?_⟩
  simp only [Walk.toSubgraph_append,Walk.toSubgraph_reverse,Walk.toSubgraph,
    ← subgraphOfAdj_symm h]
  simp [sup_assoc,sup_left_comm]

/-- Glue two partial decompositions whose only common edge is in the two
specified members. Those members may even be the same singleton edge. -/
lemma merge_partial_partitions {V : Type*} {G : SimpleGraph V}
    (D E : Finset G.Subgraph) (K L : G.Subgraph) (e : Sym2 V)
    (hpD : ∀ H ∈ D, IsPathSubgraph H) (hpE : ∀ H ∈ E, IsPathSubgraph H)
    (hdD : Set.PairwiseDisjoint (D : Set G.Subgraph) (fun H ↦ H.edgeSet))
    (hdE : Set.PairwiseDisjoint (E : Set G.Subgraph) (fun H ↦ H.edgeSet))
    (hK : K ∈ D) (hL : L ∈ E) (heK : e ∈ K.edgeSet) (heL : e ∈ L.edgeSet)
    (hinter : ∀ H ∈ D, ∀ J ∈ E, H.edgeSet ∩ J.edgeSet ⊆ {e})
    (hcover : (⋃ H ∈ D, H.edgeSet) ∪ (⋃ H ∈ E, H.edgeSet)=G.edgeSet)
    (hp : IsPathSubgraph (K ⊔ L)) :
    ∃ F : Finset G.Subgraph, GoodDecomposition G F ∧ F.card+1 ≤ D.card+E.card := by
  classical
  let R := D.erase K ∪ E.erase L
  let F := insert (K ⊔ L) R
  have hcross {H J : G.Subgraph} (hH : H ∈ D) (hJ : J ∈ E)
      (hne : H ≠ K ∨ J ≠ L) : Disjoint H.edgeSet J.edgeSet := by
    apply Set.disjoint_left.mpr
    intro f hf hg
    have hfe : f=e := hinter H hH J hJ ⟨hf,hg⟩
    subst f
    rcases hne with hne | hne
    · exact Set.disjoint_left.mp (hdD hH hK hne) hf heK
    · exact Set.disjoint_left.mp (hdE hJ hL hne) hg heL
  have hrest {H : G.Subgraph} (hH : H ∈ R) : Disjoint (K ⊔ L).edgeSet H.edgeSet := by
    rw [Subgraph.edgeSet_sup]
    apply disjoint_sup_left.mpr
    rcases Finset.mem_union.mp hH with hHD | hHE
    · obtain ⟨hHK,hHD⟩ := Finset.mem_erase.mp hHD
      exact ⟨hdD hK hHD hHK.symm,(hcross hHD hL (Or.inl hHK)).symm⟩
    · obtain ⟨hHL,hHE⟩ := Finset.mem_erase.mp hHE
      exact ⟨hcross hK hHE (Or.inr hHL),hdE hL hHE hHL.symm⟩
  refine ⟨F,⟨?_,?_,?_⟩,?_⟩
  · intro H hH
    rcases Finset.mem_insert.mp hH with rfl | hH
    · exact hp
    · rcases Finset.mem_union.mp hH with hH | hH
      · exact hpD H (Finset.mem_of_mem_erase hH)
      · exact hpE H (Finset.mem_of_mem_erase hH)
  · intro H hH J hJ hHJ
    rcases Finset.mem_insert.mp hH with rfl | hH <;>
      rcases Finset.mem_insert.mp hJ with rfl | hJ
    · exact (hHJ rfl).elim
    · exact hrest hJ
    · exact (hrest hH).symm
    · rcases Finset.mem_union.mp hH with hHD | hHE <;>
        rcases Finset.mem_union.mp hJ with hJD | hJE
      · exact hdD (Finset.mem_of_mem_erase hHD) (Finset.mem_of_mem_erase hJD) hHJ
      · exact hcross (Finset.mem_of_mem_erase hHD) (Finset.mem_of_mem_erase hJE)
          (Or.inl (Finset.mem_erase.mp hHD).1)
      · exact (hcross (Finset.mem_of_mem_erase hJD) (Finset.mem_of_mem_erase hHE)
          (Or.inl (Finset.mem_erase.mp hJD).1)).symm
      · exact hdE (Finset.mem_of_mem_erase hHE) (Finset.mem_of_mem_erase hJE) hHJ
  · ext f
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨H,_,hf⟩
      exact H.edgeSet_subset hf
    · intro hf
      rw [←hcover] at hf
      simp only [Set.mem_union,Set.mem_iUnion] at hf
      rcases hf with ⟨H,hH,hf⟩ | ⟨H,hH,hf⟩
      · by_cases heq : H=K
        · subst H
          exact ⟨K ⊔ L,Finset.mem_insert_self _ _,by rw [Subgraph.edgeSet_sup]; exact Or.inl hf⟩
        · exact ⟨H,Finset.mem_insert_of_mem (Finset.mem_union_left _
            (Finset.mem_erase.mpr ⟨heq,hH⟩)),hf⟩
      · by_cases heq : H=L
        · subst H
          exact ⟨K ⊔ L,Finset.mem_insert_self _ _,by rw [Subgraph.edgeSet_sup]; exact Or.inr hf⟩
        · exact ⟨H,Finset.mem_insert_of_mem (Finset.mem_union_right _
            (Finset.mem_erase.mpr ⟨heq,hH⟩)),hf⟩
  · have hc : F.card ≤ (D.erase K).card+(E.erase L).card+1 :=
      (Finset.card_insert_le _ _).trans (by have := Finset.card_union_le (D.erase K) (E.erase L); dsimp [R]; omega)
    have hk := Finset.card_erase_add_one hK
    have hl := Finset.card_erase_add_one hL
    omega

lemma terminal_edge_rep {V : Type*} {A : SimpleGraph V} {u v : V}
    (h : A.Adj u v) (hLeaf : ∀ x, A.Adj v x → x=u)
    {K : A.Subgraph} (hpK : IsPathSubgraph K) (he : s(u,v) ∈ K.edgeSet) :
    ∃ a, ∃ p : A.Walk u a, (Walk.cons h.symm p).IsPath ∧
      K=(Walk.cons h.symm p).toSubgraph := by
  have hKvu : K.Adj v u := (show K.Adj u v from he).symm
  have heq : K.neighborSet v={u} := by
    ext x
    constructor
    · exact fun hx ↦ hLeaf x (K.adj_sub hx)
    · rintro rfl
      exact hKvu
  have hn : (K.neighborSet v).ncard=1 := by rw [heq,Set.ncard_singleton]
  obtain ⟨a,r,hr,hKr⟩ := path_endpoint_of_neighbor_ncard_one hpK hn
  cases r with
  | nil => simp [hKr] at hn
  | @cons _ w _ hw p =>
    have hwU : w=u := hLeaf w hw
    subst w
    exact ⟨a,p,hr,hKr⟩

/-- Spanning side graphs share exactly a bridge and have its opposite ends
as leaves. A decomposition of each side glues with a saving of one member. -/
lemma glue_spanning_sides {V : Type*} [Fintype V] {G A B : SimpleGraph V}
    {u v : V} (hA : A.Adj u v) (hB : B.Adj u v)
    (hAG : A ≤ G) (hBG : B ≤ G)
    (hcover : A.edgeSet ∪ B.edgeSet=G.edgeSet)
    (hinter : ∀ x ∈ A.support, x ∈ B.support → x=u ∨ x=v)
    (hLeafA : ∀ x, A.Adj v x → x=u) (hLeafB : ∀ x, B.Adj u x → x=v)
    (D : Finset A.Subgraph) (E : Finset B.Subgraph)
    (hD : GoodDecomposition A D) (hE : GoodDecomposition B E) :
    ∃ F : Finset G.Subgraph, GoodDecomposition G F ∧ F.card+1 ≤ D.card+E.card := by
  classical
  have hd : ∃ K ∈ D, s(u,v) ∈ K.edgeSet := by
    have hh : s(u,v) ∈ ⋃ K ∈ D, K.edgeSet := hD.2.2.symm ▸ hA
    simpa only [Set.mem_iUnion,exists_prop] using hh
  have he : ∃ L ∈ E, s(u,v) ∈ L.edgeSet := by
    have hh : s(u,v) ∈ ⋃ L ∈ E, L.edgeSet := hE.2.2.symm ▸ hB
    simpa only [Set.mem_iUnion,exists_prop] using hh
  obtain ⟨K,hKD,hKe⟩ := hd
  obtain ⟨L,hLE,hLe⟩ := he
  obtain ⟨a,p,hp,hKp⟩ := terminal_edge_rep hA hLeafA (hD.1 K hKD) hKe
  obtain ⟨b,q,hq,hLq⟩ := terminal_edge_rep hB.symm hLeafB (hE.1 L hLE)
    (by simpa only [Sym2.eq_swap] using hLe)
  let D' := D.image (Subgraph.map (Hom.ofLE hAG))
  let E' := E.image (Subgraph.map (Hom.ofLE hBG))
  let K' := K.map (Hom.ofLE hAG)
  let L' := L.map (Hom.ofLE hBG)
  have hK' : K' ∈ D' := Finset.mem_image.mpr ⟨K,hKD,rfl⟩
  have hL' : L' ∈ E' := Finset.mem_image.mpr ⟨L,hLE,rfl⟩
  have hKe' : s(u,v) ∈ K'.edgeSet := by rwa [edgeSet_lift]
  have hLe' : s(u,v) ∈ L'.edgeSet := by rwa [edgeSet_lift]
  have hpathsD : ∀ J ∈ D', IsPathSubgraph J := by
    intro J hJ
    obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hJ
    exact lift_path_subgraph hAG (hD.1 I hI)
  have hpathsE : ∀ J ∈ E', IsPathSubgraph J := by
    intro J hJ
    obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hJ
    exact lift_path_subgraph hBG (hE.1 I hI)
  have hinter' : ∀ J ∈ D', ∀ M ∈ E', J.edgeSet ∩ M.edgeSet ⊆ {s(u,v)} := by
    intro J hJ M hM e he
    obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hJ
    obtain ⟨N,hN,rfl⟩ := Finset.mem_image.mp hM
    simp only [Set.mem_inter_iff,edgeSet_lift] at he
    have heA := I.edgeSet_subset he.1
    have heB := N.edgeSet_subset he.2
    induction e using Sym2.ind with
    | h x y =>
      have hx := hinter x ((A.mem_support).mpr ⟨y,heA⟩) ((B.mem_support).mpr ⟨y,heB⟩)
      have hy := hinter y ((A.mem_support).mpr ⟨x,heA.symm⟩) ((B.mem_support).mpr ⟨x,heB.symm⟩)
      rcases hx with rfl|rfl <;> rcases hy with rfl|rfl
      · exact (A.loopless _ heA).elim
      · rfl
      · exact Sym2.eq_swap
      · exact (A.loopless _ heA).elim
  have hcover' : (⋃ J ∈ D', J.edgeSet) ∪ (⋃ J ∈ E', J.edgeSet)=G.edgeSet := by
    rw [IsDecomposition.lift_union hAG hD.2,IsDecomposition.lift_union hBG hE.2]
    exact hcover
  have hKG : K'=(Walk.cons (hAG hA).symm (p.mapLe hAG)).toSubgraph := by
    simp [K',hKp,Walk.mapLe,Subgraph.map_sup]
  have hLG : L'=(Walk.cons (hAG hA) (q.mapLe hBG)).toSubgraph := by
    simp [L',hLq,Walk.mapLe,Subgraph.map_sup]
  have hpG : (Walk.cons (hAG hA).symm (p.mapLe hAG)).IsPath := by
    simpa only [Walk.mapLe,Walk.map_cons] using hp.mapLe hAG
  have hqG : (Walk.cons (hAG hA) (q.mapLe hBG)).IsPath := by
    simpa only [Walk.mapLe,Walk.map_cons] using hq.mapLe hBG
  have hpath : IsPathSubgraph (K' ⊔ L') := by
    rw [hKG,hLG]
    apply union_path_shared_edge (hAG hA) _ _ hpG hqG
    intro x hx hy
    have hx' : x ∈ p.support := by simpa [Walk.mapLe] using hx
    have hy' : x ∈ q.support := by simpa [Walk.mapLe] using hy
    exact hinter x (path_support_subset_graph_support hp (by simp) x (List.mem_cons_of_mem _ hx'))
      (path_support_subset_graph_support hq (by simp) x (List.mem_cons_of_mem _ hy'))
  obtain ⟨F,hF,hFc⟩ := merge_partial_partitions D' E' K' L' s(u,v) hpathsD hpathsE
    (hD.2.lift_pairwise hAG) (hE.2.lift_pairwise hBG) hK' hL' hKe' hLe' hinter' hcover' hpath
  exact ⟨F,hF,hFc.trans (Nat.add_le_add Finset.card_image_le Finset.card_image_le)⟩

/-- The induced graph, retained on the original ambient type with isolated
vertices outside the set. -/
def within {V : Type*} (G : SimpleGraph V) (S : Set V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ x ∈ S ∧ y ∈ S
  symm := by intro x y h; exact ⟨h.1.symm,h.2.2,h.2.1⟩
  loopless := by intro x h; exact G.loopless x h.1

lemma within_le {V : Type*} (G : SimpleGraph V) (S : Set V) : within G S ≤ G :=
  fun _ _ h ↦ h.1

lemma within_support {V : Type*} (G : SimpleGraph V) (S : Set V) :
    (within G S).support ⊆ S := by
  intro x hx
  obtain ⟨y,hy⟩ := (mem_support _).mp hx
  exact hy.2.1

lemma lift_induce_within {V : Type*} {G : SimpleGraph V} (S : Set V)
    (D : Finset (G.induce S).Subgraph) (hD : GoodDecomposition (G.induce S) D) :
    ∃ E : Finset (within G S).Subgraph, GoodDecomposition (within G S) E ∧ E.card ≤ D.card := by
  let f : G.induce S →g within G S :=
    { toFun := Subtype.val
      map_rel' := fun {x y} h ↦ ⟨h,x.property,y.property⟩ }
  apply hD.map_of_edge_surjective f Subtype.val_injective
  apply Set.Subset.antisymm
  · intro e he
    induction e using Sym2.ind with
    | h x y => exact ⟨s(⟨x,he.2.1⟩,⟨y,he.2.2⟩),he.1,rfl⟩
  · rintro e ⟨a,ha,rfl⟩
    exact f.map_mem_edgeSet ha

lemma glue_cut_sides {V : Type*} [Fintype V] {G : SimpleGraph V}
    (S : Set V) {u v : V} (h : G.Adj u v) (hu : u ∈ S) (hv : v ∉ S)
    (hcross : ∀ x ∈ S, ∀ y ∉ S, G.Adj x y → x=u ∧ y=v)
    (D : Finset (G.induce (insert v S)).Subgraph)
    (E : Finset (G.induce (insert u Sᶜ)).Subgraph)
    (hD : GoodDecomposition (G.induce (insert v S)) D)
    (hE : GoodDecomposition (G.induce (insert u Sᶜ)) E) :
    ∃ F : Finset G.Subgraph, GoodDecomposition G F ∧ F.card+1 ≤ D.card+E.card := by
  let A := within G (insert v S)
  let B := within G (insert u Sᶜ)
  have hA : A.Adj u v := ⟨h,Set.mem_insert_of_mem _ hu,Set.mem_insert _ _⟩
  have hB : B.Adj u v := ⟨h,Set.mem_insert _ _,Set.mem_insert_of_mem _ hv⟩
  have hcover : A.edgeSet ∪ B.edgeSet=G.edgeSet := by
    ext e
    constructor
    · rintro (he|he)
      · exact edgeSet_mono (within_le _ _) he
      · exact edgeSet_mono (within_le _ _) he
    · induction e using Sym2.ind with
      | h x y =>
        intro he
        by_cases hx : x ∈ S <;> by_cases hy : y ∈ S
        · exact Or.inl ⟨he,Or.inr hx,Or.inr hy⟩
        · obtain ⟨rfl,rfl⟩ := hcross x hx y hy he
          exact Or.inl hA
        · obtain ⟨rfl,rfl⟩ := hcross y hy x hx he.symm
          exact Or.inl hA.symm
        · exact Or.inr ⟨he,Or.inr hx,Or.inr hy⟩
  have hinter : ∀ x ∈ A.support, x ∈ B.support → x=u ∨ x=v := by
    intro x hx hy
    have hx' := within_support G (insert v S) hx
    have hy' := within_support G (insert u Sᶜ) hy
    simp only [Set.mem_insert_iff,Set.mem_compl_iff] at hx' hy'
    tauto
  have hLeafA : ∀ x, A.Adj v x → x=u := by
    intro x hx
    rcases hx.2.2 with hxv | hxS
    · exact (hx.1.ne hxv.symm).elim
    · exact (hcross x hxS v hv hx.1.symm).1
  have hLeafB : ∀ x, B.Adj u x → x=v := by
    intro x hx
    rcases hx.2.2 with hxu | hxS
    · exact (hx.1.ne hxu.symm).elim
    · exact (hcross u hu x hxS hx.1).2
  obtain ⟨D',hD',hDc⟩ := lift_induce_within (insert v S) D hD
  obtain ⟨E',hE',hEc⟩ := lift_induce_within (insert u Sᶜ) E hE
  obtain ⟨F,hF,hFc⟩ := glue_spanning_sides hA hB (within_le _ _) (within_le _ _)
    hcover hinter hLeafA hLeafB D' E' hD' hE'
  exact ⟨F,hF,hFc.trans (Nat.add_le_add hDc hEc)⟩

/-- Each augmented side of a single-edge cut is connected. The proof collapses
the opposite side to the one added pendant vertex. -/
lemma cut_side_connected {V : Type*} {G : SimpleGraph V}
    (hG : G.Connected) (S : Set V) {u v : V} (h : G.Adj u v)
    (hu : u ∈ S) (hv : v ∉ S)
    (hcross : ∀ x ∈ S, ∀ y ∉ S, G.Adj x y → x=u ∧ y=v) :
    (G.induce (insert v S)).Connected := by
  classical
  let f : V → ↥(insert v S) := fun x ↦ if hx : x ∈ S then ⟨x,Or.inr hx⟩ else ⟨v,Or.inl rfl⟩
  have hf : ∀ x y, G.Adj x y → (G.induce (insert v S)).Reachable (f x) (f y) := by
    intro x y hxy
    by_cases hx : x ∈ S <;> by_cases hy : y ∈ S
    · apply Adj.reachable
      simpa [f,hx,hy] using hxy
    · obtain ⟨rfl,rfl⟩ := hcross x hx y hy hxy
      apply Adj.reachable
      simpa [f,hu,hv] using h
    · obtain ⟨rfl,rfl⟩ := hcross y hy x hx hxy.symm
      apply Adj.reachable
      simpa [f,hu,hv] using h.symm
    · simp only [f,dif_neg hx,dif_neg hy]
      exact Reachable.rfl
  have hfx (x : ↥(insert v S)) : f x.val=x := by
    apply Subtype.ext
    rcases x.property with hh | hh
    · simp [f,hh,hv]
    · simp [f,hh]
  letI : Nonempty ↥(insert v S) := ⟨⟨v,Or.inl rfl⟩⟩
  refine ⟨fun x y ↦ ?_⟩
  have hh := reachable_map_to_reachable f hf (hG.preconnected x.val y.val)
  simpa only [hfx] using hh

lemma ceil_half (n : ℕ) : ⌈(n : ℚ)/2⌉₊=(n+1)/2 := by
  have hlo : n ≤ 2*⌈(n : ℚ)/2⌉₊ := by
    have hh := Nat.le_ceil ((n : ℚ)/2)
    exact_mod_cast (show (n : ℚ) ≤ 2*(⌈(n : ℚ)/2⌉₊ : ℚ) by linarith)
  have hhi : 2*⌈(n : ℚ)/2⌉₊ < n+2 := by
    have hh := Nat.ceil_lt_add_one (show (0 : ℚ) ≤ (n : ℚ)/2 by positivity)
    exact_mod_cast (show 2*(⌈(n : ℚ)/2⌉₊ : ℚ) < (n : ℚ)+2 by linarith)
  omega

lemma augmented_budget (a b : ℕ) (ho : Odd a ∨ Odd b) :
    ⌈((a+1 : ℕ) : ℚ)/2⌉₊+⌈((b+1 : ℕ) : ℚ)/2⌉₊ ≤ ⌈((a+b : ℕ) : ℚ)/2⌉₊+1 := by
  simp only [ceil_half]
  rcases ho with ⟨k,hk⟩|⟨k,hk⟩ <;> omega

/-- The same gluing count is one too large when both sides have even order.
This arithmetic obstruction is why gluing alone does not give bridgelessness. -/
lemma augmented_budget_even (a b : ℕ) (ha : Even a) (hb : Even b) :
    ⌈((a+1 : ℕ) : ℚ)/2⌉₊+⌈((b+1 : ℕ) : ℚ)/2⌉₊=⌈((a+b : ℕ) : ℚ)/2⌉₊+2 := by
  simp only [ceil_half]
  obtain ⟨r,hr⟩ := ha
  obtain ⟨s,hs⟩ := hb
  omega

lemma gallai_of_cut_side_budgets {V : Type*} [Fintype V] {G : SimpleGraph V}
    (S : Set V) {u v : V} (h : G.Adj u v) (hu : u ∈ S) (hv : v ∉ S)
    (hcross : ∀ x ∈ S, ∀ y ∉ S, G.Adj x y → x=u ∧ y=v)
    (ho : Odd S.ncard ∨ Odd Sᶜ.ncard)
    (hleft : ∃ D : Finset (G.induce (insert v S)).Subgraph,
      GoodDecomposition (G.induce (insert v S)) D ∧ D.card ≤ ⌈((S.ncard+1 : ℕ) : ℚ)/2⌉₊)
    (hright : ∃ E : Finset (G.induce (insert u Sᶜ)).Subgraph,
      GoodDecomposition (G.induce (insert u Sᶜ)) E ∧ E.card ≤ ⌈((Sᶜ.ncard+1 : ℕ) : ℚ)/2⌉₊) :
    ∃ F : Finset G.Subgraph, GoodDecomposition G F ∧ F.card ≤ ⌈(Fintype.card V : ℚ)/2⌉₊ := by
  obtain ⟨D,hD,hDc⟩ := hleft
  obtain ⟨E,hE,hEc⟩ := hright
  obtain ⟨F,hF,hFc⟩ := glue_cut_sides S h hu hv hcross D E hD hE
  have hn : S.ncard+Sᶜ.ncard=Fintype.card V := by
    simpa only [Nat.card_eq_fintype_card] using S.ncard_add_ncard_compl
  have hb := augmented_budget S.ncard Sᶜ.ncard ho
  rw [hn] at hb
  exact ⟨F,hF,by omega⟩

/-- If every proper connected induced subgraph meets its own vertex budget,
a nontrivial single-edge cut in a failing graph has even order on both sides.
No assertion is made about leaf cuts (one side of order one). -/
lemma failed_minimal_cut_even {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hG : G.Connected)
    (hsmall : ∀ S : Set V, S.ncard < Fintype.card V → (G.induce S).Connected →
      ∃ D : Finset (G.induce S).Subgraph, GoodDecomposition (G.induce S) D ∧
        D.card ≤ ⌈(S.ncard : ℚ)/2⌉₊)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card V : ℚ)/2⌉₊)
    (S : Set V) {u v : V} (h : G.Adj u v) (hu : u ∈ S) (hv : v ∉ S)
    (hcross : ∀ x ∈ S, ∀ y ∉ S, G.Adj x y → x=u ∧ y=v)
    (hS : 2 ≤ S.ncard) (hcS : 2 ≤ Sᶜ.ncard) : Even S.ncard ∧ Even Sᶜ.ncard := by
  have hn : S.ncard+Sᶜ.ncard=Fintype.card V := by
    simpa only [Nat.card_eq_fintype_card] using S.ncard_add_ncard_compl
  have hleft := hsmall (insert v S) (by rw [Set.ncard_insert_of_notMem hv]; omega)
    (cut_side_connected hG S h hu hv hcross)
  have hcross' : ∀ x ∈ Sᶜ, ∀ y ∉ Sᶜ, G.Adj x y → x=v ∧ y=u := by
    intro x hx y hy hxy
    have hy' : y ∈ S := by simpa only [Set.mem_compl_iff,not_not] using hy
    exact (hcross y hy' x hx hxy.symm).symm
  have hright := hsmall (insert u Sᶜ)
    (by rw [Set.ncard_insert_of_notMem (show u ∉ Sᶜ from fun hh ↦ hh hu)]; omega)
    (cut_side_connected hG Sᶜ h.symm hv (fun hh ↦ hh hu) hcross')
  rw [Set.ncard_insert_of_notMem hv] at hleft
  rw [Set.ncard_insert_of_notMem (show u ∉ Sᶜ from fun hh ↦ hh hu)] at hright
  have hnot : ¬(Odd S.ncard ∨ Odd Sᶜ.ncard) := by
    intro ho
    exact hfail (gallai_of_cut_side_budgets S h hu hv hcross ho hleft hright)
  exact ⟨Nat.not_odd_iff_even.mp (fun hh ↦ hnot (Or.inl hh)),
    Nat.not_odd_iff_even.mp (fun hh ↦ hnot (Or.inr hh))⟩

lemma bridge_cut {V : Type*} {G : SimpleGraph V} {u v : V}
    (hb : G.IsBridge s(u,v)) :
    ∃ S : Set V, u ∈ S ∧ v ∉ S ∧
      ∀ x ∈ S, ∀ y ∉ S, G.Adj x y → x=u ∧ y=v := by
  have hb' := isBridge_iff.mp hb
  let J := G.deleteEdges {s(u,v)}
  let S : Set V := {x | J.Reachable u x}
  have hu : u ∈ S := Reachable.rfl
  have hv : v ∉ S := hb'.2
  refine ⟨S,hu,hv,?_⟩
  intro x hx y hy hxy
  have he : s(x,y)=s(u,v) := by
    by_contra hn
    have hJ : J.Adj x y := by
      change (G.deleteEdges {s(u,v)}).Adj x y
      simpa only [deleteEdges_adj,Set.mem_singleton_iff] using And.intro hxy hn
    exact hy (hx.trans hJ.reachable)
  rcases Sym2.eq_iff.mp he with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact ⟨rfl,rfl⟩
  · exact (hv hx).elim

lemma cut_singleton_degree {V : Type*} [Fintype V] {G : SimpleGraph V}
    (S : Set V) {u v : V} (h : G.Adj u v) (hu : u ∈ S)
    (hcross : ∀ x ∈ S, ∀ y ∉ S, G.Adj x y → x=u ∧ y=v)
    (hS : S.ncard=1) : Nat.card (G.neighborSet u)=1 := by
  have hsub : S.Subsingleton := Set.ncard_le_one_iff_subsingleton.mp (by omega)
  have heq : G.neighborSet u={v} := by
    ext x
    constructor
    · intro hx
      by_cases hxS : x ∈ S
      · exact (hx.ne (hsub hu hxS)).elim
      · exact (hcross u hu x hxS hx).2
    · rintro rfl
      exact h
  rw [Nat.card_coe_set_eq,heq,Set.ncard_singleton]

end Erdos583BridgeGlueDevelopment
