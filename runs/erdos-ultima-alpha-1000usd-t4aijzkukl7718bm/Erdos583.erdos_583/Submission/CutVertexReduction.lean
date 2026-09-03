import Submission.Work

/-! Gluing at a cut vertex in odd order.  Endpoint flexibility is obtained
from a strictly smaller one-leaf augmentation, not assumed for an arbitrary
optimal path decomposition.  Nil marked paths are deliberately allowed. -/
open SimpleGraph Erdos583Work
open Erdos583Work.BridgeGlue Erdos583Work.VertexCritical
open Erdos583Work.QuotaTrails Erdos583Work.PendantCompletion
namespace Erdos583CutVertexReductionDevelopment
open scoped Classical
set_option maxHeartbeats 1200000

lemma path_family_partition_tracked {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (hp : ∀ i, (T.walk i).IsPath) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ k ∧
      ∀ i, (T.walk i).toSubgraph ∈ D := by
  classical
  let D := Finset.univ.image (fun i ↦ (T.walk i).toSubgraph)
  refine ⟨D,⟨?_,?_,?_⟩,?_,fun i ↦ Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩
  · intro K hK
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hK
    exact ⟨_,_,_,hp i,rfl⟩
  · intro K hK L hL hKL
    change K ∈ D at hK
    change L ∈ D at hL
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hK
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hL
    exact T.disjoint (fun hij ↦ hKL (hij ▸ rfl))
  · ext e
    simp only [D,Set.mem_iUnion,Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨K,⟨i,rfl⟩,he⟩
      exact (T.cover e).mpr ⟨i,he⟩
    · intro he
      obtain ⟨i,hi⟩ := (T.cover e).mp he
      exact ⟨_,⟨i,rfl⟩,hi⟩
  · exact Finset.card_image_le.trans (by simp)

lemma project_leaf_family {V : Type*} {G : SimpleGraph V} {S : Set V} {k : ℕ}
    (T : TrailFamily (leafCompletion G S) k) (hp : ∀ i, (T.walk i).IsPath) :
    ∃ U : TrailFamily G k, (∀ i, (U.walk i).IsPath) ∧
      (∀ i, U.start i=root (T.start i)) ∧ (∀ i, U.finish i=root (T.finish i)) := by
  let U : TrailFamily G k := {
    start := fun i ↦ root (T.start i)
    finish := fun i ↦ root (T.finish i)
    walk := fun i ↦ projectWalk (T.walk i)
    isTrail := fun i ↦ (project_path_support _ (hp i)).1.isTrail
    disjoint := by
      intro i j hij
      apply Set.disjoint_left.mpr
      intro e hi hj
      exact Set.disjoint_left.mp (T.disjoint hij)
        ((project_edgeSet _ e).mp hi) ((project_edgeSet _ e).mp hj)
    cover := by
      intro e
      constructor
      · intro he
        obtain ⟨i,hi⟩ := (T.cover (Sym2.map Sum.inl e)).mp ((inclusion G S).map_mem_edgeSet he)
        exact ⟨i,(project_edgeSet _ e).mpr hi⟩
      · rintro ⟨i,hi⟩
        exact (projectWalk (T.walk i)).toSubgraph.edgeSet_subset hi }
  exact ⟨U,fun i ↦ (project_path_support _ (hp i)).1,fun _ ↦ rfl,fun _ ↦ rfl⟩

lemma project_single_leaf_marked {V : Type*} [Fintype V] {G : SimpleGraph V}
    (u : V) (D : Finset (leafCompletion G {u}).Subgraph)
    (hD : GoodDecomposition (leafCompletion G {u}) D) :
    ∃ E : Finset G.Subgraph, ∃ a, ∃ p : G.Walk u a,
      GoodDecomposition G E ∧ p.IsPath ∧ p.toSubgraph ∈ E ∧ E.card ≤ D.card := by
  classical
  let v : ↥({u} : Set V) := ⟨u,rfl⟩
  have hodd : Odd (Nat.card ((leafCompletion G {u}).neighborSet (Sum.inr v))) := by
    rw [leaf_neighbor_ncard]; exact odd_one
  obtain ⟨T,hT,i,hi⟩ := EdgeDefect.decomposition_odd_endpoint D hD (Sum.inr v) hodd
  obtain ⟨U,hU,hstart,hfinish⟩ := project_leaf_family T hT
  obtain ⟨E,hE,hEc,hparts⟩ := path_family_partition_tracked U hU
  have he : u=U.start i ∨ u=U.finish i := by
    rcases hi with hi|hi
    · exact Or.inl ((hstart i).trans (congrArg root hi.symm)).symm
    · exact Or.inr ((hfinish i).trans (congrArg root hi.symm)).symm
  rcases he with he|he
  · refine ⟨E,U.finish i,(U.walk i).copy he.symm rfl,hE,by simpa using hU i,?_,hEc⟩
    simpa only [NormalTrailSystem.walk_copy_subgraph] using hparts i
  · refine ⟨E,U.start i,(U.walk i).reverse.copy he.symm rfl,hE,by simpa using (hU i).reverse,?_,hEc⟩
    simpa only [NormalTrailSystem.walk_copy_subgraph,Walk.toSubgraph_reverse] using hparts i

lemma smaller_order_marked {n : ℕ} (hsmall : SmallerOrders n)
    {V : Type*} [Fintype V] (G : SimpleGraph V) (hG : G.Connected) (u : V)
    (hsize : Fintype.card V+1 < n) :
    ∃ D : Finset G.Subgraph, ∃ a, ∃ p : G.Walk u a,
      GoodDecomposition G D ∧ p.IsPath ∧ p.toSubgraph ∈ D ∧
        D.card ≤ ⌈((Fintype.card V+1 : ℕ) : ℚ)/2⌉₊ := by
  classical
  have hcard : Fintype.card (V ⊕ ↥({u} : Set V))=Fintype.card V+1 := by simp
  obtain ⟨D,hD,hDc⟩ := hsmall.on_finite (leafCompletion G {u}) (by simpa only [hcard] using hsize)
    (leafCompletion_connected hG {u})
  obtain ⟨E,a,p,hE,hp,hpE,hEc⟩ := project_single_leaf_marked u D hD
  exact ⟨E,a,p,hE,hp,hpE,hEc.trans (by simpa only [hcard] using hDc)⟩

lemma merge_disjoint_partitions {V : Type*} {G : SimpleGraph V}
    (D E : Finset G.Subgraph) (K L : G.Subgraph)
    (hpD : ∀ H ∈ D, IsPathSubgraph H) (hpE : ∀ H ∈ E, IsPathSubgraph H)
    (hdD : Set.PairwiseDisjoint (D : Set G.Subgraph) (fun H ↦ H.edgeSet))
    (hdE : Set.PairwiseDisjoint (E : Set G.Subgraph) (fun H ↦ H.edgeSet))
    (hK : K ∈ D) (hL : L ∈ E)
    (hcross : ∀ H ∈ D, ∀ J ∈ E, Disjoint H.edgeSet J.edgeSet)
    (hcover : (⋃ H ∈ D, H.edgeSet) ∪ (⋃ H ∈ E, H.edgeSet)=G.edgeSet)
    (hp : IsPathSubgraph (K ⊔ L)) :
    ∃ F : Finset G.Subgraph, GoodDecomposition G F ∧ F.card+1 ≤ D.card+E.card := by
  classical
  let R := D.erase K ∪ E.erase L
  let F := insert (K ⊔ L) R
  have hrest {H : G.Subgraph} (hH : H ∈ R) : Disjoint (K ⊔ L).edgeSet H.edgeSet := by
    rw [Subgraph.edgeSet_sup]
    apply disjoint_sup_left.mpr
    rcases Finset.mem_union.mp hH with hHD | hHE
    · obtain ⟨hHK,hHD⟩ := Finset.mem_erase.mp hHD
      exact ⟨hdD hK hHD hHK.symm,(hcross H hHD L hL).symm⟩
    · obtain ⟨hHL,hHE⟩ := Finset.mem_erase.mp hHE
      exact ⟨hcross K hK H hHE,hdE hL hHE hHL.symm⟩
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
      · exact hcross H (Finset.mem_of_mem_erase hHD) J (Finset.mem_of_mem_erase hJE)
      · exact (hcross J (Finset.mem_of_mem_erase hJD) H (Finset.mem_of_mem_erase hHE)).symm
      · exact hdE (Finset.mem_of_mem_erase hHE) (Finset.mem_of_mem_erase hJE) hHJ
  · ext e
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨H,_,he⟩
      exact H.edgeSet_subset he
    · intro he
      rw [←hcover] at he
      simp only [Set.mem_union,Set.mem_iUnion] at he
      rcases he with ⟨H,hH,he⟩ | ⟨H,hH,he⟩
      · by_cases heq : H=K
        · subst H
          exact ⟨K ⊔ L,Finset.mem_insert_self _ _,by rw [Subgraph.edgeSet_sup]; exact Or.inl he⟩
        · exact ⟨H,Finset.mem_insert_of_mem (Finset.mem_union_left _
            (Finset.mem_erase.mpr ⟨heq,hH⟩)),he⟩
      · by_cases heq : H=L
        · subst H
          exact ⟨K ⊔ L,Finset.mem_insert_self _ _,by rw [Subgraph.edgeSet_sup]; exact Or.inr he⟩
        · exact ⟨H,Finset.mem_insert_of_mem (Finset.mem_union_right _
            (Finset.mem_erase.mpr ⟨heq,hH⟩)),he⟩
  · have hc : F.card ≤ (D.erase K).card+(E.erase L).card+1 :=
      (Finset.card_insert_le _ _).trans (by have := Finset.card_union_le (D.erase K) (E.erase L); dsimp [R]; omega)
    have hk := Finset.card_erase_add_one hK
    have hl := Finset.card_erase_add_one hL
    omega


lemma partial_induce {V : Type*} {G : SimpleGraph V} (S : Set V)
    (D : Finset (G.induce S).Subgraph) (hD : GoodDecomposition (G.induce S) D) :
    let E := D.image (Subgraph.map (Embedding.induce S).toHom)
    (∀ H ∈ E, IsPathSubgraph H) ∧
      Set.PairwiseDisjoint (E : Set G.Subgraph) (fun H ↦ H.edgeSet) ∧
      (⋃ H ∈ E, H.edgeSet)=(within G S).edgeSet := by
  classical
  dsimp only
  refine ⟨?_,?_,?_⟩
  · intro L hL
    obtain ⟨K,hK,rfl⟩ := Finset.mem_image.mp hL
    obtain ⟨a,b,p,hp,rfl⟩ := hD.1 K hK
    exact ⟨a.val,b.val,p.map (Embedding.induce S).toHom,
      Walk.map_isPath_of_injective Subtype.val_injective hp,by simp⟩
  · intro L hL M hM hLM
    obtain ⟨K,hK,rfl⟩ := Finset.mem_image.mp hL
    obtain ⟨J,hJ,rfl⟩ := Finset.mem_image.mp hM
    change Disjoint (K.map (Embedding.induce S).toHom).edgeSet (J.map (Embedding.induce S).toHom).edgeSet
    rw [Subgraph.edgeSet_map,Subgraph.edgeSet_map,Set.disjoint_image_iff
      (Sym2.map.injective (show Function.Injective (Embedding.induce S).toHom from Subtype.val_injective))]
    exact hD.2.1 hK hJ (fun h ↦ hLM (congrArg (Subgraph.map (Embedding.induce S).toHom) h))
  · ext e
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨L,hL,he⟩
      obtain ⟨K,hK,rfl⟩ := Finset.mem_image.mp hL
      rw [Subgraph.edgeSet_map] at he
      obtain ⟨e,he,rfl⟩ := he
      have heG := K.edgeSet_subset he
      induction e using Sym2.ind with
      | h x y => exact ⟨heG,x.property,y.property⟩
    · intro he
      induction e using Sym2.ind with
      | h x y =>
        let e : Sym2 S := s(⟨x,he.2.1⟩,⟨y,he.2.2⟩)
        have heG : e ∈ (G.induce S).edgeSet := he.1
        rw [←hD.2.2] at heG
        simp only [Set.mem_iUnion] at heG
        obtain ⟨K,hK,heK⟩ := heG
        refine ⟨K.map (Embedding.induce S).toHom,Finset.mem_image.mpr ⟨K,hK,rfl⟩,?_⟩
        rw [Subgraph.edgeSet_map]
        exact ⟨e,heK,rfl⟩

lemma within_edge_disjoint {V : Type*} (G : SimpleGraph V) (S T : Set V) (u : V)
    (hinter : S ∩ T ⊆ {u}) : Disjoint (within G S).edgeSet (within G T).edgeSet := by
  apply Set.disjoint_left.mpr
  intro e he hf
  induction e using Sym2.ind with
  | h x y =>
    have hx : x=u := hinter ⟨he.2.1,hf.2.1⟩
    have hy : y=u := hinter ⟨he.2.2,hf.2.2⟩
    exact he.1.ne (hx.trans hy.symm)

lemma union_disjoint_partitions {V : Type*} {G : SimpleGraph V}
    (D E : Finset G.Subgraph)
    (hpD : ∀ H ∈ D, IsPathSubgraph H) (hpE : ∀ H ∈ E, IsPathSubgraph H)
    (hdD : Set.PairwiseDisjoint (D : Set G.Subgraph) (fun H ↦ H.edgeSet))
    (hdE : Set.PairwiseDisjoint (E : Set G.Subgraph) (fun H ↦ H.edgeSet))
    (hcross : ∀ H ∈ D, ∀ J ∈ E, Disjoint H.edgeSet J.edgeSet)
    (hcover : (⋃ H ∈ D, H.edgeSet) ∪ (⋃ H ∈ E, H.edgeSet)=G.edgeSet) :
    ∃ F : Finset G.Subgraph, GoodDecomposition G F ∧ F.card ≤ D.card+E.card := by
  classical
  refine ⟨D ∪ E,⟨?_,?_,?_⟩,Finset.card_union_le _ _⟩
  · intro H hH
    rcases Finset.mem_union.mp hH with hH|hH
    · exact hpD H hH
    · exact hpE H hH
  · intro H hH J hJ hHJ
    rcases Finset.mem_union.mp hH with hH|hH <;> rcases Finset.mem_union.mp hJ with hJ|hJ
    · exact hdD hH hJ hHJ
    · exact hcross H hH J hJ
    · exact (hcross J hJ H hH).symm
    · exact hdE hH hJ hHJ
  · simpa only [Finset.mem_union,Set.iUnion_or,Set.iUnion_union_distrib] using hcover

lemma union_induced_sides {V : Type*} {G : SimpleGraph V} (S T : Set V) (u : V)
    (hinter : S ∩ T ⊆ {u})
    (hcover : (within G S).edgeSet ∪ (within G T).edgeSet=G.edgeSet)
    (D : Finset (G.induce S).Subgraph) (E : Finset (G.induce T).Subgraph)
    (hD : GoodDecomposition (G.induce S) D) (hE : GoodDecomposition (G.induce T) E) :
    ∃ F : Finset G.Subgraph, GoodDecomposition G F ∧ F.card ≤ D.card+E.card := by
  classical
  obtain ⟨hpD,hdD,hcoverD⟩ := partial_induce S D hD
  obtain ⟨hpE,hdE,hcoverE⟩ := partial_induce T E hE
  have hdis := within_edge_disjoint G S T u hinter
  have hcross (H : G.Subgraph) (hH : H ∈ D.image (Subgraph.map (Embedding.induce S).toHom))
      (J : G.Subgraph) (hJ : J ∈ E.image (Subgraph.map (Embedding.induce T).toHom)) :
      Disjoint H.edgeSet J.edgeSet := hdis.mono
    (fun _ he ↦ hcoverD ▸ Set.mem_iUnion.mpr ⟨H,Set.mem_iUnion.mpr ⟨hH,he⟩⟩)
    (fun _ he ↦ hcoverE ▸ Set.mem_iUnion.mpr ⟨J,Set.mem_iUnion.mpr ⟨hJ,he⟩⟩)
  obtain ⟨F,hF,hFc⟩ := union_disjoint_partitions _ _ hpD hpE hdD hdE hcross
    (by rw [hcoverD,hcoverE]; exact hcover)
  exact ⟨F,hF,hFc.trans (Nat.add_le_add Finset.card_image_le Finset.card_image_le)⟩

lemma glue_induced_sides {V : Type*} {G : SimpleGraph V} (S T : Set V) (u : V)
    (huS : u ∈ S) (huT : u ∈ T) (hinter : S ∩ T ⊆ {u})
    (hcover : (within G S).edgeSet ∪ (within G T).edgeSet=G.edgeSet)
    (D : Finset (G.induce S).Subgraph) (E : Finset (G.induce T).Subgraph)
    (hD : GoodDecomposition (G.induce S) D) (hE : GoodDecomposition (G.induce T) E)
    {a : S} {b : T} (p : (G.induce S).Walk ⟨u,huS⟩ a) (q : (G.induce T).Walk ⟨u,huT⟩ b)
    (hp : p.IsPath) (hq : q.IsPath) (hpD : p.toSubgraph ∈ D) (hqE : q.toSubgraph ∈ E) :
    ∃ F : Finset G.Subgraph, GoodDecomposition G F ∧ F.card+1 ≤ D.card+E.card := by
  classical
  obtain ⟨hpathsD,hdD,hcoverD⟩ := partial_induce S D hD
  obtain ⟨hpathsE,hdE,hcoverE⟩ := partial_induce T E hE
  have hdis := within_edge_disjoint G S T u hinter
  have hcross (H : G.Subgraph) (hH : H ∈ D.image (Subgraph.map (Embedding.induce S).toHom))
      (J : G.Subgraph) (hJ : J ∈ E.image (Subgraph.map (Embedding.induce T).toHom)) :
      Disjoint H.edgeSet J.edgeSet := hdis.mono
    (fun _ he ↦ hcoverD ▸ Set.mem_iUnion.mpr ⟨H,Set.mem_iUnion.mpr ⟨hH,he⟩⟩)
    (fun _ he ↦ hcoverE ▸ Set.mem_iUnion.mpr ⟨J,Set.mem_iUnion.mpr ⟨hJ,he⟩⟩)
  let p' := p.map (Embedding.induce S).toHom
  let q' := q.map (Embedding.induce T).toHom
  have hpp : p'.IsPath := Walk.map_isPath_of_injective Subtype.val_injective hp
  have hqq : q'.IsPath := Walk.map_isPath_of_injective Subtype.val_injective hq
  have hpath : IsPathSubgraph (p'.toSubgraph ⊔ q'.toSubgraph) := by
    refine ⟨a.val,b.val,p'.reverse.append q',?_,by simp⟩
    apply path_append_of_support_intersection hpp.reverse hqq
    intro x hx hy
    have hxS : x ∈ S := by
      simp only [p',Walk.support_reverse,List.mem_reverse,Walk.support_map,List.mem_map] at hx
      obtain ⟨y,_,rfl⟩ := hx
      exact y.property
    have hxT : x ∈ T := by
      simp only [q',Walk.support_map,List.mem_map] at hy
      obtain ⟨y,_,rfl⟩ := hy
      exact y.property
    exact hinter ⟨hxS,hxT⟩
  have hpm : p'.toSubgraph ∈ D.image (Subgraph.map (Embedding.induce S).toHom) := by
    exact Finset.mem_image.mpr ⟨p.toSubgraph,hpD,by simp [p']⟩
  have hqm : q'.toSubgraph ∈ E.image (Subgraph.map (Embedding.induce T).toHom) := by
    exact Finset.mem_image.mpr ⟨q.toSubgraph,hqE,by simp [q']⟩
  obtain ⟨F,hF,hFc⟩ := merge_disjoint_partitions _ _ p'.toSubgraph q'.toSubgraph
    hpathsD hpathsE hdD hdE hpm hqm hcross (by rw [hcoverD,hcoverE]; exact hcover) hpath
  exact ⟨F,hF,hFc.trans (Nat.add_le_add Finset.card_image_le Finset.card_image_le)⟩


lemma single_boundary_connected {V : Type*} {G : SimpleGraph V} (hG : G.Connected)
    (S : Set V) (u : V) (hu : u ∈ S)
    (hcross : ∀ x ∈ S, ∀ y ∉ S, G.Adj x y → x=u) : (G.induce S).Connected := by
  classical
  let f : V → S := fun x ↦ if hx : x ∈ S then ⟨x,hx⟩ else ⟨u,hu⟩
  have hf (x y : V) (hxy : G.Adj x y) : (G.induce S).Reachable (f x) (f y) := by
    by_cases hx : x ∈ S <;> by_cases hy : y ∈ S
    · apply Adj.reachable
      simpa only [f,dif_pos hx,dif_pos hy] using hxy
    · obtain rfl := hcross x hx y hy hxy
      simp only [f,dif_pos hu,dif_neg hy]
      exact Reachable.rfl
    · obtain rfl := hcross y hy x hx hxy.symm
      simp only [f,dif_neg hx,dif_pos hu]
      exact Reachable.rfl
    · simp only [f,dif_neg hx,dif_neg hy]
      exact Reachable.rfl
  have hfx (x : S) : f x.val=x := by
    apply Subtype.ext
    simp [f,x.property]
  letI : Nonempty S := ⟨⟨u,hu⟩⟩
  refine ⟨fun x y ↦ ?_⟩
  have hh := reachable_map_to_reachable f hf (hG.preconnected x.val y.val)
  simpa only [hfx] using hh

lemma opposite_single_boundary {V : Type*} {G : SimpleGraph V} (S : Set V) (u : V)
    (hcross : ∀ x ∈ S, ∀ y ∉ S, G.Adj x y → x=u) :
    ∀ x ∈ insert u Sᶜ, ∀ y ∉ insert u Sᶜ, G.Adj x y → x=u := by
  intro x hx y hy hxy
  rcases hx with hx|hx
  · exact hx
  have hyS : y ∈ S := by
    by_contra hn
    exact hy (Or.inr hn)
  have he := hcross y hyS x hx hxy.symm
  exact (hy (Or.inl he)).elim

lemma single_boundary_cover {V : Type*} {G : SimpleGraph V} (S : Set V) (u : V)
    (hcross : ∀ x ∈ S, ∀ y ∉ S, G.Adj x y → x=u) :
    (within G S).edgeSet ∪ (within G (insert u Sᶜ)).edgeSet=G.edgeSet := by
  ext e
  constructor
  · rintro (he|he)
    · exact edgeSet_mono (within_le _ _) he
    · exact edgeSet_mono (within_le _ _) he
  · intro he
    induction e using Sym2.ind with
    | h x y =>
      by_cases hx : x ∈ S <;> by_cases hy : y ∈ S
      · exact Or.inl ⟨he,hx,hy⟩
      · exact Or.inr ⟨he,Or.inl (hcross x hx y hy he),Or.inr hy⟩
      · exact Or.inr ⟨he,Or.inr hx,Or.inl (hcross y hy x hx he.symm)⟩
      · exact Or.inr ⟨he,Or.inr hx,Or.inr hy⟩

lemma single_boundary_budget {n : ℕ} (hsmall : SmallerOrders n) (hn : Odd n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected) (S : Set (Fin n)) (u : Fin n)
    (hu : u ∈ S) (hcross : ∀ x ∈ S, ∀ y ∉ S, G.Adj x y → x=u)
    (hS : 2 ≤ S.ncard) (hcomp : 0 < Sᶜ.ncard) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ := by
  classical
  let T : Set (Fin n) := insert u Sᶜ
  have huT : u ∈ T := Or.inl rfl
  have hinter : S ∩ T ⊆ {u} := by
    rintro x ⟨hx,hT⟩
    rcases hT with hxu|hxc
    · exact hxu
    · exact (hxc hx).elim
  have hconnS := single_boundary_connected hG S u hu hcross
  have hconnT := single_boundary_connected hG T u huT (opposite_single_boundary S u hcross)
  have hcover := single_boundary_cover S u hcross
  have hcT : T.ncard=Sᶜ.ncard+1 := Set.ncard_insert_of_notMem (not_not.mpr hu)
  have hsum : S.ncard+T.ncard=n+1 := by
    rw [hcT,Set.ncard_compl,Nat.card_eq_fintype_card,Fintype.card_fin]
    have hb : S.ncard ≤ n := by simpa only [Nat.card_eq_fintype_card,Fintype.card_fin] using Set.ncard_le_card S
    omega
  have hcardS : Fintype.card S=S.ncard := by rw [←Nat.card_eq_fintype_card,Nat.card_coe_set_eq]
  have hcardT : Fintype.card T=T.ncard := by rw [←Nat.card_eq_fintype_card,Nat.card_coe_set_eq]
  have hT : 2 ≤ T.ncard := by omega
  obtain ⟨k,hk⟩ := hn
  by_cases heS : Even S.ncard
  · obtain ⟨a,ha⟩ := heS
    have heT : Even T.ncard := by apply Nat.even_iff.mpr; omega
    obtain ⟨b,hb⟩ := heT
    obtain ⟨D,hD,hDc⟩ := hsmall.on_induce G S (by omega) hconnS
    obtain ⟨E,hE,hEc⟩ := hsmall.on_induce G T (by omega) hconnT
    obtain ⟨F,hF,hFc⟩ := union_induced_sides S T u hinter hcover D E hD hE
    rw [ceil_half] at hDc hEc
    exact ⟨F,hF,by simp only [Fintype.card_fin,ceil_half]; omega⟩
  · have hoS : Odd S.ncard := Nat.not_even_iff_odd.mp heS
    obtain ⟨a,ha⟩ := hoS
    have hoT : Odd T.ncard := by apply Nat.odd_iff.mpr; omega
    obtain ⟨b,hb⟩ := hoT
    obtain ⟨D,x,p,hD,hp,hpD,hDc⟩ := smaller_order_marked hsmall (G.induce S) hconnS ⟨u,hu⟩
      (by rw [hcardS]; omega)
    obtain ⟨E,y,q,hE,hq,hqE,hEc⟩ := smaller_order_marked hsmall (G.induce T) hconnT ⟨u,huT⟩
      (by rw [hcardT]; omega)
    obtain ⟨F,hF,hFc⟩ := glue_induced_sides S T u hu huT hinter hcover D E hD hE p q hp hq hpD hqE
    rw [hcardS,ceil_half] at hDc
    rw [hcardT,ceil_half] at hEc
    exact ⟨F,hF,by simp only [Fintype.card_fin,ceil_half]; omega⟩

lemma delete_vertex_connected_of_odd_failure {n : ℕ} (hsmall : SmallerOrders n) (hn : Odd n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊) (u : Fin n) :
    (G.induce ({u}ᶜ : Set (Fin n))).Connected := by
  classical
  by_contra hconn
  have hdeg := DegreeTwoReduction.min_degree_of_odd_failure hsmall hn hG hfail u
  obtain ⟨a,ha⟩ := (Set.ncard_pos (Set.toFinite _)).mp
    (show 0 < (G.neighborSet u).ncard by rw [←Nat.card_coe_set_eq]; omega)
  obtain ⟨b,hb,hnon⟩ : ∃ b, G.Adj u b ∧ ¬(within G ({u}ᶜ : Set (Fin n))).Reachable a b := by
    by_contra! hh
    exact hconn (DegreeThreeReduction.delete_vertex_connected_of_neighbor_links hG ha hh)
  let S : Set (Fin n) := {x | x=u ∨ (within G ({u}ᶜ : Set (Fin n))).Reachable a x}
  have hu : u ∈ S := Or.inl rfl
  have haS : a ∈ S := Or.inr Reachable.rfl
  have hbS : b ∉ S := by
    rintro (hbu|hr)
    · exact hb.ne hbu.symm
    · exact hnon hr
  have hsize : 2 ≤ S.ncard := by
    have hh : ({u,a} : Set (Fin n)) ⊆ S := by rintro x (rfl|rfl) <;> assumption
    have hc := Set.ncard_mono hh
    rw [Set.ncard_pair ha.ne] at hc
    exact hc
  have hcsize : 0 < Sᶜ.ncard := (Set.ncard_pos (Set.toFinite _)).mpr ⟨b,hbS⟩
  apply hfail
  apply single_boundary_budget hsmall hn hG S u hu _ hsize hcsize
  intro x hx y hy hxy
  rcases hx with hxu|hr
  · exact hxu
  by_contra hxu
  have hyu : y ≠ u := fun he ↦ hy (Or.inl he)
  exact hy (Or.inr (hr.trans (show (within G ({u}ᶜ : Set (Fin n))).Adj x y from ⟨hxy,hxu,hyu⟩).reachable))

end Erdos583CutVertexReductionDevelopment
