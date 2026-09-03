import Submission.Euler
import Submission.CycleRank

/-! Projecting cycles through a homomorphism injective on edges. -/
open SimpleGraph
open scoped Classical
namespace Erdos184

lemma eulerian_map_of_edge_bijective {V W : Type*} {G : SimpleGraph V}
    {K : SimpleGraph W} (f : G →g K)
    (hi : Set.InjOn (Sym2.map f) G.edgeSet)
    (hs : Set.SurjOn (Sym2.map f) G.edgeSet K.edgeSet)
    {u v : V} (p : G.Walk u v) (hp : p.IsEulerian) : (p.map f).IsEulerian := by
  have ht : (p.map f).IsTrail := by
    rw [Walk.isTrail_def, Walk.edges_map]
    exact List.Nodup.map_on (fun e he d hd hed =>
      hi (p.edges_subset_edgeSet he) (p.edges_subset_edgeSet hd) hed) hp.isTrail.edges_nodup
  apply ht.isEulerian_of_forall_mem
  intro e he
  obtain ⟨d, hd, rfl⟩ := hs he
  rw [Walk.edges_map]
  exact List.mem_map.mpr ⟨d, hp.mem_edges_iff.mpr hd, rfl⟩

/-- The canonical surjection from a subgraph to its image under a graph homomorphism. -/
def subgraphImageHom {V W : Type*} {G : SimpleGraph V} {K : SimpleGraph W}
    (f : G →g K) (H : G.Subgraph) : H.coe →g (H.map f).coe where
  toFun x := ⟨f x.val, Set.mem_image_of_mem _ x.property⟩
  map_rel' {x y} h := ⟨x.val, y.val, h, rfl, rfl⟩

lemma subgraphImageHom_surjective {V W : Type*} {G : SimpleGraph V} {K : SimpleGraph W}
    (f : G →g K) (H : G.Subgraph) : Function.Surjective (subgraphImageHom f H) := by
  rintro ⟨y, x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, rfl⟩

lemma subgraphImageHom_edge_bijective {V W : Type*} {G : SimpleGraph V}
    {K : SimpleGraph W} (f : G →g K) (hi : Set.InjOn (Sym2.map f) G.edgeSet)
    (H : G.Subgraph) :
    Set.InjOn (Sym2.map (subgraphImageHom f H)) H.coe.edgeSet ∧
      Set.SurjOn (Sym2.map (subgraphImageHom f H)) H.coe.edgeSet (H.map f).coe.edgeSet := by
  have hcomm (e : Sym2 H.verts) :
      Sym2.map (Subtype.val : (H.map f).verts → W)
          (Sym2.map (subgraphImageHom f H) e) =
        Sym2.map f (Sym2.map (Subtype.val : H.verts → V) e) := by
    simp only [Sym2.map_map]
    rfl
  constructor
  · intro e he d hd hed
    apply Sym2.map.injective Subtype.val_injective
    apply hi (H.hom.map_mem_edgeSet he) (H.hom.map_mem_edgeSet hd)
    have hh := congrArg (Sym2.map (Subtype.val : (H.map f).verts → W)) hed
    simpa only [hcomm] using hh
  · intro e he
    have he' : Sym2.map (Subtype.val : (H.map f).verts → W) e ∈ (H.map f).edgeSet := by
      simpa only [Subgraph.edgeSet_coe, Set.mem_preimage] using he
    rw [Subgraph.edgeSet_map] at he'
    obtain ⟨d, hd, hde⟩ := he'
    rw [← H.image_coe_edgeSet_coe] at hd
    obtain ⟨b, hb, hbd⟩ := hd
    refine ⟨b, hb, ?_⟩
    apply Sym2.map.injective Subtype.val_injective
    rw [hcomm, hbd, hde]

lemma subgraph_image_connected_even {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {K : SimpleGraph W} (f : G →g K)
    (hi : Set.InjOn (Sym2.map f) G.edgeSet) (H : G.Subgraph)
    (hc : H.coe.Connected) (he : ∀ v, Even (H.coe.degree v)) :
    (H.map f).coe.Connected ∧ ∀ v, Even ((H.map f).coe.degree v) := by
  refine ⟨hc.map (subgraphImageHom f H) (subgraphImageHom_surjective f H), ?_⟩
  obtain ⟨u, p, hp⟩ := exists_eulerian_closed_walk H.coe hc (by
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using he)
  letI : DecidableEq (H.map f).verts := Classical.decEq _
  have hb := subgraphImageHom_edge_bijective f hi H
  have hq := eulerian_map_of_edge_bijective (subgraphImageHom f H) hb.1 hb.2 p hp
  intro v
  have hev := (hq.even_degree_iff (x := v)).mpr (by simp)
  simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using hev

lemma regular_two_edge_vertex_card {V : Type*} [Fintype V] {G : SimpleGraph V}
    (H : G.Subgraph) (hr : H.coe.IsRegularOfDegree 2) : H.edgeSet.ncard = H.verts.ncard := by
  have hs := H.coe.sum_degrees_eq_twice_card_edges
  have hdeg (v : H.verts) : Nat.card (H.coe.neighborSet v) = 2 := by
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using hr v
  have hedge := coe_edgeFinset_card G H
  simp only [← SimpleGraph.card_neighborSet_eq_degree, SimpleGraph.edgeFinset_card,
    ← Nat.card_eq_fintype_card] at hs hedge
  simp only [hdeg, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, hedge] at hs
  omega

lemma projected_cycle_decomposition_rank_bound {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {K : SimpleGraph W} (f : G →g K)
    (hi : Set.InjOn (Sym2.map f) G.edgeSet) (H : G.Subgraph)
    (hc : H.coe.Connected) (hr : H.coe.IsRegularOfDegree 2) :
    ∃ E : Finset (H.map f).coe.Subgraph,
      (∀ A ∈ E, A.coe.Connected ∧ A.coe.IsRegularOfDegree 2) ∧
      IsDecomposition (H.map f).coe E ∧
      E.card + (H.map f).verts.ncard ≤ H.verts.ncard + 1 := by
  have he : ∀ v, Even (H.coe.degree v) := fun v => by rw [hr v]; decide
  obtain ⟨hconn, heven⟩ := subgraph_image_connected_even f hi H hc he
  obtain ⟨E, hcy, hd⟩ := even_cycle_decomposition (H.map f).coe (by
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using heven)
  refine ⟨E, ?_, hd, ?_⟩
  · intro A hA
    refine ⟨(hcy A hA).1, ?_⟩
    intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using (hcy A hA).2 v
  · have hb := connected_cycle_decomposition_rank_bound (H.map f).coe hconn E hcy hd
    have heq : (H.map f).edgeSet.ncard = H.edgeSet.ncard := by
      rw [Subgraph.edgeSet_map]
      exact Set.ncard_image_of_injOn (hi.mono H.edgeSet_subset)
    rw [coe_edgeFinset_card, heq, regular_two_edge_vertex_card H hr] at hb
    simpa only [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq] using hb

/-- With an injective vertex map, the canonical map onto the image is an isomorphism. -/
noncomputable def subgraphImageIso {V W : Type*} {G : SimpleGraph V} {K : SimpleGraph W}
    (f : G →g K) (hf : Function.Injective f) (H : G.Subgraph) :
    H.coe ≃g (H.map f).coe where
  toEquiv := Equiv.ofBijective (subgraphImageHom f H) ⟨by
    intro x y h
    exact Subtype.ext (hf (congrArg Subtype.val h)), subgraphImageHom_surjective f H⟩
  map_rel_iff' {a b} := by
    change (∃ x y, H.Adj x y ∧ f x = f a.val ∧ f y = f b.val) ↔ H.Adj a.val b.val
    constructor
    · rintro ⟨x, y, hxy, hx, hy⟩
      have hx' := hf hx
      have hy' := hf hy
      simpa only [hx', hy'] using hxy
    · intro hab
      exact ⟨a.val, b.val, hab, rfl, rfl⟩

lemma regular_two_of_iso {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {K : SimpleGraph W} (e : G ≃g K)
    (hr : G.IsRegularOfDegree 2) : K.IsRegularOfDegree 2 := by
  intro w
  have hc := Nat.card_congr (e.symm.mapNeighborSet w)
  have hw := hr (e.symm w)
  simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card, hc] using hw

lemma subgraph_image_cycle_of_injective {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {K : SimpleGraph W} (f : G →g K) (hf : Function.Injective f)
    (H : G.Subgraph) (hc : H.coe.Connected) (hr : H.coe.IsRegularOfDegree 2) :
    (H.map f).coe.Connected ∧ (H.map f).coe.IsRegularOfDegree 2 := by
  refine ⟨hc.map (subgraphImageHom f H) (subgraphImageHom_surjective f H), ?_⟩
  have h := regular_two_of_iso (subgraphImageIso f hf H) (by
    intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using hr v)
  intro v
  simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using h v

lemma lift_cycle_decomposition {V : Type*} [Fintype V] {G : SimpleGraph V}
    (H : G.Subgraph) (E : Finset H.coe.Subgraph)
    (hc : ∀ A ∈ E, A.coe.Connected ∧ A.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition H.coe E) :
    ∃ F : Finset G.Subgraph,
      (∀ A ∈ F, A.coe.Connected ∧ A.coe.IsRegularOfDegree 2) ∧
      Set.PairwiseDisjoint (F : Set G.Subgraph) (fun A => A.edgeSet) ∧
      (⋃ A ∈ F, A.edgeSet) = H.edgeSet ∧ F.card ≤ E.card := by
  let F : Finset G.Subgraph := E.image (Subgraph.coeSubgraph (G' := H))
  refine ⟨F, ?_, ?_, ?_, Finset.card_image_le⟩
  · intro A hA
    obtain ⟨X, hX, rfl⟩ := Finset.mem_image.mp hA
    have hh := subgraph_image_cycle_of_injective H.hom H.hom_injective X (hc X hX).1 (by
      intro v
      simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
        using (hc X hX).2 v)
    refine ⟨hh.1, ?_⟩
    intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using hh.2 v
  · intro A hA B hB hAB
    obtain ⟨X, hX, rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨Y, hY, rfl⟩ := Finset.mem_image.mp hB
    have hd' := hd.1 hX hY (fun h => hAB (congrArg Subgraph.coeSubgraph h))
    change Disjoint (X.map H.hom).edgeSet (Y.map H.hom).edgeSet
    rw [Subgraph.edgeSet_map, Subgraph.edgeSet_map]
    exact Set.disjoint_image_of_injective (Sym2.map.injective H.hom_injective) hd'
  · ext e
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨A, hA, he⟩
      obtain ⟨X, hX, rfl⟩ := Finset.mem_image.mp hA
      exact Subgraph.edgeSet_mono (Subgraph.coeSubgraph_le X) he
    · intro he
      rw [← H.image_coe_edgeSet_coe, ← hd.2] at he
      obtain ⟨d, hd, rfl⟩ := he
      simp only [Set.mem_iUnion] at hd
      obtain ⟨A, hA, hd⟩ := hd
      refine ⟨Subgraph.coeSubgraph A, Finset.mem_image.mpr ⟨A, hA, rfl⟩, ?_⟩
      change Sym2.map H.hom d ∈ (A.map H.hom).edgeSet
      rw [Subgraph.edgeSet_map]
      exact Set.mem_image_of_mem _ hd

lemma card_le_image_add_exceptional {V W : Type*} [Finite V] [Finite W]
    (f : V → W) (B S : Set V) (hi : Set.InjOn f Bᶜ) :
    S.ncard ≤ (f '' S).ncard + (S ∩ B).ncard := by
  have heq : S = (S \ B) ∪ (S ∩ B) := by ext x; simp
  have hdis : Disjoint (S \ B) (S ∩ B) := by
    apply Set.disjoint_left.mpr
    exact fun _ hx hy => hx.2 hy.2
  have hc : (S \ B).ncard ≤ (f '' S).ncard := by
    rw [← Set.ncard_image_of_injOn (hi.mono (show S \ B ⊆ Bᶜ from fun _ h => h.2))]
    exact Set.ncard_le_ncard (Set.image_mono Set.diff_subset)
  have hcard := Set.ncard_union_eq hdis
  rw [← heq] at hcard
  omega

lemma projected_cycle_decomposition_exceptional_bound {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {K : SimpleGraph W} (f : G →g K)
    (hi : Set.InjOn (Sym2.map f) G.edgeSet) (B : Set V) (hB : Set.InjOn f Bᶜ)
    (H : G.Subgraph) (hc : H.coe.Connected) (hr : H.coe.IsRegularOfDegree 2) :
    ∃ F : Finset K.Subgraph,
      (∀ A ∈ F, A.coe.Connected ∧ A.coe.IsRegularOfDegree 2) ∧
      Set.PairwiseDisjoint (F : Set K.Subgraph) (fun A => A.edgeSet) ∧
      (⋃ A ∈ F, A.edgeSet) = (H.map f).edgeSet ∧
      F.card ≤ 1 + (H.verts ∩ B).ncard := by
  obtain ⟨E, hcy, hd, hcard⟩ := projected_cycle_decomposition_rank_bound f hi H hc hr
  obtain ⟨F, hcF, hdF, heF, hbF⟩ := lift_cycle_decomposition (H.map f) E (by
    intro A hA
    refine ⟨(hcy A hA).1, ?_⟩
    intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using (hcy A hA).2 v) hd
  refine ⟨F, ?_, hdF, heF, ?_⟩
  · intro A hA
    refine ⟨(hcF A hA).1, ?_⟩
    intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using (hcF A hA).2 v
  · have hbound := card_le_image_add_exceptional f B H.verts hB
    change E.card + (f '' H.verts).ncard ≤ _ at hcard
    omega

lemma cycle_decomposition_exceptional_incidence {V : Type*} [Fintype V]
    (G : SimpleGraph V) (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D) (B : Set V) (hB : ∀ v ∈ B, G.degree v = 2) :
    ∑ H ∈ D, (H.verts ∩ B).ncard = B.ncard := by
  have hvert : ∀ v ∈ B, (D.filter (fun H => v ∈ H.verts)).card = 1 := by
    intro v hv
    have hh := cycle_decomposition_vertex_count G D hc hd v
    have hv' := hB v hv
    simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hh hv'
    omega
  have hcard (H : G.Subgraph) :
      (H.verts ∩ B).ncard = ∑ v ∈ B.toFinset, if v ∈ H.verts then 1 else 0 := by
    rw [← Finset.card_filter]
    have hs : B.toFinset.filter (fun v => v ∈ H.verts) = (H.verts ∩ B).toFinset := by
      ext v
      simp [and_comm]
    rw [hs, Set.ncard_eq_toFinset_card']
  calc
    _ = ∑ H ∈ D, ∑ v ∈ B.toFinset, if v ∈ H.verts then 1 else 0 :=
      Finset.sum_congr rfl (fun H _ => hcard H)
    _ = ∑ v ∈ B.toFinset, ∑ H ∈ D, if v ∈ H.verts then 1 else 0 := Finset.sum_comm
    _ = ∑ v ∈ B.toFinset, 1 := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [← Finset.card_filter, hvert v (Set.mem_toFinset.mp hv)]
    _ = B.ncard := by simp [Set.ncard_eq_toFinset_card']

/-- Identifying exceptional degree-two vertices costs at most one extra cycle per vertex. -/
lemma project_decomposition_degree_two {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {K : SimpleGraph W} (f : G →g K)
    (hi : Set.InjOn (Sym2.map f) G.edgeSet)
    (hs : Set.SurjOn (Sym2.map f) G.edgeSet K.edgeSet)
    (B : Set V) (hB : Set.InjOn f Bᶜ) (hdegree : ∀ v ∈ B, G.degree v = 2)
    (D : Finset G.Subgraph)
    (hcy : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D) :
    ∃ E : Finset K.Subgraph,
      (∀ A ∈ E, A.coe.Connected ∧ A.coe.IsRegularOfDegree 2) ∧
      IsDecomposition K E ∧ E.card ≤ D.card + B.ncard := by
  have hex : ∀ H : {H // H ∈ D}, ∃ F : Finset K.Subgraph,
      (∀ A ∈ F, A.coe.Connected ∧ A.coe.IsRegularOfDegree 2) ∧
      Set.PairwiseDisjoint (F : Set K.Subgraph) (fun A => A.edgeSet) ∧
      (⋃ A ∈ F, A.edgeSet) = (H.val.map f).edgeSet ∧
      F.card ≤ 1 + (H.val.verts ∩ B).ncard := by
    intro H
    exact projected_cycle_decomposition_exceptional_bound f hi B hB H.val
      (hcy H.val H.property).1 (hcy H.val H.property).2
  choose F hcF hdF heF hbF using hex
  let E := Finset.univ.biUnion F
  have hsub (H : {H // H ∈ D}) (A : K.Subgraph) (hA : A ∈ F H) :
      A.edgeSet ⊆ (H.val.map f).edgeSet := by
    intro e he
    rw [← heF H]
    exact Set.mem_iUnion.mpr ⟨A, Set.mem_iUnion.mpr ⟨hA, he⟩⟩
  refine ⟨E, ?_, ⟨?_, ?_⟩, ?_⟩
  · intro A hA
    obtain ⟨H, _, hA⟩ := Finset.mem_biUnion.mp hA
    refine ⟨(hcF H A hA).1, ?_⟩
    intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using (hcF H A hA).2 v
  · intro A hA A' hA' hAA'
    obtain ⟨H, _, hA⟩ := Finset.mem_biUnion.mp hA
    obtain ⟨H', _, hA'⟩ := Finset.mem_biUnion.mp hA'
    by_cases hHH' : H = H'
    · subst H'
      exact hdF H hA hA' hAA'
    · apply Set.disjoint_left.mpr
      intro e he he'
      have h1 := hsub H A hA he
      have h2 := hsub H' A' hA' he'
      rw [Subgraph.edgeSet_map] at h1 h2
      obtain ⟨d, hd1, hde⟩ := h1
      obtain ⟨d', hd2, hde'⟩ := h2
      have heq := hi (H.val.edgeSet_subset hd1) (H'.val.edgeSet_subset hd2) (hde.trans hde'.symm)
      exact Set.disjoint_left.mp (hd.1 H.property H'.property (fun h => hHH' (Subtype.ext h)))
        hd1 (heq.symm ▸ hd2)
  · ext e
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨A, _, he⟩
      exact A.edgeSet_subset he
    · intro he
      obtain ⟨d, hdG, hde⟩ := hs he
      rw [← hd.2] at hdG
      simp only [Set.mem_iUnion] at hdG
      obtain ⟨H, hH, hdH⟩ := hdG
      have heH : e ∈ (H.map f).edgeSet := by
        rw [Subgraph.edgeSet_map]
        exact ⟨d, hdH, hde⟩
      rw [← heF ⟨H, hH⟩] at heH
      simp only [Set.mem_iUnion] at heH
      obtain ⟨A, hA, heA⟩ := heH
      exact ⟨A, Finset.mem_biUnion.mpr ⟨⟨H, hH⟩, Finset.mem_univ _, hA⟩, heA⟩
  · calc
      E.card ≤ ∑ H, (F H).card := Finset.card_biUnion_le
      _ ≤ ∑ H : {H // H ∈ D}, (1 + (H.val.verts ∩ B).ncard) :=
        Finset.sum_le_sum (fun H _ => hbF H)
      _ = D.card + ∑ H ∈ D, (H.verts ∩ B).ncard := by
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one,
          Fintype.card_coe]
        exact congrArg (D.card + ·) (Finset.sum_coe_sort D (fun H => (H.verts ∩ B).ncard))
      _ = D.card + B.ncard := by
        rw [cycle_decomposition_exceptional_incidence G D hcy hd B hdegree]

end Erdos184
