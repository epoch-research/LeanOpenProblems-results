import Submission.Projection

/-!
Loop-erasing projection along a vertex map. Only noncollapsed edges are
required to be injective. This supplies contraction infrastructure, not a
linear cycle-decomposition theorem.
-/
open SimpleGraph
open scoped Classical
namespace Erdos184
namespace WeakProjection
variable {V W : Type*} {G : SimpleGraph V} {K : SimpleGraph W}

def IsWeakMap (f : V → W) : Prop :=
  ∀ ⦃u v⦄, G.Adj u v → f u = f v ∨ K.Adj (f u) (f v)

def survivingEdges (G : SimpleGraph V) (f : V → W) : Set (Sym2 V) :=
  {e | e ∈ G.edgeSet ∧ ¬(Sym2.map f e).IsDiag}

noncomputable def mapWalk (f : V → W) (hf : IsWeakMap (G := G) (K := K) f)
    {u v : V} : G.Walk u v → K.Walk (f u) (f v)
  | .nil => .nil
  | @Walk.cons _ _ u v w h p =>
    if hh : f u = f v then (mapWalk f hf p).copy hh.symm rfl
    else .cons ((hf h).resolve_left hh) (mapWalk f hf p)

lemma edges_mapWalk (f : V → W) (hf : IsWeakMap (G := G) (K := K) f)
    {u v : V} (p : G.Walk u v) :
    (mapWalk f hf p).edges =
      (p.edges.filter (fun e => !(Sym2.map f e).IsDiag)).map (Sym2.map f) := by
  induction p with
  | nil => simp [mapWalk]
  | @cons u v w h p ih =>
    by_cases hh : f u = f v <;>
      simp [mapWalk,hh,ih,Sym2.map_pair_eq]

lemma mapWalk_isTrail (f : V → W) (hf : IsWeakMap (G := G) (K := K) f)
    (hi : Set.InjOn (Sym2.map f) (survivingEdges G f))
    {u v : V} (p : G.Walk u v) (hp : p.IsTrail) : (mapWalk f hf p).IsTrail := by
  rw [Walk.isTrail_def,edges_mapWalk]
  apply List.Nodup.map_on _ (hp.edges_nodup.filter _)
  intro e he d hd hed
  have he' := List.mem_filter.mp he
  have hd' := List.mem_filter.mp hd
  apply hi ⟨p.edges_subset_edgeSet he'.1,?_⟩ ⟨p.edges_subset_edgeSet hd'.1,?_⟩ hed
  · simpa using he'.2
  · simpa using hd'.2

lemma connected_map (f : V → W) (hf : IsWeakMap (G := G) (K := K) f)
    (hs : Function.Surjective f) (hc : G.Connected) : K.Connected := by
  have hn : Nonempty W := hc.nonempty.map f
  refine { nonempty := hn, preconnected := ?_ }
  intro x y
  obtain ⟨u,rfl⟩ := hs x
  obtain ⟨v,rfl⟩ := hs y
  obtain ⟨p⟩ := hc.preconnected u v
  exact ⟨mapWalk f hf p⟩

lemma eulerian_map (f : V → W) (hf : IsWeakMap (G := G) (K := K) f)
    (hi : Set.InjOn (Sym2.map f) (survivingEdges G f))
    (hs : Set.SurjOn (Sym2.map f) (survivingEdges G f) K.edgeSet)
    {u v : V} (p : G.Walk u v) (hp : p.IsEulerian) : (mapWalk f hf p).IsEulerian := by
  apply (mapWalk_isTrail f hf hi p hp.isTrail).isEulerian_of_forall_mem
  intro e he
  obtain ⟨d,hd,rfl⟩ := hs he
  rw [edges_mapWalk]
  apply List.mem_map.mpr
  refine ⟨d,List.mem_filter.mpr ⟨hp.mem_edges_iff.mpr hd.1,?_⟩,rfl⟩
  simpa using hd.2

lemma connected_even_map [Fintype V] [Fintype W]
    (f : V → W) (hf : IsWeakMap (G := G) (K := K) f)
    (hi : Set.InjOn (Sym2.map f) (survivingEdges G f))
    (hs : Set.SurjOn (Sym2.map f) (survivingEdges G f) K.edgeSet)
    (hv : Function.Surjective f) (hc : G.Connected) (he : ∀ v, Even (G.degree v)) :
    K.Connected ∧ ∀ w, Even (K.degree w) := by
  refine ⟨connected_map f hf hv hc,?_⟩
  obtain ⟨u,p,hp⟩ := exists_eulerian_closed_walk G hc he
  have hq := eulerian_map f hf hi hs p hp
  intro w
  exact hq.even_degree_iff.mpr (by simp)

/-- The subgraph image retains the image vertices but discards collapsed
edges, rather than pretending that a contraction is an ordinary homomorphism. -/
def image (f : V → W) (hf : IsWeakMap (G := G) (K := K) f) (H : G.Subgraph) :
    K.Subgraph where
  verts := f '' H.verts
  Adj x y := x ≠ y ∧ ∃ u v, H.Adj u v ∧ f u = x ∧ f v = y
  adj_sub := by
    rintro x y ⟨hne,u,v,h,hx,hy⟩
    have hh := hf (H.adj_sub h)
    rw [hx,hy] at hh
    exact hh.resolve_left hne
  edge_vert := by
    rintro x y ⟨_,u,v,h,hx,_⟩
    exact ⟨u,H.edge_vert h,hx⟩
  symm := by
    rintro x y ⟨hne,u,v,h,hx,hy⟩
    exact ⟨hne.symm,v,u,H.symm h,hy,hx⟩

lemma image_edgeSet (f : V → W) (hf : IsWeakMap (G := G) (K := K) f)
    (H : G.Subgraph) :
    (image f hf H).edgeSet = Sym2.map f '' survivingEdges H.spanningCoe f := by
  ext e
  constructor
  · intro he
    induction e using Sym2.ind with
    | h x y =>
      obtain ⟨hne,u,v,h,hx,hy⟩ := he
      refine ⟨s(u,v),⟨h,?_⟩,?_⟩
      · simpa only [Sym2.map_pair_eq,Sym2.mk_isDiag_iff,hx,hy] using hne
      · simp only [Sym2.map_pair_eq,hx,hy]
  · rintro ⟨d,hd,rfl⟩
    induction d using Sym2.ind with
    | h u v =>
      refine ⟨?_,u,v,hd.1,rfl,rfl⟩
      simpa only [Sym2.map_pair_eq,Sym2.mk_isDiag_iff] using hd.2

def imageMap (f : V → W) (hf : IsWeakMap (G := G) (K := K) f) (H : G.Subgraph) :
    H.verts → (image f hf H).verts := fun x => ⟨f x.val,⟨x.val,x.property,rfl⟩⟩

lemma imageMap_surjective (f : V → W) (hf : IsWeakMap (G := G) (K := K) f)
    (H : G.Subgraph) : Function.Surjective (imageMap f hf H) := by
  rintro ⟨y,x,hx,rfl⟩
  exact ⟨⟨x,hx⟩,rfl⟩

lemma imageMap_weak (f : V → W) (hf : IsWeakMap (G := G) (K := K) f)
    (H : G.Subgraph) : IsWeakMap (G := H.coe) (K := (image f hf H).coe) (imageMap f hf H) := by
  intro x y h
  by_cases he : f x.val = f y.val
  · left
    exact Subtype.ext he
  · right
    exact ⟨he,x.val,y.val,h,rfl,rfl⟩

lemma imageMap_comm (f : V → W) (hf : IsWeakMap (G := G) (K := K) f)
    (H : G.Subgraph) (e : Sym2 H.verts) :
    Sym2.map (Subtype.val : (image f hf H).verts → W) (Sym2.map (imageMap f hf H) e) =
      Sym2.map f (Sym2.map (Subtype.val : H.verts → V) e) := by
  simp only [Sym2.map_map]
  rfl

lemma imageMap_edge_injective (f : V → W) (hf : IsWeakMap (G := G) (K := K) f)
    (hi : Set.InjOn (Sym2.map f) (survivingEdges G f)) (H : G.Subgraph) :
    Set.InjOn (Sym2.map (imageMap f hf H)) (survivingEdges H.coe (imageMap f hf H)) := by
  intro e he d hd hed
  apply Sym2.map.injective Subtype.val_injective
  have hs (a : Sym2 H.verts) (ha : a ∈ survivingEdges H.coe (imageMap f hf H)) :
      Sym2.map (Subtype.val : H.verts → V) a ∈ survivingEdges G f := by
    refine ⟨H.hom.map_mem_edgeSet ha.1,?_⟩
    have hn := (Sym2.isDiag_map (f := (Subtype.val : (image f hf H).verts → W))
      Subtype.val_injective).not.mpr ha.2
    rwa [imageMap_comm] at hn
  apply hi (hs e he) (hs d hd)
  have hh := congrArg (Sym2.map (Subtype.val : (image f hf H).verts → W)) hed
  simpa only [imageMap_comm] using hh

lemma imageMap_edge_surjective (f : V → W) (hf : IsWeakMap (G := G) (K := K) f)
    (H : G.Subgraph) :
    Set.SurjOn (Sym2.map (imageMap f hf H)) (survivingEdges H.coe (imageMap f hf H))
      (image f hf H).coe.edgeSet := by
  intro e he
  have he' : Sym2.map (Subtype.val : (image f hf H).verts → W) e ∈
      (image f hf H).edgeSet := by
    simpa only [Subgraph.edgeSet_coe,Set.mem_preimage] using he
  rw [image_edgeSet] at he'
  obtain ⟨d,hd,hde⟩ := he'
  have hdH : d ∈ H.edgeSet := hd.1
  rw [← H.image_coe_edgeSet_coe] at hdH
  obtain ⟨b,hb,hbd⟩ := hdH
  refine ⟨b,⟨hb,?_⟩,?_⟩
  · intro hn
    have hn' := hn.map (f := (Subtype.val : (image f hf H).verts → W))
    rw [imageMap_comm,hbd] at hn'
    exact hd.2 hn'
  · apply Sym2.map.injective Subtype.val_injective
    rw [imageMap_comm,hbd,hde]

lemma image_connected_even [Fintype V] [Fintype W]
    (f : V → W) (hf : IsWeakMap (G := G) (K := K) f)
    (hi : Set.InjOn (Sym2.map f) (survivingEdges G f)) (H : G.Subgraph)
    (hc : H.coe.Connected) (he : ∀ v, Even (H.coe.degree v)) :
    (image f hf H).coe.Connected ∧ ∀ w, Even ((image f hf H).coe.degree w) := by
  have hh := connected_even_map (imageMap f hf H) (imageMap_weak f hf H)
    (imageMap_edge_injective f hf hi H) (imageMap_edge_surjective f hf H)
    (imageMap_surjective f hf H) hc (by
      intro v
      simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using he v)
  refine ⟨hh.1,?_⟩
  intro w
  simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hh.2 w

lemma image_edge_card [Fintype V] [Fintype W]
    (f : V → W) (hf : IsWeakMap (G := G) (K := K) f)
    (hi : Set.InjOn (Sym2.map f) (survivingEdges G f)) (H : G.Subgraph) :
    (image f hf H).edgeSet.ncard = (survivingEdges H.spanningCoe f).ncard := by
  rw [image_edgeSet]
  apply Set.ncard_image_of_injOn
  apply hi.mono
  intro e he
  exact ⟨H.edgeSet_subset he.1,he.2⟩

set_option maxHeartbeats 800000 in
/-- A contracted even connected piece decomposes at the cycle-space cost
of its surviving edges. An entirely collapsed cycle correctly costs zero. -/
lemma image_decomposition_bound [Fintype V] [Fintype W]
    (f : V → W) (hf : IsWeakMap (G := G) (K := K) f)
    (hi : Set.InjOn (Sym2.map f) (survivingEdges G f)) (H : G.Subgraph)
    (hc : H.coe.Connected) (he : ∀ v, Even (H.coe.degree v)) :
    ∃ E : Finset (image f hf H).coe.Subgraph,
      (∀ A ∈ E, A.coe.Connected ∧ A.coe.IsRegularOfDegree 2) ∧
      IsDecomposition (image f hf H).coe E ∧
      E.card + (f '' H.verts).ncard ≤ (survivingEdges H.spanningCoe f).ncard + 1 := by
  obtain ⟨hconn,heven⟩ := image_connected_even f hf hi H hc he
  obtain ⟨E,hcE,hdE⟩ := even_cycle_decomposition (image f hf H).coe (by
    intro v
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using heven v)
  refine ⟨E,?_,hdE,?_⟩
  · intro A hA
    refine ⟨(hcE A hA).1,?_⟩
    intro v
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using (hcE A hA).2 v
  have hb := connected_cycle_decomposition_rank_bound (image f hf H).coe hconn E hcE hdE
  rw [coe_edgeFinset_card,image_edge_card f hf hi H] at hb
  simpa only [← Nat.card_eq_fintype_card,Nat.card_coe_set_eq] using hb

lemma mapsTo_surviving (f : V → W) (hf : IsWeakMap (G := G) (K := K) f) :
    Set.MapsTo (Sym2.map f) (survivingEdges G f) K.edgeSet := by
  intro e he
  induction e using Sym2.ind with
  | h u v =>
    have hn : f u ≠ f v := by
      simpa only [Sym2.map_pair_eq,Sym2.mk_isDiag_iff] using he.2
    exact (hf he.1).resolve_left hn

lemma surviving_card_sum [Fintype V] (f : V → W)
    (D : Finset G.Subgraph) (hd : IsDecomposition G D) :
    (∑ H ∈ D, (survivingEdges H.spanningCoe f).ncard) = (survivingEdges G f).ncard := by
  let F := fun H : G.Subgraph => (survivingEdges H.spanningCoe f).toFinset
  have hdis : (D : Set G.Subgraph).PairwiseDisjoint F := by
    intro H hH J hJ hne
    apply Finset.disjoint_left.mpr
    intro e heH heJ
    exact Set.disjoint_left.mp (hd.1 hH hJ hne)
      (Set.mem_toFinset.mp heH).1 (Set.mem_toFinset.mp heJ).1
  have hcov : D.biUnion F = (survivingEdges G f).toFinset := by
    ext e
    simp only [Finset.mem_biUnion,F,Set.mem_toFinset]
    constructor
    · rintro ⟨H,_,heH⟩
      exact ⟨H.edgeSet_subset heH.1,heH.2⟩
    · rintro ⟨heG,hn⟩
      rw [← hd.2] at heG
      obtain ⟨H,hH,heH⟩ := Set.mem_iUnion₂.mp heG
      exact ⟨H,hH,heH,hn⟩
  have hh := Finset.card_biUnion hdis
  rw [hcov,← Set.ncard_eq_toFinset_card'] at hh
  simpa only [F,← Set.ncard_eq_toFinset_card'] using hh.symm

lemma projected_piece_bound [Fintype V] [Fintype W]
    (f : V → W) (hf : IsWeakMap (G := G) (K := K) f)
    (hi : Set.InjOn (Sym2.map f) (survivingEdges G f)) (H : G.Subgraph)
    (hc : H.coe.Connected) (hr : H.coe.IsRegularOfDegree 2) :
    ∃ F : Finset K.Subgraph,
      (∀ A ∈ F, A.coe.Connected ∧ A.coe.IsRegularOfDegree 2) ∧
      Set.PairwiseDisjoint (F : Set K.Subgraph) (fun A => A.edgeSet) ∧
      (⋃ A ∈ F, A.edgeSet) = (image f hf H).edgeSet ∧
      F.card + (f '' H.verts).ncard ≤ (survivingEdges H.spanningCoe f).ncard + 1 := by
  obtain ⟨E,hcE,hdE,hbE⟩ := image_decomposition_bound f hf hi H hc (by
    intro v
    have hh := hr v
    simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hh ⊢
    rw [hh]
    decide)
  obtain ⟨F,hcF,hdF,heF,hbF⟩ := lift_cycle_decomposition (image f hf H) E (by
    intro A hA
    refine ⟨(hcE A hA).1,?_⟩
    intro v
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using (hcE A hA).2 v) hdE
  refine ⟨F,?_,hdF,heF,by omega⟩
  intro A hA
  refine ⟨(hcF A hA).1,?_⟩
  intro v
  simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using (hcF A hA).2 v

set_option maxHeartbeats 800000 in
/-- Project a complete cycle decomposition, erasing collapsed edges and
charging exactly for the surviving edges and image-vertex incidences. -/
lemma project_decomposition [Fintype V] [Fintype W]
    (f : V → W) (hf : IsWeakMap (G := G) (K := K) f)
    (hi : Set.InjOn (Sym2.map f) (survivingEdges G f))
    (hs : Set.SurjOn (Sym2.map f) (survivingEdges G f) K.edgeSet)
    (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D) :
    ∃ E : Finset K.Subgraph,
      (∀ A ∈ E, A.coe.Connected ∧ A.coe.IsRegularOfDegree 2) ∧
      IsDecomposition K E ∧
      E.card + (∑ H ∈ D, (f '' H.verts).ncard) ≤ K.edgeSet.ncard + D.card := by
  have hex : ∀ H : {H // H ∈ D}, ∃ F : Finset K.Subgraph,
      (∀ A ∈ F, A.coe.Connected ∧ A.coe.IsRegularOfDegree 2) ∧
      Set.PairwiseDisjoint (F : Set K.Subgraph) (fun A => A.edgeSet) ∧
      (⋃ A ∈ F, A.edgeSet) = (image f hf H.val).edgeSet ∧
      F.card + (f '' H.val.verts).ncard ≤ (survivingEdges H.val.spanningCoe f).ncard + 1 := by
    intro H
    exact projected_piece_bound f hf hi H.val (hc H.val H.property).1 (hc H.val H.property).2
  choose F hcF hdF heF hbF using hex
  let E := Finset.univ.biUnion F
  have hsub (H : {H // H ∈ D}) (A : K.Subgraph) (hA : A ∈ F H) :
      A.edgeSet ⊆ (image f hf H.val).edgeSet := by
    intro e he
    rw [← heF H]
    exact Set.mem_iUnion₂.mpr ⟨A,hA,he⟩
  refine ⟨E,?_,⟨?_,?_⟩,?_⟩
  · intro A hA
    obtain ⟨H,_,hA⟩ := Finset.mem_biUnion.mp hA
    refine ⟨(hcF H A hA).1,?_⟩
    intro v
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using (hcF H A hA).2 v
  · intro A hA B hB hne
    obtain ⟨H,_,hA⟩ := Finset.mem_biUnion.mp hA
    obtain ⟨J,_,hB⟩ := Finset.mem_biUnion.mp hB
    by_cases hHJ : H = J
    · subst J
      exact hdF H hA hB hne
    · apply Set.disjoint_left.mpr
      intro e heA heB
      have hh := hsub H A hA heA
      have hj := hsub J B hB heB
      rw [image_edgeSet] at hh hj
      obtain ⟨d,hdH,hde⟩ := hh
      obtain ⟨b,hbJ,hbe⟩ := hj
      have heq := hi ⟨H.val.edgeSet_subset hdH.1,hdH.2⟩
        ⟨J.val.edgeSet_subset hbJ.1,hbJ.2⟩ (hde.trans hbe.symm)
      exact Set.disjoint_left.mp (hd.1 H.property J.property
        (fun h => hHJ (Subtype.ext h))) hdH.1 (heq.symm ▸ hbJ.1)
  · ext e
    constructor
    · rintro ⟨_,⟨A,rfl⟩,_,⟨_,rfl⟩,heA⟩
      exact A.edgeSet_subset heA
    · intro he
      obtain ⟨d,hdG,hde⟩ := hs he
      have hdG' := hdG.1
      rw [← hd.2] at hdG'
      obtain ⟨H,hH,hdH⟩ := Set.mem_iUnion₂.mp hdG'
      have heH : e ∈ (image f hf H).edgeSet := by
        rw [image_edgeSet]
        exact ⟨d,⟨hdH,hdG.2⟩,hde⟩
      rw [← heF ⟨H,hH⟩] at heH
      obtain ⟨A,hA,heA⟩ := Set.mem_iUnion₂.mp heH
      exact Set.mem_iUnion₂.mpr ⟨A,
        Finset.mem_biUnion.mpr ⟨⟨H,hH⟩,Finset.mem_univ _,hA⟩,heA⟩
  · have hsum := Finset.sum_le_sum (s := Finset.univ) (fun H _ => hbF H)
    have hcard : E.card ≤ ∑ H, (F H).card := Finset.card_biUnion_le
    have hverts := Finset.sum_coe_sort D (fun H => (f '' H.verts).ncard)
    have hedges := (Finset.sum_coe_sort D (fun H => (survivingEdges H.spanningCoe f).ncard)).trans
      (surviving_card_sum f D hd)
    have himage : K.edgeSet = Sym2.map f '' survivingEdges G f :=
      Set.Subset.antisymm hs (by
        rintro e ⟨d,hd,rfl⟩
        exact mapsTo_surviving f hf hd)
    have hedgecard : K.edgeSet.ncard = (survivingEdges G f).ncard := by
      rw [himage]
      exact Set.ncard_image_of_injOn hi
    simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,
      smul_eq_mul,mul_one,Fintype.card_coe,hverts,hedges,← hedgecard] at hsum
    omega

end WeakProjection
end Erdos184
