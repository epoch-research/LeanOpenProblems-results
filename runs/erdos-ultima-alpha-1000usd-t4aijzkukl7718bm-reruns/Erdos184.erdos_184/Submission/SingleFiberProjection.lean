import Submission.Projection

/-!
Exact amortized projection cost when one fibre of degree-two vertices is
identified. This is a tool for vertex smoothing, not a proof of Erdos 184.
-/
open SimpleGraph
open scoped Classical
namespace Erdos184
namespace SingleFiberProjection

/-- The exact loss of vertex cardinality under a map with just one possibly
nontrivial fibre. The indicator accounts for that fibre's surviving image. -/
lemma image_card_one_fiber {V W : Type*} [Finite V] [Finite W]
    (f : V → W) (w : W) (hi : Set.InjOn f (f ⁻¹' {w})ᶜ) (S : Set V) :
    (f '' S).ncard + (S ∩ f ⁻¹' {w}).ncard =
      S.ncard + if (S ∩ f ⁻¹' {w}).Nonempty then 1 else 0 := by
  let B := f ⁻¹' {w}
  have hpart : (S \ B) ∪ (S ∩ B) = S := by ext x; simp
  have hdis : Disjoint (S \ B) (S ∩ B) := by
    apply Set.disjoint_left.mpr
    exact fun _ hx hy => hx.2 hy.2
  have himg : Disjoint (f '' (S \ B)) (f '' (S ∩ B)) := by
    apply Set.disjoint_left.mpr
    rintro y ⟨a,ha,rfl⟩ ⟨b,hb,heq⟩
    apply ha.2
    change f a = w
    have hbw : f b = w := hb.2
    exact heq.symm.trans hbw
  have hcard := Set.ncard_union_eq hdis
  rw [hpart] at hcard
  have hcardimg := Set.ncard_union_eq himg
  rw [← Set.image_union, hpart] at hcardimg
  have hinj : (f '' (S \ B)).ncard = (S \ B).ncard :=
    Set.ncard_image_of_injOn (hi.mono (fun _ h => h.2))
  have hsmall : (f '' (S ∩ B)).ncard = if (S ∩ B).Nonempty then 1 else 0 := by
    split_ifs with h
    · have heq : f '' (S ∩ B) = {w} := by
        apply Set.Subset.antisymm
        · rintro _ ⟨x,hx,rfl⟩
          exact hx.2
        · rintro y rfl
          obtain ⟨x,hx⟩ := h
          exact ⟨x,hx,hx.2⟩
      rw [heq, Set.ncard_singleton]
    · rw [Set.not_nonempty_iff_eq_empty.mp h]
      simp
  change (f '' S).ncard + (S ∩ B).ncard =
    S.ncard + if (S ∩ B).Nonempty then 1 else 0
  omega

lemma projected_cycle_bound {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {K : SimpleGraph W} (f : G →g K)
    (hi : Set.InjOn (Sym2.map f) G.edgeSet)
    (w : W) (hB : Set.InjOn f (f ⁻¹' {w})ᶜ)
    (H : G.Subgraph) (hc : H.coe.Connected) (hr : H.coe.IsRegularOfDegree 2) :
    ∃ F : Finset K.Subgraph,
      (∀ A ∈ F, A.coe.Connected ∧ A.coe.IsRegularOfDegree 2) ∧
      Set.PairwiseDisjoint (F : Set K.Subgraph) (fun A => A.edgeSet) ∧
      (⋃ A ∈ F, A.edgeSet) = (H.map f).edgeSet ∧
      F.card + (if (H.verts ∩ f ⁻¹' {w}).Nonempty then 1 else 0) ≤
        1 + (H.verts ∩ f ⁻¹' {w}).ncard := by
  obtain ⟨E,hcE,hdE,hbE⟩ := projected_cycle_decomposition_rank_bound f hi H hc hr
  obtain ⟨F,hcF,hdF,heF,hbF⟩ := lift_cycle_decomposition (H.map f) E (by
    intro A hA
    refine ⟨(hcE A hA).1,?_⟩
    intro v
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using (hcE A hA).2 v) hdE
  refine ⟨F,?_,hdF,heF,?_⟩
  · intro A hA
    refine ⟨(hcF A hA).1,?_⟩
    intro v
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using (hcF A hA).2 v
  · have hcard := image_card_one_fiber f w hB H.verts
    change E.card + (f '' H.verts).ncard ≤ _ at hbE
    omega

/-- Identifying r degree-two copies of one vertex costs at most r-q additional
pieces, where q is the number of original pieces meeting the copies. -/
lemma project_decomposition {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {K : SimpleGraph W} (f : G →g K)
    (hi : Set.InjOn (Sym2.map f) G.edgeSet)
    (hs : Set.SurjOn (Sym2.map f) G.edgeSet K.edgeSet)
    (w : W) (hB : Set.InjOn f (f ⁻¹' {w})ᶜ)
    (hdegree : ∀ v, f v = w → G.degree v = 2)
    (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D) :
    ∃ E : Finset K.Subgraph,
      (∀ A ∈ E, A.coe.Connected ∧ A.coe.IsRegularOfDegree 2) ∧
      IsDecomposition K E ∧
      E.card + (D.filter (fun H => (H.verts ∩ f ⁻¹' {w}).Nonempty)).card ≤
        D.card + (f ⁻¹' {w}).ncard := by
  have hex : ∀ H : {H // H ∈ D}, ∃ F : Finset K.Subgraph,
      (∀ A ∈ F, A.coe.Connected ∧ A.coe.IsRegularOfDegree 2) ∧
      Set.PairwiseDisjoint (F : Set K.Subgraph) (fun A => A.edgeSet) ∧
      (⋃ A ∈ F, A.edgeSet) = (H.val.map f).edgeSet ∧
      F.card + (if (H.val.verts ∩ f ⁻¹' {w}).Nonempty then 1 else 0) ≤
        1 + (H.val.verts ∩ f ⁻¹' {w}).ncard := by
    intro H
    exact projected_cycle_bound f hi w hB H.val (hc H.val H.property).1
      (hc H.val H.property).2
  choose F hcF hdF heF hbF using hex
  let E := Finset.univ.biUnion F
  have hsub (H : {H // H ∈ D}) (A : K.Subgraph) (hA : A ∈ F H) :
      A.edgeSet ⊆ (H.val.map f).edgeSet := by
    intro e he
    rw [← heF H]
    exact Set.mem_iUnion.mpr ⟨A,Set.mem_iUnion.mpr ⟨hA,he⟩⟩
  refine ⟨E,?_,⟨?_,?_⟩,?_⟩
  · intro A hA
    obtain ⟨H,_,hA⟩ := Finset.mem_biUnion.mp hA
    refine ⟨(hcF H A hA).1,?_⟩
    intro v
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using (hcF H A hA).2 v
  · intro A hA A' hA' hAA'
    obtain ⟨H,_,hA⟩ := Finset.mem_biUnion.mp hA
    obtain ⟨H',_,hA'⟩ := Finset.mem_biUnion.mp hA'
    by_cases hHH' : H = H'
    · subst H'
      exact hdF H hA hA' hAA'
    · apply Set.disjoint_left.mpr
      intro e he he'
      have h1 := hsub H A hA he
      have h2 := hsub H' A' hA' he'
      rw [Subgraph.edgeSet_map] at h1 h2
      obtain ⟨d,hd1,hde⟩ := h1
      obtain ⟨d',hd2,hde'⟩ := h2
      have heq := hi (H.val.edgeSet_subset hd1) (H'.val.edgeSet_subset hd2)
        (hde.trans hde'.symm)
      exact Set.disjoint_left.mp (hd.1 H.property H'.property
        (fun h => hHH' (Subtype.ext h))) hd1 (heq.symm ▸ hd2)
  · ext e
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨A,_,he⟩
      exact A.edgeSet_subset he
    · intro he
      obtain ⟨d,hdG,hde⟩ := hs he
      rw [← hd.2] at hdG
      obtain ⟨H,hH,hdH⟩ := Set.mem_iUnion₂.mp hdG
      have heH : e ∈ (H.map f).edgeSet := by
        rw [Subgraph.edgeSet_map]
        exact ⟨d,hdH,hde⟩
      rw [← heF ⟨H,hH⟩] at heH
      obtain ⟨A,hA,heA⟩ := Set.mem_iUnion₂.mp heH
      exact ⟨A,Finset.mem_biUnion.mpr ⟨⟨H,hH⟩,Finset.mem_univ _,hA⟩,heA⟩
  · have hsum := Finset.sum_le_sum (s := Finset.univ) (fun H _ => hbF H)
    have hcard : E.card ≤ ∑ H, (F H).card := Finset.card_biUnion_le
    have hinc := cycle_decomposition_exceptional_incidence G D hc hd
      (f ⁻¹' {w}) (fun v hv => hdegree v hv)
    have hq : (∑ H : {H // H ∈ D},
        if (H.val.verts ∩ f ⁻¹' {w}).Nonempty then 1 else 0) =
        (D.filter (fun H => (H.verts ∩ f ⁻¹' {w}).Nonempty)).card := by
      simpa only [Finset.card_filter] using
        Finset.sum_coe_sort D (fun H => if (H.verts ∩ f ⁻¹' {w}).Nonempty then 1 else 0)
    have hr : (∑ H : {H // H ∈ D}, (H.val.verts ∩ f ⁻¹' {w}).ncard) =
        (f ⁻¹' {w}).ncard := by
      exact (Finset.sum_coe_sort D (fun H => (H.verts ∩ f ⁻¹' {w}).ncard)).trans hinc
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      smul_eq_mul, mul_one, Fintype.card_coe, hq, hr] at hsum
    omega

/-- A nonempty degree-two fibre meets at least one piece, giving the usual
r-1 bound as a consequence of the sharper r-q estimate. -/
lemma project_decomposition_nonempty_fiber {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {K : SimpleGraph W} (f : G →g K)
    (hi : Set.InjOn (Sym2.map f) G.edgeSet)
    (hs : Set.SurjOn (Sym2.map f) G.edgeSet K.edgeSet)
    (w : W) (hB : Set.InjOn f (f ⁻¹' {w})ᶜ)
    (hdegree : ∀ v, f v = w → G.degree v = 2)
    (hne : (f ⁻¹' {w}).Nonempty)
    (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D) :
    ∃ E : Finset K.Subgraph,
      (∀ A ∈ E, A.coe.Connected ∧ A.coe.IsRegularOfDegree 2) ∧
      IsDecomposition K E ∧ E.card + 1 ≤ D.card + (f ⁻¹' {w}).ncard := by
  obtain ⟨E,hcE,hdE,hbE⟩ := project_decomposition f hi hs w hB hdegree D hc hd
  refine ⟨E,hcE,hdE,?_⟩
  obtain ⟨v,hv⟩ := hne
  have hdeg := hdegree v hv
  have hvcount := cycle_decomposition_vertex_count G D hc hd v
  have hpos : 0 < (D.filter (fun H => v ∈ H.verts)).card := by omega
  obtain ⟨H,hH⟩ := Finset.card_pos.mp hpos
  obtain ⟨hHD,hvH⟩ := Finset.mem_filter.mp hH
  have hq : 0 < (D.filter (fun H => (H.verts ∩ f ⁻¹' {w}).Nonempty)).card :=
    Finset.card_pos.mpr ⟨H,Finset.mem_filter.mpr ⟨hHD,⟨v,hvH,hv⟩⟩⟩
  omega

/-- If each piece meets the fibre at most once, identification costs no
additional cycles. This does not assert existence of such a decomposition. -/
lemma project_decomposition_no_repeat {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {K : SimpleGraph W} (f : G →g K)
    (hi : Set.InjOn (Sym2.map f) G.edgeSet)
    (hs : Set.SurjOn (Sym2.map f) G.edgeSet K.edgeSet)
    (w : W) (hB : Set.InjOn f (f ⁻¹' {w})ᶜ)
    (hdegree : ∀ v, f v = w → G.degree v = 2)
    (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D)
    (hn : ∀ H ∈ D, (H.verts ∩ f ⁻¹' {w}).ncard ≤ 1) :
    ∃ E : Finset K.Subgraph,
      (∀ A ∈ E, A.coe.Connected ∧ A.coe.IsRegularOfDegree 2) ∧
      IsDecomposition K E ∧ E.card ≤ D.card := by
  obtain ⟨E,hcE,hdE,hbE⟩ := project_decomposition f hi hs w hB hdegree D hc hd
  refine ⟨E,hcE,hdE,?_⟩
  have hq : (D.filter (fun H => (H.verts ∩ f ⁻¹' {w}).Nonempty)).card =
      (f ⁻¹' {w}).ncard := by
    rw [← cycle_decomposition_exceptional_incidence G D hc hd (f ⁻¹' {w})
      (fun v hv => hdegree v hv), Finset.card_filter]
    apply Finset.sum_congr rfl
    intro H hH
    have hb := hn H hH
    split_ifs with h
    · have hp := Set.ncard_pos (Set.toFinite (H.verts ∩ f ⁻¹' {w})) |>.mpr h
      omega
    · rw [Set.not_nonempty_iff_eq_empty.mp h]
      simp
  omega

end SingleFiberProjection
end Erdos184
