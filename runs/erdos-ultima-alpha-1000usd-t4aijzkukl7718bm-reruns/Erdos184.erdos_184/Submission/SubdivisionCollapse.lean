import Submission.EdgeSubdivision

/-! Inverse cycle transport for subdivision of selected edges. This applies
only to genuine subdivisions; it does not suppress a vertex onto an already
present edge. -/
open SimpleGraph
open scoped Classical
namespace Erdos184.EdgeSubdivision
variable {V : Type*} {G : SimpleGraph V} {R : Set (Sym2 V)}
set_option maxHeartbeats 1000000

/-- Collapse two-edge passages through the added edge vertices. -/
def collapse (H : (graph G R).Subgraph) : G.Subgraph where
  verts v := Sum.inl v ∈ H.verts
  Adj u v := H.Adj (.inl u) (.inl v) ∨
    ∃ e : R, e.val = s(u,v) ∧ H.Adj (.inl u) (.inr e) ∧ H.Adj (.inl v) (.inr e)
  symm := by
    intro u v h
    rcases h with h | ⟨e,he,hu,hv⟩
    · exact Or.inl h.symm
    · exact Or.inr ⟨e,by simpa only [Sym2.eq_swap] using he,hv,hu⟩
  adj_sub := by
    intro u v h
    rcases h with h | ⟨e,he,hu,_⟩
    · exact (H.adj_sub h).1
    · have hg := (H.adj_sub hu).1
      rwa [he] at hg
  edge_vert := by
    intro u v h
    rcases h with h | ⟨e,_,hu,_⟩
    · exact H.edge_vert h
    · exact H.edge_vert hu

lemma collapse_lift (H : G.Subgraph) : collapse (lift R H) = H := by
  apply Subgraph.ext
  · rfl
  · funext u v
    apply propext
    constructor
    · rintro (h | ⟨e,he,hu,_⟩)
      · exact h.1
      · have heH := hu.1
        rwa [he] at heH
    · intro h
      by_cases he : s(u,v) ∈ R
      · exact Or.inr ⟨⟨s(u,v),he⟩,rfl,⟨h,Sym2.mem_mk_left _ _⟩,
          ⟨h,Sym2.mem_mk_right _ _⟩⟩
      · exact Or.inl ⟨h,he⟩

lemma new_saturated [Fintype V] (H : (graph G R).Subgraph)
    (hr : ∀ e : R, Sum.inr e ∈ H.verts → H.degree (.inr e) = 2)
    (e : R) (he : Sum.inr e ∈ H.verts) :
    ∀ x, H.Adj (.inr e) x ↔ (graph G R).Adj (.inr e) x := by
  have hh := hr e he
  obtain ⟨x,hx⟩ := (Subgraph.degree_pos_iff_exists_adj).mp (show 0 < H.degree (.inr e) by
    simp only [Subgraph.degree, ← Nat.card_eq_fintype_card] at hh ⊢
    omega)
  have hge : e.val ∈ G.edgeSet := by
    cases x with
    | inl x => exact (H.adj_sub hx).1
    | inr d => exact (H.adj_sub hx).elim
  have hg := degree_new G R e hge
  have hn : H.neighborSet (.inr e) = (graph G R).neighborSet (.inr e) := by
    apply Set.eq_of_subset_of_ncard_le (H.neighborSet_subset _)
    simp only [Subgraph.degree, ← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card,
      Nat.card_coe_set_eq] at hh hg
    omega
  intro x
  exact Set.ext_iff.mp hn x

lemma new_vertex_edge [Fintype V] (H : (graph G R).Subgraph)
    (hr : ∀ e : R, Sum.inr e ∈ H.verts → H.degree (.inr e) = 2) (e : R) :
    Sum.inr e ∈ H.verts ↔ e.val ∈ (collapse H).edgeSet := by
  obtain ⟨⟨u,v⟩,he⟩ := Sym2.mk_surjective e.val
  have he' : e.val = s(u,v) := he.symm
  constructor
  · intro hv
    have hh := hr e hv
    obtain ⟨x,hx⟩ := (Subgraph.degree_pos_iff_exists_adj).mp (show 0 < H.degree (.inr e) by
      simp only [Subgraph.degree, ← Nat.card_eq_fintype_card] at hh ⊢
      omega)
    have hge : e.val ∈ G.edgeSet := by
      cases x with
      | inl x => exact (H.adj_sub hx).1
      | inr d => exact (H.adj_sub hx).elim
    rw [he']
    refine Or.inr ⟨e,he',?_,?_⟩
    · exact ((new_saturated H hr e hv (.inl u)).mpr
        ⟨hge,by rw [he']; exact Sym2.mem_mk_left _ _⟩).symm
    · exact ((new_saturated H hr e hv (.inl v)).mpr
        ⟨hge,by rw [he']; exact Sym2.mem_mk_right _ _⟩).symm
  · rw [he']
    rintro (h | ⟨d,hd,hu,_⟩)
    · have hn := (H.adj_sub h).2
      exact (hn (he' ▸ e.property)).elim
    · have hde : d = e := Subtype.ext (hd.trans he'.symm)
      subst d
      exact H.edge_vert hu.symm

lemma lift_collapse [Fintype V] (H : (graph G R).Subgraph)
    (hr : ∀ e : R, Sum.inr e ∈ H.verts → H.degree (.inr e) = 2) :
    lift R (collapse H) = H := by
  apply Subgraph.ext
  · ext x
    cases x with
    | inl v => rfl
    | inr e => exact (new_vertex_edge H hr e).symm
  · funext x y
    apply propext
    cases x with
    | inl u =>
      cases y with
      | inl v =>
        change (((collapse H).Adj u v) ∧ s(u,v) ∉ R) ↔ H.Adj (.inl u) (.inl v)
        constructor
        · rintro ⟨h,hn⟩
          rcases h with h | ⟨e,he,_,_⟩
          · exact h
          · exact (hn (he ▸ e.property)).elim
        · intro h
          exact ⟨Or.inl h,(H.adj_sub h).2⟩
      | inr e =>
        change (e.val ∈ (collapse H).edgeSet ∧ u ∈ e.val) ↔ H.Adj (.inl u) (.inr e)
        rw [← new_vertex_edge H hr e]
        constructor
        · rintro ⟨he,hu⟩
          have hg : e.val ∈ G.edgeSet := (collapse H).edgeSet_subset ((new_vertex_edge H hr e).mp he)
          exact ((new_saturated H hr e he (.inl u)).mpr ⟨hg,hu⟩).symm
        · intro h
          exact ⟨H.edge_vert h.symm,(H.adj_sub h).2⟩
    | inr e =>
      cases y with
      | inl v =>
        change (e.val ∈ (collapse H).edgeSet ∧ v ∈ e.val) ↔ H.Adj (.inr e) (.inl v)
        rw [← new_vertex_edge H hr e]
        constructor
        · rintro ⟨he,hv⟩
          have hg : e.val ∈ G.edgeSet := (collapse H).edgeSet_subset ((new_vertex_edge H hr e).mp he)
          exact (new_saturated H hr e he (.inl v)).mpr ⟨hg,hv⟩
        · intro h
          exact ⟨H.edge_vert h,(H.adj_sub h).2⟩
      | inr d =>
        change False ↔ H.Adj (.inr e) (.inr d)
        exact ⟨False.elim,fun h => H.adj_sub h⟩

lemma edge_endpoint_exists (H : G.Subgraph) (e : R) (he : e.val ∈ H.edgeSet) :
    ∃ v : H.verts, v.val ∈ e.val := by
  obtain ⟨⟨a,b⟩,hab⟩ := Sym2.mk_surjective e.val
  have hh : H.Adj a b := by
    change s(a,b) ∈ H.edgeSet
    rwa [hab]
  exact ⟨⟨a,H.edge_vert hh⟩,hab ▸ Sym2.mem_mk_left a b⟩

noncomputable def edgeAnchor (H : G.Subgraph) (e : R) (he : e.val ∈ H.edgeSet) : H.verts :=
  Classical.choose (edge_endpoint_exists H e he)

lemma edgeAnchor_mem (H : G.Subgraph) (e : R) (he : e.val ∈ H.edgeSet) :
    (edgeAnchor H e he).val ∈ e.val := Classical.choose_spec (edge_endpoint_exists H e he)

noncomputable def anchor (H : G.Subgraph) : (lift R H).verts → H.verts
  | ⟨.inl v,hv⟩ => ⟨v,hv⟩
  | ⟨.inr e,he⟩ => edgeAnchor H e he

lemma endpoints_reachable (H : G.Subgraph) {e : Sym2 V} (he : e ∈ H.edgeSet)
    (u v : H.verts) (hu : u.val ∈ e) (hv : v.val ∈ e) : H.coe.Reachable u v := by
  by_cases h : u = v
  · subst v; exact .rfl
  · have hne : u.val ≠ v.val := fun hh => h (Subtype.ext hh)
    have heq : e = s(u.val,v.val) :=
      Sym2.eq_of_ne_mem hne hu hv (Sym2.mem_mk_left _ _) (Sym2.mem_mk_right _ _)
    rw [heq] at he
    exact (show H.coe.Adj u v from he).reachable

lemma anchor_adj_reachable (H : G.Subgraph) {x y : (lift R H).verts}
    (h : (lift R H).coe.Adj x y) : H.coe.Reachable (anchor H x) (anchor H y) := by
  rcases x with ⟨x,hx⟩
  rcases y with ⟨y,hy⟩
  cases x with
  | inl u =>
    cases y with
    | inl v => exact (show H.coe.Adj ⟨u,hx⟩ ⟨v,hy⟩ from h.1).reachable
    | inr e =>
      exact endpoints_reachable H hy ⟨u,hx⟩ (edgeAnchor H e hy)
        h.2 (edgeAnchor_mem H e hy)
  | inr e =>
    cases y with
    | inl v =>
      exact endpoints_reachable H hx (edgeAnchor H e hx) ⟨v,hy⟩
        (edgeAnchor_mem H e hx) h.2
    | inr d => exact h.elim

lemma connected_of_lift_connected (H : G.Subgraph) (hc : (lift R H).coe.Connected) :
    H.coe.Connected := by
  haveI : Nonempty H.verts := Nonempty.map (anchor H) hc.nonempty
  refine ⟨fun u v => ?_⟩
  obtain ⟨p⟩ := hc ⟨.inl u.val,u.property⟩ ⟨.inl v.val,v.property⟩
  have hp : ∀ {x y : (lift R H).verts} (q : (lift R H).coe.Walk x y),
      H.coe.Reachable (anchor H x) (anchor H y) := by
    intro x y q
    induction q with
    | nil => exact .rfl
    | cons h q ih => exact (anchor_adj_reachable H h).trans ih
  exact hp p

lemma collapse_cycle [Fintype V] (H : (graph G R).Subgraph)
    (hc : H.coe.Connected) (hr : H.coe.IsRegularOfDegree 2) :
    (collapse H).coe.Connected ∧ (collapse H).coe.IsRegularOfDegree 2 := by
  have hn (e : R) (he : Sum.inr e ∈ H.verts) : H.degree (.inr e) = 2 := by
    have hh := hr ⟨.inr e,he⟩
    rw [Subgraph.coe_degree] at hh
    simpa only [Subgraph.degree,← Nat.card_eq_fintype_card] using hh
  have hh := lift_collapse H hn
  refine ⟨connected_of_lift_connected (collapse H) (hh.symm ▸ hc),?_⟩
  intro v
  have hdeg := hr ⟨.inl v.val,v.property⟩
  rw [Subgraph.coe_degree,← Subgraph.degree_spanningCoe] at hdeg
  have hspan : graph (collapse H).spanningCoe R = H.spanningCoe :=
    congrArg Subgraph.spanningCoe hh
  have ho := degree_old (collapse H).spanningCoe R v.val
  rw [Subgraph.coe_degree,← Subgraph.degree_spanningCoe]
  simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hdeg ho ⊢
  rw [hspan] at ho
  exact ho.symm.trans hdeg

lemma new_degree_of_cycle [Fintype V] (H : (graph G R).Subgraph)
    (hr : H.coe.IsRegularOfDegree 2) (e : R) (he : Sum.inr e ∈ H.verts) :
    H.degree (.inr e) = 2 := by
  have hh := hr ⟨.inr e,he⟩
  rw [Subgraph.coe_degree] at hh
  simpa only [Subgraph.degree,← Nat.card_eq_fintype_card] using hh

lemma decomposition_of_lift_decomposition (E : Finset G.Subgraph)
    (hd : IsDecomposition (graph G R) (E.image (lift R))) : IsDecomposition G E := by
  constructor
  · intro H hH K hK hne
    have hl := hd.1 (Finset.mem_image.mpr ⟨H,hH,rfl⟩) (Finset.mem_image.mpr ⟨K,hK,rfl⟩)
      (fun he => hne (lift_injective R he))
    apply Set.disjoint_left.mpr
    intro e heH heK
    induction e using Sym2.ind with
    | h u v =>
      by_cases he : s(u,v) ∈ R
      · have ha : (lift R H).Adj (.inl u) (.inr ⟨s(u,v),he⟩) :=
          ⟨heH,Sym2.mem_mk_left _ _⟩
        have hb : (lift R K).Adj (.inl u) (.inr ⟨s(u,v),he⟩) :=
          ⟨heK,Sym2.mem_mk_left _ _⟩
        exact Set.disjoint_left.mp hl
          (show s(Sum.inl u,Sum.inr ⟨s(u,v),he⟩) ∈ (lift R H).edgeSet from ha) hb
      · exact Set.disjoint_left.mp hl
          (show s(Sum.inl u,Sum.inl v) ∈ (lift R H).edgeSet from ⟨heH,he⟩)
          (show s(Sum.inl u,Sum.inl v) ∈ (lift R K).edgeSet from ⟨heK,he⟩)
  · ext e
    constructor
    · intro he
      obtain ⟨H,_,heH⟩ := Set.mem_iUnion₂.mp he
      exact H.edgeSet_subset heH
    · intro heG
      induction e using Sym2.ind with
      | h u v =>
        by_cases he : s(u,v) ∈ R
        · have hge : s(Sum.inl u,Sum.inr ⟨s(u,v),he⟩) ∈ (graph G R).edgeSet :=
            ⟨heG,Sym2.mem_mk_left _ _⟩
          rw [← hd.2] at hge
          obtain ⟨K,hK,heK⟩ := Set.mem_iUnion₂.mp hge
          obtain ⟨H,hH,rfl⟩ := Finset.mem_image.mp hK
          exact Set.mem_iUnion₂.mpr ⟨H,hH,heK.1⟩
        · have hge : s(Sum.inl u,Sum.inl v) ∈ (graph G R).edgeSet := ⟨heG,he⟩
          rw [← hd.2] at hge
          obtain ⟨K,hK,heK⟩ := Set.mem_iUnion₂.mp hge
          obtain ⟨H,hH,rfl⟩ := Finset.mem_image.mp hK
          exact Set.mem_iUnion₂.mpr ⟨H,hH,heK.1⟩

lemma collapse_decomposition [Fintype V] (D : Finset (graph G R).Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition (graph G R) D) :
    ∃ E : Finset G.Subgraph,
      (∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G E ∧ E.card = D.card := by
  let E := D.image collapse
  have hl : E.image (lift R) = D := by
    ext H
    constructor
    · intro hH
      obtain ⟨K,hK,rfl⟩ := Finset.mem_image.mp hH
      obtain ⟨J,hJ,rfl⟩ := Finset.mem_image.mp hK
      rw [lift_collapse J (new_degree_of_cycle J (hc J hJ).2)]
      exact hJ
    · intro hH
      exact Finset.mem_image.mpr ⟨collapse H,Finset.mem_image.mpr ⟨H,hH,rfl⟩,
        lift_collapse H (new_degree_of_cycle H (hc H hH).2)⟩
  refine ⟨E,?_,decomposition_of_lift_decomposition E (hl.symm ▸ hd),?_⟩
  · intro H hH
    obtain ⟨J,hJ,rfl⟩ := Finset.mem_image.mp hH
    have hh := collapse_cycle J (hc J hJ).1 (hc J hJ).2
    refine ⟨hh.1,?_⟩
    intro v
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hh.2 v
  · have h1 : E.card ≤ D.card := Finset.card_image_le
    have h2 : (E.image (lift R)).card ≤ E.card := Finset.card_image_le
    rw [hl] at h2
    omega

lemma graph_injective (R : Set (Sym2 V)) : Function.Injective (fun G : SimpleGraph V => graph G R) := by
  intro A B h
  ext u v
  by_cases he : s(u,v) ∈ R
  · have hh := congrArg (fun K : SimpleGraph (V ⊕ R) => K.Adj (.inl u) (.inr ⟨s(u,v),he⟩)) h
    change (A.Adj u v ∧ u ∈ s(u,v)) = (B.Adj u v ∧ u ∈ s(u,v)) at hh
    simpa only [Sym2.mem_mk_left,and_true] using iff_of_eq hh
  · have hh := congrArg (fun K : SimpleGraph (V ⊕ R) => K.Adj (.inl u) (.inl v)) h
    change (A.Adj u v ∧ s(u,v) ∉ R) = (B.Adj u v ∧ s(u,v) ∉ R) at hh
    simpa only [he,not_false_eq_true,and_true] using iff_of_eq hh

lemma graph_mono (R : Set (Sym2 V)) {A B : SimpleGraph V} (h : A ≤ B) : graph A R ≤ graph B R := by
  intro x y hxy
  cases x <;> cases y
  · exact ⟨h hxy.1,hxy.2⟩
  · exact ⟨SimpleGraph.edgeSet_mono h hxy.1,hxy.2⟩
  · exact ⟨SimpleGraph.edgeSet_mono h hxy.1,hxy.2⟩
  · exact hxy

lemma graph_even [Fintype V] (G : SimpleGraph V) (R : Set (Sym2 V))
    (he : ∀ v, Even (G.degree v)) : ∀ x, Even ((graph G R).degree x) := by
  intro x
  cases x with
  | inl v =>
    have hd := degree_old G R v
    simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hd ⊢
    rw [hd]
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using he v
  | inr e =>
    by_cases he : e.val ∈ G.edgeSet
    · have hd := degree_new G R e he
      simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hd ⊢
      rw [hd]
      decide
    · have hn : (graph G R).neighborSet (.inr e) = ∅ := by
        ext x
        cases x <;> simp [graph,he,neighborSet]
      simp [← card_neighborSet_eq_degree,hn]

lemma even_of_graph_even [Fintype V] (G : SimpleGraph V) (R : Set (Sym2 V))
    (he : ∀ x, Even ((graph G R).degree x)) : ∀ v, Even (G.degree v) := by
  intro v
  have hd := degree_old G R v
  have hv := he (.inl v)
  simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hd hv ⊢
  rwa [hd] at hv

end Erdos184.EdgeSubdivision
