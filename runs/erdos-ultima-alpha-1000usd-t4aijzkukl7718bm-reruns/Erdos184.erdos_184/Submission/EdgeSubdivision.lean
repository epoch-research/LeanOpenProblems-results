import Submission.SingleFiberProjection

/-!
Subdividing a selected set of edges, with an exact transport of pure-cycle
decompositions. This is auxiliary infrastructure for vertex smoothing.
-/
open SimpleGraph
open scoped Classical
namespace Erdos184
namespace EdgeSubdivision

variable {V : Type*}

/-- The extra vertex for a selected edge is isolated if that edge is absent
from `A`. This convention lets all subgraphs use the same ambient type. -/
def graph (A : SimpleGraph V) (R : Set (Sym2 V)) : SimpleGraph (V ⊕ R) where
  Adj
    | .inl u, .inl v => A.Adj u v ∧ s(u,v) ∉ R
    | .inl u, .inr e => e.val ∈ A.edgeSet ∧ u ∈ e.val
    | .inr e, .inl v => e.val ∈ A.edgeSet ∧ v ∈ e.val
    | .inr _, .inr _ => False
  symm := by
    intro x y h
    cases x <;> cases y
    · exact ⟨h.1.symm, by simpa only [Sym2.eq_swap] using h.2⟩
    · exact h
    · exact h
    · exact h
  loopless := by
    intro x
    cases x
    · exact fun h => A.loopless _ h.1
    · exact id

/-- Expand a subgraph in the common subdivided ambient graph. -/
def lift {G : SimpleGraph V} (R : Set (Sym2 V)) (H : G.Subgraph) :
    (graph G R).Subgraph where
  verts x := match x with
    | .inl v => v ∈ H.verts
    | .inr e => e.val ∈ H.edgeSet
  Adj := (graph H.spanningCoe R).Adj
  symm := (graph H.spanningCoe R).symm
  adj_sub := by
    intro x y h
    cases x <;> cases y
    · exact ⟨H.adj_sub h.1,h.2⟩
    · exact ⟨H.edgeSet_subset h.1,h.2⟩
    · exact ⟨H.edgeSet_subset h.1,h.2⟩
    · exact h
  edge_vert := by
    intro x y h
    cases x <;> cases y
    · exact H.edge_vert h.1
    · exact Subgraph.mem_verts_of_mem_edge h.1 h.2
    · exact h.1
    · exact h.elim

@[simp] lemma lift_spanningCoe {G : SimpleGraph V} (R : Set (Sym2 V))
    (H : G.Subgraph) : (lift R H).spanningCoe = graph H.spanningCoe R := rfl

lemma lift_injective {G : SimpleGraph V} (R : Set (Sym2 V)) :
    Function.Injective (lift (G := G) R) := by
  intro H K h
  apply Subgraph.ext
  · ext v
    exact Set.ext_iff.mp (congrArg Subgraph.verts h) (.inl v)
  · funext u v
    apply propext
    by_cases he : s(u,v) ∈ R
    · have hh := Set.ext_iff.mp (congrArg Subgraph.verts h) (.inr ⟨s(u,v),he⟩)
      exact hh
    · have hh := congrFun (congrFun (congrArg Subgraph.Adj h) (.inl u)) (.inl v)
      change (H.Adj u v ∧ s(u,v) ∉ R) = (K.Adj u v ∧ s(u,v) ∉ R) at hh
      simpa only [he,not_false_eq_true,and_true] using (iff_of_eq hh)

/-- Each old neighbor is replaced either by itself or by its edge vertex. -/
noncomputable def neighborMap (A : SimpleGraph V) (R : Set (Sym2 V)) (v : V) :
    A.neighborSet v → (graph A R).neighborSet (.inl v) := fun x =>
  if h : s(v,x.val) ∈ R then
    ⟨.inr ⟨s(v,x.val),h⟩, x.property, Sym2.mem_mk_left _ _⟩
  else ⟨.inl x.val, x.property, h⟩

lemma neighborMap_bijective (A : SimpleGraph V) (R : Set (Sym2 V)) (v : V) :
    Function.Bijective (neighborMap A R v) := by
  constructor
  · intro x y h
    apply Subtype.ext
    have hh := congrArg Subtype.val h
    simp only [neighborMap] at hh
    by_cases hx : s(v,x.val) ∈ R <;> by_cases hy : s(v,y.val) ∈ R
    · simp only [dif_pos hx,dif_pos hy] at hh
      have he := congrArg Subtype.val (Sum.inr.inj hh)
      rcases Sym2.eq_iff.mp he with h | h
      · exact h.2
      · exact h.2.trans h.1
    · simp only [dif_pos hx,dif_neg hy] at hh
      cases hh
    · simp only [dif_neg hx,dif_pos hy] at hh
      cases hh
    · simp only [dif_neg hx,dif_neg hy] at hh
      exact Sum.inl.inj hh
  · rintro ⟨x,hx⟩
    cases x with
    | inl x =>
      refine ⟨⟨x,hx.1⟩,?_⟩
      apply Subtype.ext
      simp [neighborMap,hx.2]
    | inr e =>
      obtain ⟨u,hu⟩ := Sym2.mem_iff_exists.mp hx.2
      have hvu : A.Adj v u := by
        change s(v,u) ∈ A.edgeSet
        rw [← hu]
        exact hx.1
      have he : s(v,u) ∈ R := hu ▸ e.property
      refine ⟨⟨u,hvu⟩,?_⟩
      apply Subtype.ext
      simp only [neighborMap,dif_pos he]
      congr 1
      exact Subtype.ext hu.symm

lemma degree_old [Fintype V] (A : SimpleGraph V) (R : Set (Sym2 V)) (v : V) :
    (graph A R).degree (.inl v) = A.degree v := by
  simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
  exact (Nat.card_congr (Equiv.ofBijective (neighborMap A R v)
    (neighborMap_bijective A R v))).symm

lemma degree_new [Fintype V] (A : SimpleGraph V) (R : Set (Sym2 V))
    (e : R) (he : e.val ∈ A.edgeSet) : (graph A R).degree (.inr e) = 2 := by
  have hs : (graph A R).neighborFinset (.inr e) =
      e.val.toFinset.map Function.Embedding.inl := by
    ext x
    cases x with
    | inl v => simp [graph,he,Sym2.mem_toFinset]
    | inr d => simp [graph]
  rw [degree,hs,Finset.card_map]
  exact Sym2.card_toFinset_of_not_isDiag e.val (A.not_isDiag_of_mem_edgeSet he)

/-- Old adjacency becomes a path with one or two edges. -/
lemma old_reachable {G : SimpleGraph V} (R : Set (Sym2 V)) (H : G.Subgraph)
    {u v : H.verts} (h : H.coe.Adj u v) :
    (lift R H).coe.Reachable ⟨.inl u.val,u.property⟩ ⟨.inl v.val,v.property⟩ := by
  by_cases he : s(u.val,v.val) ∈ R
  · let e : R := ⟨s(u.val,v.val),he⟩
    let z : (lift R H).verts := ⟨.inr e,h⟩
    have h1 : (lift R H).coe.Adj ⟨.inl u.val,u.property⟩ z :=
      ⟨h,Sym2.mem_mk_left _ _⟩
    have h2 : (lift R H).coe.Adj z ⟨.inl v.val,v.property⟩ :=
      ⟨h,Sym2.mem_mk_right _ _⟩
    exact h1.reachable.trans h2.reachable
  · exact (show (lift R H).coe.Adj ⟨.inl u.val,u.property⟩
      ⟨.inl v.val,v.property⟩ from ⟨h,he⟩).reachable

lemma lift_connected {G : SimpleGraph V} (R : Set (Sym2 V))
    (H : G.Subgraph) (hc : H.coe.Connected) : (lift R H).coe.Connected := by
  have hpath : ∀ {u v : H.verts}, H.coe.Reachable u v →
      (lift R H).coe.Reachable ⟨.inl u.val,u.property⟩ ⟨.inl v.val,v.property⟩ := by
    rintro u v ⟨p⟩
    induction p with
    | nil => exact .rfl
    | cons h p ih => exact (old_reachable R H h).trans ih
  have hanchor : ∀ x : (lift R H).verts, ∃ u : H.verts,
      (lift R H).coe.Reachable ⟨.inl u.val,u.property⟩ x := by
    rintro ⟨x,hx⟩
    cases x with
    | inl v => exact ⟨⟨v,hx⟩,.rfl⟩
    | inr e =>
      obtain ⟨⟨u,v⟩,he⟩ := Sym2.mk_surjective e.val
      have heH : s(u,v) ∈ H.edgeSet := he.symm ▸ hx
      refine ⟨⟨u,H.edge_vert heH⟩,?_⟩
      have hu : u ∈ e.val := by rw [← he]; exact Sym2.mem_mk_left _ _
      exact (show (lift R H).coe.Adj ⟨.inl u,H.edge_vert heH⟩ ⟨.inr e,hx⟩
        from ⟨hx,hu⟩).reachable
  haveI : Nonempty (lift R H).verts := by
    obtain ⟨v⟩ := hc.nonempty
    exact ⟨⟨.inl v.val,v.property⟩⟩
  refine ⟨fun x y => ?_⟩
  obtain ⟨u,hu⟩ := hanchor x
  obtain ⟨v,hv⟩ := hanchor y
  exact hu.symm.trans ((hpath (hc u v)).trans hv)

lemma lift_regular_two [Fintype V] {G : SimpleGraph V} (R : Set (Sym2 V))
    (H : G.Subgraph) (hr : H.coe.IsRegularOfDegree 2) :
    (lift R H).coe.IsRegularOfDegree 2 := by
  rintro ⟨x,hx⟩
  rw [Subgraph.coe_degree,← Subgraph.degree_spanningCoe, lift_spanningCoe]
  cases x with
  | inl v =>
    have h := hr ⟨v,hx⟩
    rw [Subgraph.coe_degree,← Subgraph.degree_spanningCoe] at h
    have hh := degree_old H.spanningCoe R v
    simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at h hh ⊢
    exact hh.trans h
  | inr e =>
    have h := degree_new H.spanningCoe R e hx
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using h

/-- Subdivision transports an edge partition to an edge partition. -/
lemma lift_decomposition {G : SimpleGraph V} (R : Set (Sym2 V))
    (D : Finset G.Subgraph) (hd : IsDecomposition G D) :
    IsDecomposition (graph G R) (D.image (lift R)) := by
  constructor
  · intro H hH K hK hHK
    obtain ⟨A,hA,rfl⟩ := Finset.mem_image.mp hH
    obtain ⟨B,hB,rfl⟩ := Finset.mem_image.mp hK
    have hab := hd.1 hA hB (fun h => hHK (congrArg (lift R) h))
    apply Set.disjoint_left.mpr
    intro e heA heB
    induction e using Sym2.ind with
    | h x y =>
      cases x <;> cases y
      case inl.inl x y =>
        exact Set.disjoint_left.mp hab (show s(x,y) ∈ A.edgeSet from heA.1) heB.1
      case inl.inr x d => exact Set.disjoint_left.mp hab heA.1 heB.1
      case inr.inl d y => exact Set.disjoint_left.mp hab heA.1 heB.1
      case inr.inr d e => exact heA.elim
  · ext e
    constructor
    · rintro h
      obtain ⟨H,hH,heH⟩ := Set.mem_iUnion₂.mp h
      exact H.edgeSet_subset heH
    · intro he
      induction e using Sym2.ind with
      | h x y =>
        cases x with
        | inl x =>
          cases y with
          | inl y =>
            have hxy : s(x,y) ∈ G.edgeSet := he.1
            rw [← hd.2] at hxy
            obtain ⟨H,hH,heH⟩ := Set.mem_iUnion₂.mp hxy
            exact Set.mem_iUnion₂.mpr ⟨lift R H,Finset.mem_image.mpr ⟨H,hH,rfl⟩,
              show (lift R H).Adj (.inl x) (.inl y) from ⟨heH,he.2⟩⟩
          | inr d =>
            have hdG : d.val ∈ G.edgeSet := he.1
            rw [← hd.2] at hdG
            obtain ⟨H,hH,hdH⟩ := Set.mem_iUnion₂.mp hdG
            exact Set.mem_iUnion₂.mpr ⟨lift R H,Finset.mem_image.mpr ⟨H,hH,rfl⟩,
              show (lift R H).Adj (.inl x) (.inr d) from ⟨hdH,he.2⟩⟩
        | inr d =>
          cases y with
          | inl y =>
            have hdG : d.val ∈ G.edgeSet := he.1
            rw [← hd.2] at hdG
            obtain ⟨H,hH,hdH⟩ := Set.mem_iUnion₂.mp hdG
            exact Set.mem_iUnion₂.mpr ⟨lift R H,Finset.mem_image.mpr ⟨H,hH,rfl⟩,
              show (lift R H).Adj (.inr d) (.inl y) from ⟨hdH,he.2⟩⟩
          | inr e => exact he.elim

lemma lift_card {G : SimpleGraph V} (R : Set (Sym2 V)) (D : Finset G.Subgraph) :
    (D.image (lift R)).card = D.card :=
  Finset.card_image_of_injective D (lift_injective R)

lemma lift_meets_new_iff {G : SimpleGraph V} (R : Set (Sym2 V)) (H : G.Subgraph) :
    (∃ e : R, Sum.inr e ∈ (lift R H).verts) ↔ (H.edgeSet ∩ R).Nonempty := by
  constructor
  · rintro ⟨e,he⟩
    exact ⟨e.val,he,e.property⟩
  · rintro ⟨e,he,heR⟩
    exact ⟨⟨e,heR⟩,he⟩

lemma lift_marked_card {G : SimpleGraph V} (R : Set (Sym2 V)) (D : Finset G.Subgraph) :
    ((D.image (lift R)).filter (fun H => ∃ e : R, Sum.inr e ∈ H.verts)).card =
      (D.filter (fun H => (H.edgeSet ∩ R).Nonempty)).card := by
  have heq : (D.image (lift R)).filter (fun H => ∃ e : R, Sum.inr e ∈ H.verts) =
      (D.filter (fun H => (H.edgeSet ∩ R).Nonempty)).image (lift R) := by
    ext H
    simp only [Finset.mem_filter,Finset.mem_image]
    constructor
    · rintro ⟨⟨K,hK,rfl⟩,hm⟩
      exact ⟨K,⟨hK,(lift_meets_new_iff R K).mp hm⟩,rfl⟩
    · rintro ⟨K,⟨hK,hm⟩,rfl⟩
      exact ⟨⟨K,hK,rfl⟩,(lift_meets_new_iff R K).mpr hm⟩
  rw [heq,lift_card]

set_option maxHeartbeats 800000 in
/-- Every pure-cycle decomposition lifts without changing either its size or
the number of pieces meeting the selected edges. -/
lemma transport_decomposition [Fintype V] {G : SimpleGraph V}
    (R : Set (Sym2 V)) (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D) :
    ∃ E : Finset (graph G R).Subgraph,
      (∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition (graph G R) E ∧ E.card = D.card ∧
      (E.filter (fun H => ∃ e : R, Sum.inr e ∈ H.verts)).card =
        (D.filter (fun H => (H.edgeSet ∩ R).Nonempty)).card := by
  refine ⟨D.image (lift R),?_,lift_decomposition R D hd,lift_card R D,?_⟩
  · intro H hH
    obtain ⟨K,hK,rfl⟩ := Finset.mem_image.mp hH
    exact ⟨lift_connected R K (hc K hK).1,lift_regular_two R K (hc K hK).2⟩
  · convert lift_marked_card R D using 1
    congr 1
    ext H
    simp only [Finset.mem_filter]

end EdgeSubdivision
end Erdos184
