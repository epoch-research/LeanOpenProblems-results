import Submission.Work

/-! A certificate for safely appending a matching at selected path endpoints.
This module does not prove that the simultaneous avoidance certificate exists. -/
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails
namespace Erdos583MatchingAppendDevelopment
open scoped Classical
set_option maxHeartbeats 1200000

/-- The sources and targets of an oriented matching are disjoint. -/
structure OrientedMatching {V : Type*} (G : SimpleGraph V) where
  sources : Set V
  target : V → V
  injective : Set.InjOn target sources
  target_outside : ∀ a ∈ sources, target a ∉ sources
  adj : ∀ a ∈ sources, G.Adj a (target a)

namespace OrientedMatching

def edges {V : Type*} {G : SimpleGraph V} (M : OrientedMatching G) : Set (Sym2 V) :=
  {e | ∃ a ∈ M.sources, e = s(a,M.target a)}

lemma edge_injective {V : Type*} {G : SimpleGraph V} (M : OrientedMatching G)
    {a b : V} (ha : a ∈ M.sources) (hb : b ∈ M.sources)
    (he : s(a,M.target a)=s(b,M.target b)) : a=b := by
  rcases Sym2.eq_iff.mp he with h | h
  · exact h.1
  · exact (M.target_outside b hb (h.1 ▸ ha)).elim

noncomputable def moved {V : Type*} {G : SimpleGraph V} (M : OrientedMatching G) (a : V) : V :=
  if a ∈ M.sources then M.target a else a

noncomputable def cap {V : Type*} {G : SimpleGraph V} (M : OrientedMatching G) (a : V) :
    G.Walk (M.moved a) a := by
  classical
  by_cases ha : a ∈ M.sources
  · exact (Walk.cons (M.adj a ha).symm Walk.nil).copy (by simp [moved,ha]) rfl
  · exact (Walk.nil : G.Walk a a).copy (by simp [moved,ha]) rfl

lemma cap_edges {V : Type*} {G : SimpleGraph V} (M : OrientedMatching G) (a : V) (e : Sym2 V) :
    e ∈ (M.cap a).toSubgraph.edgeSet ↔ a ∈ M.sources ∧ e=s(a,M.target a) := by
  classical
  by_cases ha : a ∈ M.sources
  · simp [cap,ha,Sym2.eq_swap]
  · simp [cap,ha]

lemma cap_support {V : Type*} {G : SimpleGraph V} (M : OrientedMatching G) (a x : V) :
    x ∈ (M.cap a).support ↔ x=a ∨ a ∈ M.sources ∧ x=M.target a := by
  classical
  by_cases ha : a ∈ M.sources
  · simp [cap,ha,Walk.support_cons,or_comm]
  · simp [cap,ha]

lemma cap_append_isPath {V : Type*} {G : SimpleGraph V} (M : OrientedMatching G)
    {a b : V} (p : G.Walk a b) (hp : p.IsPath)
    (havoid : a ∈ M.sources → M.target a ∉ p.support) :
    ((M.cap a).append p).IsPath := by
  classical
  by_cases ha : a ∈ M.sources
  · have han := havoid ha
    have hpn := hp.support_nodup
    rw [p.support_eq_cons] at han hpn
    have hh : (M.target a :: a :: p.support.tail).Nodup := List.nodup_cons.mpr ⟨han,hpn⟩
    simpa [Walk.isPath_def,Walk.support_append,cap,ha] using hh
  · have hpn := hp.support_nodup
    rw [p.support_eq_cons] at hpn
    simpa [Walk.isPath_def,Walk.support_append,cap,ha] using hpn

noncomputable def decorate {V : Type*} {G : SimpleGraph V} (M : OrientedMatching G)
    {a b : V} (p : G.Walk a b) : G.Walk (M.moved a) (M.moved b) :=
  ((M.cap a).append p).append (M.cap b).reverse

lemma decorate_edges {V : Type*} {G : SimpleGraph V} (M : OrientedMatching G)
    {a b : V} (p : G.Walk a b) (e : Sym2 V) :
    e ∈ (M.decorate p).toSubgraph.edgeSet ↔
      e ∈ p.toSubgraph.edgeSet ∨
      (a ∈ M.sources ∧ e=s(a,M.target a)) ∨ (b ∈ M.sources ∧ e=s(b,M.target b)) := by
  simp only [decorate,Walk.toSubgraph_append,Subgraph.edgeSet_sup,Set.mem_union,
    Walk.toSubgraph_reverse,cap_edges]
  tauto

lemma decorate_isPath {V : Type*} {G : SimpleGraph V} (M : OrientedMatching G)
    {a b : V} (p : G.Walk a b) (hp : p.IsPath) (hab : a ≠ b)
    (ha : a ∈ M.sources → M.target a ∉ p.support)
    (hb : b ∈ M.sources → M.target b ∉ p.support) : (M.decorate p).IsPath := by
  have hleft := M.cap_append_isPath p hp ha
  have hright : b ∈ M.sources → M.target b ∉ ((M.cap a).append p).reverse.support := by
    intro hbs hx
    rw [Walk.support_reverse,List.mem_reverse,Walk.mem_support_append_iff] at hx
    rcases hx with hx | hx
    · rcases (M.cap_support a _).mp hx with hx | ⟨has,hx⟩
      · exact hb hbs (hx ▸ p.start_mem_support)
      · exact hab ((M.injective hbs has hx).symm)
    · exact hb hbs hx
  have hh := (M.cap_append_isPath _ hleft.reverse hright).reverse
  simpa [decorate,Walk.reverse_append] using hh

/-- If every source endpoint avoids its matching partner, all marked edges
can be appended simultaneously, without increasing the number of members. -/
lemma append_to_normal_system {V : Type*} {H G : SimpleGraph V} {k : ℕ}
    (hHG : H ≤ G) (M : OrientedMatching G) (T : NormalTrailSystem H k)
    (hpath : ∀ i, (T.walk i).IsPath)
    (hnew : Disjoint H.edgeSet M.edges)
    (hcover : G.edgeSet=H.edgeSet ∪ M.edges)
    (havoid : ∀ i a, (a=T.start i ∨ a=T.finish i) → a ∈ M.sources →
      M.target a ∉ (T.walk i).support) :
    ∃ U : TrailFamily G k, ∀ i, (U.walk i).IsPath := by
  classical
  let p (i : Fin k) : G.Walk (T.start i) (T.finish i) := (T.walk i).mapLe hHG
  have hp (i : Fin k) : (p i).IsPath := (hpath i).mapLe hHG
  have he (i : Fin k) : (p i).toSubgraph.edgeSet=(T.walk i).toSubgraph.edgeSet := by
    simp [p,Walk.mapLe]
  have hs (i : Fin k) : (p i).support=(T.walk i).support := by simp [p,Walk.mapLe]
  have hdec (i : Fin k) : (M.decorate (p i)).IsPath := by
    apply M.decorate_isPath _ (hp i) (T.endpoints_ne i)
    · intro ha; rw [hs]; exact havoid i _ (Or.inl rfl) ha
    · intro hb; rw [hs]; exact havoid i _ (Or.inr rfl) hb
  have hed (i : Fin k) (e : Sym2 V) : e ∈ (M.decorate (p i)).toSubgraph.edgeSet ↔
      e ∈ (T.walk i).toSubgraph.edgeSet ∨
      ∃ a, (a=T.start i ∨ a=T.finish i) ∧ a ∈ M.sources ∧ e=s(a,M.target a) := by
    rw [M.decorate_edges,he]
    constructor
    · rintro (hh | ⟨ha,he⟩ | ⟨hb,he⟩)
      · exact Or.inl hh
      · exact Or.inr ⟨_,Or.inl rfl,ha,he⟩
      · exact Or.inr ⟨_,Or.inr rfl,hb,he⟩
    · rintro (hh | ⟨a,(rfl | rfl),ha,he⟩)
      · exact Or.inl hh
      · exact Or.inr (Or.inl ⟨ha,he⟩)
      · exact Or.inr (Or.inr ⟨ha,he⟩)
  have hdis : Pairwise fun i j ↦ Disjoint (M.decorate (p i)).toSubgraph.edgeSet
      (M.decorate (p j)).toSubgraph.edgeSet := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro e hei hej
    rcases (hed i e).mp hei with hei | ⟨a,hai,ha,hea⟩ <;>
      rcases (hed j e).mp hej with hej | ⟨b,hbj,hb,heb⟩
    · exact Set.disjoint_left.mp (T.disjoint hij) hei hej
    · exact Set.disjoint_left.mp hnew ((T.walk i).toSubgraph.edgeSet_subset hei) ⟨b,hb,heb⟩
    · exact Set.disjoint_left.mp hnew ((T.walk j).toSubgraph.edgeSet_subset hej) ⟨a,ha,hea⟩
    · have hab : a=b := M.edge_injective ha hb (hea.symm.trans heb)
      have hi := (T.endpoint_iff_owner a i).mp hai
      have hj := (T.endpoint_iff_owner b j).mp hbj
      exact hij (hi.symm.trans (hab ▸ hj))
  have hc (e : Sym2 V) : e ∈ G.edgeSet ↔ ∃ i, e ∈ (M.decorate (p i)).toSubgraph.edgeSet := by
    rw [hcover,Set.mem_union]
    constructor
    · rintro (heH | ⟨a,ha,heM⟩)
      · obtain ⟨i,hi⟩ := (T.cover e).mp heH
        exact ⟨i,(hed i e).mpr (Or.inl hi)⟩
      · exact ⟨T.owner a,(hed _ e).mpr (Or.inr ⟨a,T.owner_spec a,ha,heM⟩)⟩
    · rintro ⟨i,hi⟩
      rcases (hed i e).mp hi with hh | ⟨a,_,ha,he⟩
      · exact Or.inl ((T.walk i).toSubgraph.edgeSet_subset hh)
      · exact Or.inr ⟨a,ha,he⟩
  exact ⟨⟨fun i ↦ M.moved (T.start i),fun i ↦ M.moved (T.finish i),
    fun i ↦ M.decorate (p i),fun i ↦ (hdec i).isTrail,hdis,hc⟩,hdec⟩

end OrientedMatching

lemma path_family_partition {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (hp : ∀ i, (T.walk i).IsPath) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ k := by
  classical
  let D := Finset.univ.image (fun i ↦ (T.walk i).toSubgraph)
  refine ⟨D,⟨?_,?_,?_⟩,?_⟩
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
  · exact (Finset.card_image_le).trans (by simp)

/-- The endpoint-avoidance certificate implies a matching-addition bound.
The simultaneous existence of this certificate is not asserted here. -/
lemma matching_append_certificate {V : Type*} [Fintype V] {H G : SimpleGraph V} {k : ℕ}
    (hHG : H ≤ G) (M : OrientedMatching G) (T : NormalTrailSystem H k)
    (hpath : ∀ i, (T.walk i).IsPath)
    (hnew : Disjoint H.edgeSet M.edges) (hcover : G.edgeSet=H.edgeSet ∪ M.edges)
    (havoid : ∀ i a, (a=T.start i ∨ a=T.finish i) → a ∈ M.sources →
      M.target a ∉ (T.walk i).support) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ 2*D.card ≤ Fintype.card V := by
  obtain ⟨U,hU⟩ := M.append_to_normal_system hHG T hpath hnew hcover havoid
  obtain ⟨D,hD,hcard⟩ := path_family_partition U hU
  exact ⟨D,hD,by have hh := T.twice_card; omega⟩

end Erdos583MatchingAppendDevelopment
