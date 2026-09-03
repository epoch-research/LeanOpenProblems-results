import Submission.Work

/-! Canonical core orientations for singleton-token rotations. -/
open SimpleGraph Erdos583Work
open Erdos583Work.TrailNormalization Erdos583Work.PendantCompletion
open Erdos583Work.LeafPermutation Erdos583Work.SingletonRotation
open Erdos583Work.EulerianPermutation
namespace Erdos583CanonicalRotationDevelopment
open scoped Classical
set_option maxHeartbeats 1200000

lemma projection_mem_iff {V : Type*} [Fintype V] {G : SimpleGraph V} {S : Set V} {k : ℕ}
    (T : NormalTrailSystem (leafCompletion G S) k) {D : Finset G.Subgraph}
    (hD : GoodDecomposition G D) (hne : ∀ H ∈ D, H.edgeSet.Nonempty)
    (htrack : ∀ H ∈ D, ∃ i, H = (projectWalk (T.walk i)).toSubgraph) (i : Fin k) :
    (projectWalk (T.walk i)).toSubgraph ∈ D ↔ ¬(projectWalk (T.walk i)).Nil := by
  constructor
  · intro hi hn
    obtain ⟨e,he⟩ := hne _ hi
    have hh := (projectWalk (T.walk i)).mem_edges_toSubgraph.mp he
    rw [Walk.edges_eq_nil.mpr hn] at hh
    exact List.not_mem_nil hh
  · intro hn
    let e := s(root (T.start i),(projectWalk (T.walk i)).snd)
    have he : e ∈ (projectWalk (T.walk i)).toSubgraph.edgeSet :=
      (projectWalk (T.walk i)).toSubgraph_adj_snd hn
    have heG := (projectWalk (T.walk i)).toSubgraph.edgeSet_subset he
    rw [← hD.2.2] at heG
    obtain ⟨H,hH,heH⟩ := Set.mem_iUnion₂.mp heG
    obtain ⟨j,rfl⟩ := htrack H hH
    have hij : i=j := by
      by_contra hh
      exact Set.disjoint_left.mp (T.disjoint hh)
        ((project_edgeSet _ _).mp he) ((project_edgeSet _ _).mp heH)
    rw [hij]
    exact hH

lemma leaf_to_core_path {V : Type*} {G : SimpleGraph V} (z : V)
    (p : (allLeafCompletion G).Walk (Sum.inr ⟨z,Set.mem_univ _⟩) (Sum.inl z))
    (hp : p.IsPath) : p.toSubgraph = leafPart G z := by
  cases p with
  | @cons a w b h q =>
    have hh := (Walk.cons_isPath_iff h q).mp hp
    cases w with
    | inr w => exact h.elim
    | inl w =>
      have hw : z = w := h
      subst w
      have he : q = Walk.nil := (Walk.isPath_iff_eq_nil _).mp hh.1
      subst q
      ext <;> simp [leafPart,leafWalk,inclusion,Walk.concat,Walk.toSubgraph,or_comm,and_comm]

lemma own_leaf_purified {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : NormalTrailSystem (allLeafCompletion G) k) (hp : ∀ i, (T.walk i).IsPath) (z : V) :
    NormalTrailSystem.owner T (Sum.inl z) =
        NormalTrailSystem.owner T (Sum.inr ⟨z,Set.mem_univ _⟩) ↔ z ∈ purified T := by
  constructor
  · intro he
    let i := NormalTrailSystem.owner T (Sum.inl z)
    have hc := NormalTrailSystem.owner_spec T (Sum.inl z)
    have hl := NormalTrailSystem.owner_spec T (Sum.inr ⟨z,Set.mem_univ _⟩)
    rw [←he] at hl
    change Sum.inl z = T.start i ∨ Sum.inl z = T.finish i at hc
    change Sum.inr ⟨z,Set.mem_univ _⟩ = T.start i ∨
      Sum.inr ⟨z,Set.mem_univ _⟩ = T.finish i at hl
    apply (mem_purified T z).mpr
    refine ⟨i,?_⟩
    rcases hc with hc | hc <;> rcases hl with hl | hl
    · exact (Sum.inl_ne_inr (hc.trans hl.symm)).elim
    · have hh := leaf_to_core_path z ((T.walk i).reverse.copy hl.symm hc.symm)
        (by simpa using (hp i).reverse)
      simpa only [NormalTrailSystem.walk_copy_subgraph,Walk.toSubgraph_reverse] using hh
    · have hh := leaf_to_core_path z ((T.walk i).copy hl.symm hc.symm) (by simpa using hp i)
      simpa only [NormalTrailSystem.walk_copy_subgraph] using hh
    · exact (Sum.inl_ne_inr (hc.trans hl.symm)).elim
  · intro hz
    obtain ⟨i,hi⟩ := (mem_purified T z).mp hz
    obtain ⟨hc,hl⟩ := leafPart_owners T i z hi
    exact hc.trans hl.symm

lemma inactive_projection_eq_purified {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : NormalTrailSystem (allLeafCompletion G) k) (hp : ∀ i, (T.walk i).IsPath)
    {D : Finset G.Subgraph} (hD : GoodDecomposition G D)
    (hne : ∀ H ∈ D, H.edgeSet.Nonempty)
    (htrack : ∀ H ∈ D, ∃ i, H = (projectWalk (T.walk i)).toSubgraph) :
    inactive D = purified T := by
  classical
  ext z
  constructor
  · intro hz
    have hzero : endpointMultiplicity D z = 0 := (Finset.mem_filter.mp hz).2
    let i := NormalTrailSystem.owner T (Sum.inl z)
    have hc : Sum.inl z = T.start i ∨ Sum.inl z = T.finish i :=
      NormalTrailSystem.owner_spec T (Sum.inl z)
    have hn : (projectWalk (T.walk i)).Nil := by
      by_contra hn
      have hmem := (projection_mem_iff T hD hne htrack i).mpr hn
      have hdeg : ((projectWalk (T.walk i)).toSubgraph.neighborSet z).ncard = 1 := by
        apply (EndpointSelection.path_neighbor_one_iff (project_path_support _ (hp i)).1 hn z).mpr
        rcases hc with hh | hh
        · exact Or.inl (by rw [←hh]; rfl)
        · exact Or.inr (by rw [←hh]; rfl)
      have hpos : 0 < endpointMultiplicity D z :=
        Finset.card_pos.mpr ⟨_,Finset.mem_filter.mpr ⟨hmem,hdeg⟩⟩
      omega
    have he := (project_nil_iff _ (hp i)).mp hn
    have hneends : T.start i ≠ T.finish i := by
      intro hh
      have heq := T.endpoint_bijective.1 (a₁ := (i,true)) (a₂ := (i,false)) (show
        (if true then T.start i else T.finish i) =
        (if false then T.start i else T.finish i) from hh)
      exact Bool.noConfusion (congrArg Prod.snd heq)
    have hl : Sum.inr ⟨z,Set.mem_univ _⟩ = T.start i ∨
        Sum.inr ⟨z,Set.mem_univ _⟩ = T.finish i := by
      rcases hc with hc | hc
      · right
        rw [←hc] at he hneends
        cases hb : T.finish i with
        | inl w =>
          rw [hb] at he hneends
          exact (hneends (congrArg Sum.inl he)).elim
        | inr w =>
          rw [hb] at he
          exact congrArg Sum.inr (Subtype.ext he)
      · left
        rw [←hc] at he hneends
        cases ha : T.start i with
        | inl w =>
          rw [ha] at he hneends
          exact (hneends (congrArg Sum.inl he)).elim
        | inr w =>
          rw [ha] at he
          exact congrArg Sum.inr (Subtype.ext he.symm)
    apply (own_leaf_purified T hp z).mp
    exact ((NormalTrailSystem.endpoint_iff_owner T _ i).mp hl).symm
  · intro hz
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    exact EndpointSelection.projection_inactive_of_owner_eq T hp hne htrack
      ⟨z,Set.mem_univ _⟩ ((own_leaf_purified T hp z).mpr hz)

lemma core_leaf_path_eq {V : Type*} {G : SimpleGraph V} {a : V}
    {b : (Set.univ : Set V)}
    (p : (allLeafCompletion G).Walk (Sum.inl a) (Sum.inr b)) (hp : p.IsPath) :
    p = leafWalk (projectWalk p) := by
  generalize hn : p.length = n
  induction n using Nat.strong_induction_on generalizing a with
  | h n ih =>
    cases p with
    | @cons x w y h q =>
      have hqp := (Walk.cons_isPath_iff h q).mp hp
      cases w with
      | inl c =>
        have hq := ih q.length (by simp only [Walk.length_cons] at hn; omega) q hqp.1 rfl
        simpa only [leafWalk,projectWalk,Walk.map_cons,Walk.concat_cons,inclusion] using
          congrArg (Walk.cons h) hq
      | inr c =>
        have hac : a = c.val := h
        have hnil : q.Nil := by
          by_contra hnil
          exact hqp.2 (hac.symm ▸ leaf_first q hnil)
        cases hnil
        cases hac
        rfl

lemma project_copy_heq {V : Type*} {G : SimpleGraph V} {S : Set V}
    {a b c d : V ⊕ S} (p : (leafCompletion G S).Walk a b) (ha : a=c) (hb : b=d) :
    HEq (projectWalk (p.copy ha hb)) (projectWalk p) := by
  subst c d
  rfl

lemma lift_permutation_exact {V : Type*} [Fintype V] {G : SimpleGraph V}
    (P : PermutationPathSystem G) :
    ∃ T : NormalTrailSystem (allLeafCompletion G) (Fintype.card V),
      (∀ i, (T.walk i).IsPath) ∧ purified T = P.fixed ∧
      ∃ e : Fin (Fintype.card V) ≃ V,
        (∀ i, T.start i = Sum.inl (e i)) ∧
        (∀ i, T.finish i = Sum.inr ⟨P.perm (e i),Set.mem_univ _⟩) ∧
        ∀ i, (T.walk i).toSubgraph = (leafWalk (P.walk (e i))).toSubgraph := by
  classical
  obtain ⟨T,hp,_,e,ha,hb,hproj,_⟩ := lift_permutation_system P
  refine ⟨T,hp,?_,e,ha,hb,?_⟩
  · ext v
    simp only [PermutationPathSystem.fixed,Finset.mem_filter,Finset.mem_univ,true_and]
    exact (own_leaf_purified T hp v).symm.trans (same_owner_iff_fixed P T e ha hb v)
  · intro i
    let q := (T.walk i).copy (ha i) (hb i)
    have hq : q.IsPath := by simpa only [q,Walk.isPath_copy] using hp i
    have hproj' : projectWalk q = P.walk (e i) :=
      eq_of_heq ((project_copy_heq (T.walk i) (ha i) (hb i)).trans (hproj i))
    have he := core_leaf_path_eq q hq
    rw [hproj'] at he
    have hh := congrArg Walk.toSubgraph he
    simpa only [q,NormalTrailSystem.walk_copy_subgraph] using hh

lemma single_edge_endpoints {V : Type*} [Fintype V] {G : SimpleGraph V}
    {a b u v : V} (h : G.Adj a b) (p : G.Walk u v) (hp : p.IsPath)
    (he : p.toSubgraph = G.subgraphOfAdj h) :
    (u=a ∧ v=b) ∨ (u=b ∧ v=a) := by
  have hn : ¬p.Nil := by
    intro hn
    have hh : s(a,b) ∈ p.toSubgraph.edgeSet := by rw [he,G.edgeSet_subgraphOfAdj]; exact Set.mem_singleton _
    have hh' := p.mem_edges_toSubgraph.mp hh
    rw [Walk.edges_eq_nil.mpr hn] at hh'
    exact List.not_mem_nil hh'
  have hp' : (Walk.cons h Walk.nil).IsPath := by simp [h.ne]
  have hends (x : V) (hx : x=a ∨ x=b) : x=u ∨ x=v := by
    apply (EndpointSelection.path_neighbor_one_iff hp hn x).mp
    rw [he]
    exact by simpa using (EndpointSelection.path_neighbor_one_iff hp' (by simp) x).mpr hx
  have ha := hends a (Or.inl rfl)
  have hb := hends b (Or.inr rfl)
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · exact (h.ne (ha.trans hb.symm)).elim
  · exact Or.inl ⟨ha.symm,hb.symm⟩
  · exact Or.inr ⟨hb.symm,ha.symm⟩
  · exact (h.ne (ha.trans hb.symm)).elim

open Erdos583Work.EulerianPermutation.PermutationPathSystem

def reversed {V : Type*} {G : SimpleGraph V} (P : PermutationPathSystem G) :
    PermutationPathSystem G where
  perm := P.perm.symm
  walk v := (P.walk (P.perm.symm v)).reverse.copy (P.perm.apply_symm_apply v) rfl
  isPath v := by simpa only [Walk.isPath_copy] using (P.isPath (P.perm.symm v)).reverse
  disjoint := by
    intro v w hvw
    simp only [NormalTrailSystem.walk_copy_subgraph,Walk.toSubgraph_reverse]
    exact P.disjoint (fun hh ↦ hvw (P.perm.symm.injective hh))
  cover := by
    intro e
    simp only [NormalTrailSystem.walk_copy_subgraph,Walk.toSubgraph_reverse]
    constructor
    · intro he
      obtain ⟨v,hv⟩ := (P.cover e).mp he
      refine ⟨P.perm v,?_⟩
      rw [Equiv.symm_apply_apply]
      exact hv
    · rintro ⟨v,hv⟩
      exact (P.cover e).mpr ⟨P.perm.symm v,hv⟩

lemma reversed_subgraph {V : Type*} {G : SimpleGraph V}
    (P : PermutationPathSystem G) (v : V) :
    ((reversed P).walk v).toSubgraph = (P.walk (P.perm.symm v)).toSubgraph := by
  simp only [reversed,NormalTrailSystem.walk_copy_subgraph,Walk.toSubgraph_reverse]

lemma reversed_fixed {V : Type*} [Fintype V] {G : SimpleGraph V}
    (P : PermutationPathSystem G) : (reversed P).fixed = P.fixed := by
  classical
  ext v
  simp only [fixed,Finset.mem_filter,Finset.mem_univ,true_and]
  change P.perm.symm v = v ↔ P.perm v = v
  rw [P.perm.symm_apply_eq]
  exact eq_comm

lemma reversed_parts {V : Type*} [Fintype V] {G : SimpleGraph V}
    (P : PermutationPathSystem G) : (reversed P).parts = P.parts := by
  classical
  ext H
  simp only [parts,Finset.mem_image,moved,Finset.mem_filter,Finset.mem_univ,true_and,
    reversed_subgraph]
  constructor
  · rintro ⟨v,hv,he⟩
    refine ⟨P.perm.symm v,?_,he⟩
    change P.perm.symm v ≠ v at hv
    simpa only [Equiv.apply_symm_apply,ne_comm] using hv
  · rintro ⟨v,hv,he⟩
    refine ⟨P.perm v,?_,?_⟩
    · change P.perm.symm (P.perm v) ≠ P.perm v
      simpa only [Equiv.symm_apply_apply,ne_comm] using hv
    · rw [Equiv.symm_apply_apply]
      exact he


lemma permutation_of_normal_oriented {V : Type*} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {D : Finset G.Subgraph} (hD : GoodDecomposition G D)
    (hne : ∀ H ∈ D, H.edgeSet.Nonempty) (hb : ∀ v, endpointMultiplicity D v ≤ 2)
    (heven : ∀ v, Even (G.degree v)) {a b : V} (h : G.Adj a b)
    (hmem : G.subgraphOfAdj h ∈ D) :
    ∃ P : PermutationPathSystem G, P.fixed = inactive D ∧ P.parts = D ∧
      P.perm a = b ∧ (P.walk a).toSubgraph = G.subgraphOfAdj h := by
  classical
  obtain ⟨P,hfix,hparts⟩ := permutation_of_normal hD hne hb heven
  have hparts' : P.parts = D := hparts.symm
  have hfixed : P.fixed = inactive D := by
    ext v
    simpa only [PermutationPathSystem.fixed,Finset.mem_filter,Finset.mem_univ,true_and] using hfix v
  obtain ⟨v,_,hv⟩ := Finset.mem_image.mp (hparts'.symm ▸ hmem)
  obtain ⟨hva,hvb⟩ | ⟨hvb,hva⟩ := single_edge_endpoints h (P.walk v) (P.isPath v) hv
  · subst v
    exact ⟨P,hfixed,hparts',hvb,hv⟩
  · subst v
    refine ⟨(reversed P),(reversed_fixed P).trans hfixed,(reversed_parts P).trans hparts',?_,?_⟩
    · change P.perm.symm a = b
      exact P.perm.symm_apply_eq.mpr hva.symm
    · rw [reversed_subgraph P,show P.perm.symm a = b from P.perm.symm_apply_eq.mpr hva.symm]
      exact hv

lemma leafWalk_subgraph {V : Type*} {G : SimpleGraph V} {a b : V} (p : G.Walk a b) :
    (leafWalk p).toSubgraph =
      p.toSubgraph.map (inclusion G Set.univ) ⊔
        (allLeafCompletion G).subgraphOfAdj
          (show (allLeafCompletion G).Adj (Sum.inl b) (Sum.inr ⟨b,Set.mem_univ _⟩) from rfl) := by
  simp [leafWalk,Walk.concat,Walk.toSubgraph_append,Walk.toSubgraph_map]

lemma walk_subgraph_eq_of_edges {V : Type*} {G : SimpleGraph V} {a b c d : V}
    (p : G.Walk a b) (q : G.Walk c d) (hp : ¬p.Nil) (hq : ¬q.Nil)
    (he : p.toSubgraph.edgeSet = q.toSubgraph.edgeSet) : p.toSubgraph = q.toSubgraph := by
  ext x y
  · simp only [Walk.mem_verts_toSubgraph,Walk.mem_support_iff_exists_mem_edges_of_not_nil hp,
      Walk.mem_support_iff_exists_mem_edges_of_not_nil hq,← Walk.mem_edges_toSubgraph,he]
  · change s(x,y) ∈ p.toSubgraph.edgeSet ↔ s(x,y) ∈ q.toSubgraph.edgeSet
    rw [he]

lemma project_short_subgraph {V : Type*} {G : SimpleGraph V} {a b : V}
    {u v : V ⊕ (Set.univ : Set V)} (p : (allLeafCompletion G).Walk u v) (h : G.Adj a b)
    (he : p.toSubgraph = (leafWalk (Walk.cons h Walk.nil)).toSubgraph) :
    (projectWalk p).toSubgraph = G.subgraphOfAdj h := by
  have he' : (projectWalk p).toSubgraph.edgeSet = (Walk.cons h Walk.nil).toSubgraph.edgeSet := by
    ext e
    rw [project_edgeSet,he,← project_edgeSet,leafWalk_project]
  have hp : ¬(projectWalk p).Nil := by
    intro hn
    have hh : s(a,b) ∈ (projectWalk p).toSubgraph.edgeSet := by
      rw [he']
      exact (Walk.cons h Walk.nil).toSubgraph_adj_snd (by simp)
    have hh' := (projectWalk p).mem_edges_toSubgraph.mp hh
    rw [Walk.edges_eq_nil.mpr hn] at hh'
    exact List.not_mem_nil hh'
  simpa only [Walk.toSubgraph_cons_nil_eq_subgraphOfAdj] using
    walk_subgraph_eq_of_edges (projectWalk p) (Walk.cons h Walk.nil) hp (by simp) he'

lemma lifted_short_subgraph {V : Type*} {G : SimpleGraph V}
    (P : PermutationPathSystem G) {a b : V} (h : G.Adj a b)
    (hp : P.perm a = b) (he : (P.walk a).toSubgraph = G.subgraphOfAdj h) :
    (leafWalk (P.walk a)).toSubgraph = (leafWalk (Walk.cons h Walk.nil)).toSubgraph := by
  rw [leafWalk_subgraph,leafWalk_subgraph,he,Walk.toSubgraph_cons_nil_eq_subgraphOfAdj]
  congr 1
  ext <;> simp [hp]

/-- Projecting all-leaf normal paths preserves the exact inactive set, not just
its cardinality. Every nonempty projected member occurs in the partition. -/
lemma project_normal_exact {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : NormalTrailSystem (allLeafCompletion G) k) (hp : ∀ i, (T.walk i).IsPath) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      (∀ H ∈ D, H.edgeSet.Nonempty) ∧ (∀ v, endpointMultiplicity D v ≤ 2) ∧
      inactive D = purified T ∧
      ∀ i, (projectWalk (T.walk i)).toSubgraph ∈ D ↔ ¬(projectWalk (T.walk i)).Nil := by
  obtain ⟨D,hD,hne,_,hb,htrack⟩ := project_system_tracked T hp
  refine ⟨D,hD,hne,?_,inactive_projection_eq_purified T hp hD hne htrack,
    projection_mem_iff T hD hne htrack⟩
  intro v
  simpa only [Set.mem_univ,↓reduceIte] using hb v

/-- A prescribed singleton edge can be given either orientation in the core
permutation, then lifted with the same exact inactive set. -/
lemma lift_normal_oriented {V : Type*} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {D : Finset G.Subgraph} (hD : GoodDecomposition G D)
    (hne : ∀ H ∈ D, H.edgeSet.Nonempty) (hb : ∀ v, endpointMultiplicity D v ≤ 2)
    (heven : ∀ v, Even (G.degree v)) {a b : V} (h : G.Adj a b)
    (hmem : G.subgraphOfAdj h ∈ D) :
    ∃ T : NormalTrailSystem (allLeafCompletion G) (Fintype.card V),
      (∀ i, (T.walk i).IsPath) ∧ purified T = inactive D ∧
      ∃ i, T.start i = Sum.inl a ∧ T.finish i = Sum.inr ⟨b,Set.mem_univ _⟩ ∧
        (T.walk i).toSubgraph = (leafWalk (Walk.cons h Walk.nil)).toSubgraph := by
  obtain ⟨P,hfix,_,hperm,hPa⟩ := permutation_of_normal_oriented hD hne hb heven h hmem
  obtain ⟨T,hp,hT,e,ha,hb⟩ := lift_permutation_exact P
  let i := e.symm a
  have hei : e i = a := e.apply_symm_apply a
  refine ⟨T,hp,hT.trans hfix,i,(ha i).trans (congrArg Sum.inl hei),?_,?_⟩
  · simpa only [hei,hperm] using hb.1 i
  · rw [hb.2,hei]
    exact lifted_short_subgraph P h hperm hPa

/-- A two-ended singleton-token exchange in an actual normal Eulerian core
partition. The argument can be applied at either end of the singleton edge.
This does not assert that its repeated application increases the inactive set. -/
lemma normal_single_edge_exchange {V : Type*} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {D : Finset G.Subgraph} (hD : GoodDecomposition G D)
    (hne : ∀ H ∈ D, H.edgeSet.Nonempty) (hb : ∀ v, endpointMultiplicity D v ≤ 2)
    (heven : ∀ v, Even (G.degree v))
    (hmax : ∀ E : Finset G.Subgraph, GoodDecomposition G E →
      (∀ H ∈ E, H.edgeSet.Nonempty) → (∀ v, endpointMultiplicity E v ≤ 2) →
      (inactive E).card ≤ (inactive D).card)
    {a b : V} (h : G.Adj a b) (hmem : G.subgraphOfAdj h ∈ D) :
    ∃ E : Finset G.Subgraph, GoodDecomposition G E ∧
      (∀ H ∈ E, H.edgeSet.Nonempty) ∧ (∀ v, endpointMultiplicity E v ≤ 2) ∧
      (∀ F : Finset G.Subgraph, GoodDecomposition G F →
        (∀ H ∈ F, H.edgeSet.Nonempty) → (∀ v, endpointMultiplicity F v ≤ 2) →
        (inactive F).card ≤ (inactive E).card) ∧
      ∃ z ∈ inactive D, ∃ haz : G.Adj a z,
        inactive E = insert b ((inactive D).erase z) ∧ G.subgraphOfAdj haz ∈ E := by
  classical
  obtain ⟨T,hp,hI,i,hai,hbi,hei⟩ := lift_normal_oriented hD hne hb heven h hmem
  have hTmax : ∀ U : NormalTrailSystem (allLeafCompletion G) (Fintype.card V),
      (∀ l, (U.walk l).IsPath) → (purified U).card ≤ (purified T).card := by
    intro U hU
    obtain ⟨F,hF,hFn,hFb,hFI,_⟩ := project_normal_exact U hU
    rw [hI,←hFI]
    exact hmax F hF hFn hFb
  obtain ⟨S,hSp,hSmax,z,hz,haz,hSI,l,hla,hlb,hle⟩ :=
    rooted_singleton_rotation T hp hTmax i h hai hbi hei
  obtain ⟨E,hE,hEn,hEb,hEI,hproj⟩ := project_normal_exact S hSp
  have hIb : b ∉ inactive D := hI ▸ destination_not_purified T i h hbi hei
  have hIz : z ∈ inactive D := hI ▸ hz
  have hIE : inactive E = insert b ((inactive D).erase z) := by rw [hEI,hSI,hI]
  have hcard : (inactive E).card = (inactive D).card := by
    rw [hIE,Finset.card_insert_of_notMem (fun hh ↦ hIb (Finset.mem_of_mem_erase hh)),
      Finset.card_erase_of_mem hIz]
    have hh := Finset.card_pos.mpr ⟨z,hIz⟩
    omega
  refine ⟨E,hE,hEn,hEb,?_,z,hIz,haz,hIE,?_⟩
  · intro F hF hFn hFb
    rw [hcard]
    exact hmax F hF hFn hFb
  · have heproj := project_short_subgraph (S.walk l) haz hle
    rw [←heproj]
    apply (hproj l).mpr
    intro hn
    have hh : s(a,z) ∈ (projectWalk (S.walk l)).toSubgraph.edgeSet := by
      rw [heproj,G.edgeSet_subgraphOfAdj]
      exact Set.mem_singleton _
    have hh' := (projectWalk (S.walk l)).mem_edges_toSubgraph.mp hh
    rw [Walk.edges_eq_nil.mpr hn] at hh'
    exact List.not_mem_nil hh'

end Erdos583CanonicalRotationDevelopment
