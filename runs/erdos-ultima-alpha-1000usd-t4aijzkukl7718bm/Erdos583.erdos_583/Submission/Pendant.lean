import Submission.Work

/-! Pendant completion and projection. This is a reduction of the remaining
endpoint-choice problem, not an assumed simultaneous-purification theorem. -/

open SimpleGraph Erdos583Work
namespace Erdos583PendantDevelopment

set_option maxHeartbeats 1200000

/-- Attach one new leaf to each vertex of S. -/
def leafCompletion {V : Type*} (G : SimpleGraph V) (S : Set V) : SimpleGraph (V ⊕ S) where
  Adj a b := match a,b with
    | .inl u,.inl v => G.Adj u v
    | .inl u,.inr v => u=v.val
    | .inr u,.inl v => u.val=v
    | .inr _,.inr _ => False
  symm := by rintro (u|u) (v|v) h <;> first | exact h.symm | exact h.elim
  loopless := by rintro (u|u) <;> simp

def root {V : Type*} {S : Set V} : V ⊕ S → V
  | .inl v => v
  | .inr v => v.val

def inclusion {V : Type*} (G : SimpleGraph V) (S : Set V) : G →g leafCompletion G S where
  toFun := Sum.inl
  map_rel' h := h

lemma leaf_adj {V : Type*} {G : SimpleGraph V} {S : Set V} (v : S) (x : V ⊕ S) :
    (leafCompletion G S).Adj (.inr v) x ↔ x = .inl v.val := by
  cases x <;> simp [leafCompletion,eq_comm]

lemma leaf_neighbor_ncard {V : Type*} {G : SimpleGraph V} {S : Set V} (v : S) :
    Nat.card ((leafCompletion G S).neighborSet (.inr v)) = 1 := by
  have he : (leafCompletion G S).neighborSet (.inr v) = {Sum.inl v.val} := by
    ext x; exact leaf_adj v x
  rw [he,Nat.card_coe_set_eq]
  simp

lemma original_neighbor_ncard {V : Type*} [Fintype V] (G : SimpleGraph V)
    (S : Set V) [DecidablePred (· ∈ S)] (v : V) :
    Nat.card ((leafCompletion G S).neighborSet (.inl v)) =
      Nat.card (G.neighborSet v) + if v ∈ S then 1 else 0 := by
  classical
  have he : (leafCompletion G S).neighborSet (.inl v) =
      Sum.inl '' G.neighborSet v ∪ {x | ∃ s : S, x = Sum.inr s ∧ s.val = v} := by
    ext x
    cases x <;> simp [leafCompletion,eq_comm]
  simp only [Nat.card_coe_set_eq]
  rw [he,Set.ncard_union_eq (by
    apply Set.disjoint_left.mpr
    rintro _ ⟨u,hu,rfl⟩ ⟨s,hs,_⟩
    exact Sum.inl_ne_inr hs), Set.ncard_image_of_injective _ Sum.inl_injective]
  by_cases hv : v ∈ S
  · have hs : {x : V ⊕ S | ∃ s : S, x = Sum.inr s ∧ s.val = v} = {Sum.inr ⟨v,hv⟩} := by
      ext x
      constructor
      · rintro ⟨s,rfl,hs⟩
        exact congrArg Sum.inr (Subtype.ext hs)
      · intro hx
        exact ⟨⟨v,hv⟩,hx,rfl⟩
    rw [hs]
    simp [hv]
  · have hs : {x : V ⊕ S | ∃ s : S, x = Sum.inr s ∧ s.val = v} = ∅ := by
      ext x
      simp only [Set.mem_setOf_eq,Set.mem_empty_iff_false,iff_false]
      rintro ⟨s,_,hs⟩
      exact hv (hs ▸ s.property)
    rw [hs]
    simp [hv]

lemma leafCompletion_odd {V : Type*} [Fintype V] (G : SimpleGraph V)
    (x : V ⊕ {v | Even (Nat.card (G.neighborSet v))}) :
    Odd (Nat.card ((leafCompletion G {v | Even (Nat.card (G.neighborSet v))}).neighborSet x)) := by
  classical
  cases x with
  | inl v =>
    rw [original_neighbor_ncard]
    by_cases hv : Even (Nat.card (G.neighborSet v))
    · simp only [Set.mem_setOf_eq,hv,↓reduceIte]
      exact hv.add_odd (by decide : Odd 1)
    · simp only [Set.mem_setOf_eq,hv,↓reduceIte,add_zero]
      exact Nat.not_even_iff_odd.mp hv
  | inr v => rw [leaf_neighbor_ncard]; decide

lemma leafCompletion_connected {V : Type*} {G : SimpleGraph V}
    (hG : G.Connected) (S : Set V) : (leafCompletion G S).Connected := by
  letI : Nonempty V := hG.nonempty
  letI : Nonempty (V ⊕ S) := ⟨.inl (Classical.arbitrary V)⟩
  have hr (x : V ⊕ S) : (leafCompletion G S).Reachable x (.inl (root x)) := by
    cases x with
    | inl v => exact Reachable.refl _
    | inr v => exact (show (leafCompletion G S).Adj (.inr v) (.inl v.val) from rfl).reachable
  refine ⟨fun x y ↦ (hr x).trans (?_ : (leafCompletion G S).Reachable (.inl (root x)) y)⟩
  exact ((hG.preconnected (root x) (root y)).map (inclusion G S)).trans (hr y).symm

/-- Collapse the pendant edges, keeping all original edges in their order. -/
def projectWalk {V : Type*} {G : SimpleGraph V} {S : Set V} :
    {a b : V ⊕ S} → (leafCompletion G S).Walk a b → G.Walk (root a) (root b)
  | _,_,.nil => .nil
  | .inl _,_,.cons (v := .inl _) h p => .cons h (projectWalk p)
  | .inl _,_,.cons (v := .inr _) h p => (projectWalk p).copy h.symm rfl
  | .inr _,_,.cons (v := .inl _) h p => (projectWalk p).copy h.symm rfl
  | .inr _,_,.cons (v := .inr _) h _ => h.elim

lemma leaf_first {V : Type*} {G : SimpleGraph V} {S : Set V} {v : S} {b : V ⊕ S}
    (p : (leafCompletion G S).Walk (.inr v) b) (hn : ¬p.Nil) :
    Sum.inl v.val ∈ p.support := by
  have ha := p.adj_snd hn
  have he : p.snd = .inl v.val := (leaf_adj v _).mp ha
  rw [←he]
  exact p.getVert_mem_support 1

lemma project_path_support {V : Type*} {G : SimpleGraph V} {S : Set V}
    {a b : V ⊕ S} (p : (leafCompletion G S).Walk a b) (hp : p.IsPath) :
    (projectWalk p).IsPath ∧
      ∀ x ∈ (projectWalk p).support, Sum.inl x ∈ p.support ∨ (p.Nil ∧ root a=x) := by
  induction p with
  | nil =>
    refine ⟨Walk.IsPath.nil,?_⟩
    intro x hx
    exact Or.inr ⟨Walk.Nil.nil,by simpa [projectWalk,eq_comm] using hx⟩
  | @cons a w b h p ih =>
    obtain ⟨hp',ha⟩ := (Walk.cons_isPath_iff h p).mp hp
    obtain ⟨hproj,hsupp⟩ := ih hp'
    cases a with
    | inl u =>
      cases w with
      | inl v =>
        have hs : ∀ x ∈ (projectWalk p).support, Sum.inl x ∈ p.support := by
          intro x hx
          rcases hsupp x hx with hh | ⟨_,hh⟩
          · exact hh
          · rw [←hh]; exact p.start_mem_support
        refine ⟨(Walk.cons_isPath_iff (show G.Adj u v from h) _).mpr
          ⟨hproj,fun hh ↦ ha (hs u hh)⟩,?_⟩
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact Or.inl (List.mem_cons_self ..)
        · exact Or.inl (List.mem_cons_of_mem _ (hs x hx))
      | inr v =>
        have h' : u=v.val := h
        have hn : p.Nil := by
          by_contra hn
          exact ha (h'.symm ▸ leaf_first p hn)
        cases hn
        constructor
        · simp [projectWalk]
        · intro x hx
          have hx' : v.val=x := by simpa [projectWalk,Walk.support_copy,eq_comm] using hx
          exact Or.inl (List.mem_cons.mpr (Or.inl (congrArg Sum.inl (h'.trans hx').symm)))
    | inr u =>
      cases w with
      | inl v =>
        have h' : u.val=v := h
        refine ⟨by simpa [projectWalk] using hproj,?_⟩
        intro x hx
        have hx' : x ∈ (projectWalk p).support := by simpa [projectWalk] using hx
        apply Or.inl
        apply List.mem_cons_of_mem
        rcases hsupp x hx' with hh | ⟨_,hh⟩
        · exact hh
        · rw [←hh]; exact p.start_mem_support
      | inr v => exact h.elim

lemma inl_edge_injective {V : Type*} {S : Set V} :
    Function.Injective (Sym2.map (Sum.inl : V → V ⊕ S)) := by
  intro e f he
  induction e using Sym2.ind with
  | h a b =>
    induction f using Sym2.ind with
    | h c d =>
      simp only [Sym2.map_pair_eq,Sym2.eq_iff,Sum.inl.injEq] at he ⊢
      exact he

lemma inl_edge_ne_cross {V : Type*} {S : Set V} (e : Sym2 V) (u : V) (v : S) :
    Sym2.map Sum.inl e ≠ s(Sum.inl u,Sum.inr v) := by
  induction e using Sym2.ind with
  | h a b => simp

lemma project_edges {V : Type*} {G : SimpleGraph V} {S : Set V}
    {a b : V ⊕ S} (p : (leafCompletion G S).Walk a b) (e : Sym2 V) :
    e ∈ (projectWalk p).edges ↔ Sym2.map Sum.inl e ∈ p.edges := by
  induction p with
  | nil => simp [projectWalk]
  | @cons a w b h p ih =>
    cases a with
    | inl u =>
      cases w with
      | inl v =>
        have hinj : Sym2.map (Sum.inl : V → V ⊕ S) e = s(.inl u,.inl v) ↔ e=s(u,v) := by
          constructor
          · intro h; exact inl_edge_injective h
          · rintro rfl; rfl
        simp only [projectWalk,root,Walk.edges_cons,List.mem_cons,ih,hinj]
      | inr v =>
        simp only [projectWalk,Walk.edges_copy,Walk.edges_cons,List.mem_cons,
          inl_edge_ne_cross e u v,false_or,ih]
    | inr u =>
      cases w with
      | inl v =>
        have hn : Sym2.map Sum.inl e ≠ s(Sum.inr u,Sum.inl v) := by
          simpa only [Sym2.eq_swap] using inl_edge_ne_cross e v u
        simp only [projectWalk,Walk.edges_copy,Walk.edges_cons,List.mem_cons,hn,false_or,ih]
      | inr v => exact h.elim

lemma project_edgeSet {V : Type*} {G : SimpleGraph V} {S : Set V}
    {a b : V ⊕ S} (p : (leafCompletion G S).Walk a b) (e : Sym2 V) :
    e ∈ (projectWalk p).toSubgraph.edgeSet ↔ Sym2.map Sum.inl e ∈ p.toSubgraph.edgeSet := by
  simpa only [Walk.mem_edges_toSubgraph] using project_edges p e

/-- A simple projected member is empty exactly when its two projected endpoints
coincide. -/
lemma project_nil_iff {V : Type*} {G : SimpleGraph V} {S : Set V}
    {a b : V ⊕ S} (p : (leafCompletion G S).Walk a b) (hp : p.IsPath) :
    (projectWalk p).Nil ↔ root a = root b := by
  constructor
  · exact Walk.Nil.eq
  · intro hab
    have hh := (project_path_support p hp).1
    have hn : ((projectWalk p).copy rfl hab.symm).Nil := by
      have hp' : ((projectWalk p).copy rfl hab.symm).IsPath := by
        simpa only [Walk.isPath_copy] using hh
      rw [Walk.isPath_iff_eq_nil] at hp'
      rw [hp']
      exact Walk.Nil.nil
    simpa using hn

open scoped Classical in
noncomputable def vanished {V : Type*} {G : SimpleGraph V} {S : Set V} {k : ℕ}
    (T : NormalTrailSystem (leafCompletion G S) k) : Finset (Fin k) :=
  Finset.univ.filter fun i ↦ (projectWalk (T.walk i)).Nil

open scoped Classical in
lemma root_fiber_card {V : Type*} [Fintype V] {S : Set V} (v : V) :
    Nat.card {x : V ⊕ S // root x=v} = 1 + if v ∈ S then 1 else 0 := by
  classical
  have he : {x : V ⊕ S | root x=v} = {Sum.inl v} ∪
      {x | ∃ s : S, x = Sum.inr s ∧ s.val=v} := by
    ext x
    cases x <;> simp [root]
  change {x : V ⊕ S | root x=v}.ncard = _
  rw [he,Set.ncard_union_eq (by
    apply Set.disjoint_left.mpr
    rintro _ rfl ⟨s,hs,_⟩
    exact Sum.inl_ne_inr hs)]
  simp only [Set.ncard_singleton]
  by_cases hv : v ∈ S
  · have hs : {x : V ⊕ S | ∃ s : S, x = Sum.inr s ∧ s.val=v} = {Sum.inr ⟨v,hv⟩} := by
      ext x
      constructor
      · rintro ⟨s,rfl,hs⟩
        exact congrArg Sum.inr (Subtype.ext hs)
      · intro hx; exact ⟨⟨v,hv⟩,hx,rfl⟩
    simp [hv]
  · have hs : {x : V ⊕ S | ∃ s : S, x = Sum.inr s ∧ s.val=v} = ∅ := by
      ext x
      simp only [Set.mem_setOf_eq,Set.mem_empty_iff_false,iff_false]
      rintro ⟨s,_,hs⟩
      exact hv (hs ▸ s.property)
    simp [hv]

open scoped Classical in
/-- Project an all-odd normal path system and discard precisely the empty
projections. Its cardinality loss and endpoint multiplicity bounds are exact. -/
lemma project_system_tracked {V : Type*} [Fintype V] {G : SimpleGraph V} {S : Set V} {k : ℕ}
    (T : NormalTrailSystem (leafCompletion G S) k) (hp : ∀ i, (T.walk i).IsPath) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      (∀ H ∈ D, H.edgeSet.Nonempty) ∧ D.card + (vanished T).card = k ∧
      (∀ v, endpointMultiplicity D v ≤ 1 + if v ∈ S then 1 else 0) ∧
      ∀ H ∈ D, ∃ i, H = (projectWalk (T.walk i)).toSubgraph := by
  classical
  let p (i : Fin k) := projectWalk (T.walk i)
  have hpath (i : Fin k) : (p i).IsPath := (project_path_support _ (hp i)).1
  let I := Finset.univ.filter fun i ↦ ¬(p i).Nil
  let f (i : Fin k) := (p i).toSubgraph
  have hne (i : Fin k) (hi : i ∈ I) : (f i).edgeSet.Nonempty := by
    have hn : ¬(p i).Nil := (Finset.mem_filter.mp hi).2
    exact ⟨s(root (T.start i),(p i).snd),(p i).toSubgraph_adj_snd hn⟩
  have hdis : Pairwise fun i j ↦ Disjoint (f i).edgeSet (f j).edgeSet := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro e hi hj
    exact Set.disjoint_left.mp (T.disjoint hij)
      ((project_edgeSet (T.walk i) e).mp hi) ((project_edgeSet (T.walk j) e).mp hj)
  have hinj : Set.InjOn f (I : Set (Fin k)) := by
    intro i hi j hj he
    by_contra hij
    obtain ⟨e,he'⟩ := hne i hi
    exact Set.disjoint_left.mp (hdis hij) he' (he ▸ he')
  let D := I.image f
  have hD : GoodDecomposition G D := by
    refine ⟨?_,?_,?_⟩
    · intro H hH
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hH
      exact ⟨_,_,p i,hpath i,rfl⟩
    · intro H hH K hK hHK
      change H ∈ I.image f at hH
      change K ∈ I.image f at hK
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hH
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hK
      exact hdis (fun hh ↦ hHK (congrArg f hh))
    · ext e
      simp only [Set.mem_iUnion]
      constructor
      · rintro ⟨H,_,he⟩; exact H.edgeSet_subset he
      · intro he
        have heH : Sym2.map Sum.inl e ∈ (leafCompletion G S).edgeSet := by
          induction e using Sym2.ind with
          | h u v => exact he
        obtain ⟨i,hi⟩ := (T.cover _).mp heH
        have he' : e ∈ (f i).edgeSet := (project_edgeSet (T.walk i) e).mpr hi
        have hiI : i ∈ I := by
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
          intro hn
          have hh := (p i).mem_edges_toSubgraph.mp he'
          have hempty : (p i).edges = [] := Walk.edges_eq_nil.mpr hn
          rw [hempty] at hh
          exact List.not_mem_nil hh
        exact ⟨f i,Finset.mem_image.mpr ⟨i,hiI,rfl⟩,he'⟩
  have hDne : ∀ H ∈ D, H.edgeSet.Nonempty := by
    intro H hH
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hH
    exact hne i hi
  have hc : D.card + (vanished T).card = k := by
    rw [show D.card = I.card from Finset.card_image_of_injOn hinj]
    have hh := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin k)))
      (fun i ↦ (p i).Nil)
    simpa [I,vanished,p,Nat.add_comm] using hh
  refine ⟨D,hD,hDne,hc,?_,?_⟩
  · intro v
    let E := D.filter fun H ↦ (H.neighborSet v).ncard = 1
    have hslot (H : E) : ∃ x : Fin k × Bool,
        H.val = f x.1 ∧ root (NormalTrailSystem.endpointEquiv T x) = v := by
      obtain ⟨hHD,hHv⟩ := Finset.mem_filter.mp H.property
      obtain ⟨i,hi,he⟩ := Finset.mem_image.mp hHD
      have hv : v = root (T.start i) ∨ v = root (T.finish i) := by
        have hdeg : ((p i).toSubgraph.neighborSet v).ncard = 1 := by
          change ((f i).neighborSet v).ncard = 1
          rw [he]
          exact hHv
        rw [path_neighbor_ncard_formula (hpath i) (Finset.mem_filter.mp hi).2] at hdeg
        by_contra hv
        simp [hv] at hdeg
        split_ifs at hdeg; norm_num at hdeg
      rcases hv with hv | hv
      · exact ⟨(i,true),he.symm,hv.symm⟩
      · exact ⟨(i,false),he.symm,hv.symm⟩
    choose slot hslotK hslotV using hslot
    let g (H : E) : {x : V ⊕ S // root x=v} :=
      ⟨NormalTrailSystem.endpointEquiv T (slot H),hslotV H⟩
    have hg : Function.Injective g := by
      intro H K hHK
      have hends := (NormalTrailSystem.endpointEquiv T).injective (congrArg Subtype.val hHK)
      apply Subtype.ext
      rw [hslotK,hslotK,hends]
    have hcard := Fintype.card_le_of_injective g hg
    change E.card ≤ _
    rw [← root_fiber_card v]
    simpa only [Nat.card_eq_fintype_card,Fintype.card_coe] using hcard
  · intro H hH
    obtain ⟨i,_,he⟩ := Finset.mem_image.mp hH
    exact ⟨i,he.symm⟩

open scoped Classical in
lemma project_system {V : Type*} [Fintype V] {G : SimpleGraph V} {S : Set V} {k : ℕ}
    (T : NormalTrailSystem (leafCompletion G S) k) (hp : ∀ i, (T.walk i).IsPath) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      (∀ H ∈ D, H.edgeSet.Nonempty) ∧ D.card + (vanished T).card = k ∧
      ∀ v, endpointMultiplicity D v ≤ 1 + if v ∈ S then 1 else 0 := by
  obtain ⟨D,hD,hne,hc,hb,_⟩ := project_system_tracked T hp
  exact ⟨D,hD,hne,hc,hb⟩

/-- Every finite graph has a path partition with at most two endpoints per
vertex. No bound of `ceil(|V|/2)` is being asserted here. -/
lemma exists_normal_decomposition {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      (∀ H ∈ D, H.edgeSet.Nonempty) ∧
      ∀ v, endpointMultiplicity D v ≤ 2 ∧
        (endpointMultiplicity D v = 1 ↔ Odd (G.degree v)) := by
  classical
  let S : Set V := {v | Even (Nat.card (G.neighborSet v))}
  let H := leafCompletion G S
  have ho (x : V ⊕ S) : Odd (H.degree x) := by
    simpa only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree] using leafCompletion_odd G x
  obtain ⟨k,hk,⟨T⟩⟩ := all_odd_normal_trail_system H ho
  obtain ⟨R,hR⟩ := T.exists_max_score
  obtain ⟨D,hD,hne,hcard,hends⟩ := project_system R (TrailNormalization.max_score_isPath R hR)
  refine ⟨D,hD,hne,fun v ↦ ?_⟩
  have hb : endpointMultiplicity D v ≤ 2 := (hends v).trans (by split_ifs <;> omega)
  refine ⟨hb,?_⟩
  rw [← hD.odd_endpointMultiplicity_iff, Nat.odd_iff]
  omega

/-- The vertices which are not endpoints of any nonempty member. -/
noncomputable def inactive {V : Type*} [Fintype V] {G : SimpleGraph V}
    (D : Finset G.Subgraph) : Finset V := by
  classical
  exact Finset.univ.filter fun v ↦ endpointMultiplicity D v = 0

lemma inactive_even {V : Type*} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {D : Finset G.Subgraph} (hD : GoodDecomposition G D)
    {v : V} (hv : v ∈ inactive D) : Even (G.degree v) := by
  classical
  have hz : endpointMultiplicity D v = 0 := (Finset.mem_filter.mp hv).2
  apply Nat.not_odd_iff_even.mp
  rw [← hD.odd_endpointMultiplicity_iff,hz]
  decide

open scoped Classical in
/-- Exact endpoint count in a normal partition. The missing part of the Gallai
bound is a lower bound on the inactive set, not the existence of normality. -/
lemma normal_count {V : Type*} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {D : Finset G.Subgraph} (hD : GoodDecomposition G D)
    (hne : ∀ H ∈ D, H.edgeSet.Nonempty) (hb : ∀ v, endpointMultiplicity D v ≤ 2) :
    2*D.card + 2*(inactive D).card = Fintype.card V +
      (Finset.univ.filter fun v ↦ Even (G.degree v)).card := by
  classical
  have he (v : V) : endpointMultiplicity D v +
      2*(if endpointMultiplicity D v = 0 then 1 else 0) =
      1 + if Even (G.degree v) then 1 else 0 := by
    have hpar := hD.odd_endpointMultiplicity_iff v
    have hn := hb v
    rw [Nat.odd_iff,Nat.odd_iff] at hpar
    simp only [Nat.even_iff]
    split_ifs <;> omega
  have hs := congrArg (fun f : V → ℕ ↦ ∑ v, f v) (funext he)
  simpa only [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.card_filter,
    Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one,
    hD.sum_endpointMultiplicity hne,inactive] using hs

open scoped Classical in
lemma normal_gallai_iff {V : Type*} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {D : Finset G.Subgraph} (hD : GoodDecomposition G D)
    (hne : ∀ H ∈ D, H.edgeSet.Nonempty) (hb : ∀ v, endpointMultiplicity D v ≤ 2) :
    D.card ≤ ⌈(Fintype.card V : ℚ)/2⌉₊ ↔
      (Finset.univ.filter fun v ↦ Even (G.degree v)).card / 2 ≤ (inactive D).card := by
  have hc := normal_count hD hne hb
  have hlo : Fintype.card V ≤ 2*⌈(Fintype.card V : ℚ)/2⌉₊ := by
    have hh := Nat.le_ceil ((Fintype.card V : ℚ)/2)
    exact_mod_cast (show (Fintype.card V : ℚ) ≤ 2*(⌈(Fintype.card V : ℚ)/2⌉₊ : ℚ) by linarith)
  have hhi : 2*⌈(Fintype.card V : ℚ)/2⌉₊ < Fintype.card V + 2 := by
    have hh := Nat.ceil_lt_add_one (show (0 : ℚ) ≤ (Fintype.card V : ℚ)/2 by positivity)
    exact_mod_cast (show 2*(⌈(Fintype.card V : ℚ)/2⌉₊ : ℚ) < (Fintype.card V : ℚ) + 2 by linarith)
  omega

/-- There is a normal decomposition maximizing the number of inactive vertices.
Existence is unconditional; the desired lower bound on this maximum is not. -/
lemma exists_max_inactive {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      (∀ H ∈ D, H.edgeSet.Nonempty) ∧ (∀ v, endpointMultiplicity D v ≤ 2) ∧
      ∀ E : Finset G.Subgraph, GoodDecomposition G E →
        (∀ H ∈ E, H.edgeSet.Nonempty) → (∀ v, endpointMultiplicity E v ≤ 2) →
        (inactive E).card ≤ (inactive D).card := by
  classical
  let P (j : ℕ) := ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
    (∀ H ∈ D, H.edgeSet.Nonempty) ∧ (∀ v, endpointMultiplicity D v ≤ 2) ∧
    (inactive D).card = j
  obtain ⟨D,hD,hne,hends⟩ := exists_normal_decomposition G
  have hn : (inactive D).card ≤ Fintype.card V := Finset.card_le_univ _
  have hf := Nat.findGreatest_spec (P := P) hn ⟨D,hD,hne,fun v ↦ (hends v).1,rfl⟩
  obtain ⟨E,hE,hEne,hEends,hc⟩ := hf
  refine ⟨E,hE,hEne,hEends,?_⟩
  intro F hF hFne hFends
  rw [hc]
  exact Nat.le_findGreatest (Finset.card_le_univ _) ⟨F,hF,hFne,hFends,rfl⟩

open scoped Classical in
/-- A precise conditional reduction. The strict endpoint-extension premise is
NOT proved here and is not assumed elsewhere in the development. -/
lemma gallai_of_inactive_extension {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj]
    (hext : ∀ D : Finset G.Subgraph, GoodDecomposition G D →
      (∀ H ∈ D, H.edgeSet.Nonempty) → (∀ v, endpointMultiplicity D v ≤ 2) →
      (inactive D).card < (Finset.univ.filter fun v ↦ Even (G.degree v)).card / 2 →
      ∃ E : Finset G.Subgraph, GoodDecomposition G E ∧
        (∀ H ∈ E, H.edgeSet.Nonempty) ∧ (∀ v, endpointMultiplicity E v ≤ 2) ∧
        inactive D ⊂ inactive E) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card V : ℚ)/2⌉₊ := by
  classical
  obtain ⟨D,hD,hne,hb,hmax⟩ := exists_max_inactive G
  refine ⟨D,hD,(normal_gallai_iff hD hne hb).mpr ?_⟩
  by_contra hh
  obtain ⟨E,hE,hEne,hEb,hss⟩ := hext D hD hne hb (by omega)
  exact (not_lt_of_ge (hmax E hE hEne hEb)) (Finset.card_lt_card hss)

open scoped Classical in
/-- For the even-vertex completion, the two exact counts identify the number
of vanished members with the number of inactive original vertices. -/
lemma project_even_system {V : Type*} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {k : ℕ}
    (T : NormalTrailSystem (leafCompletion G {v | Even (Nat.card (G.neighborSet v))}) k)
    (hp : ∀ i, (T.walk i).IsPath) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      (∀ H ∈ D, H.edgeSet.Nonempty) ∧ (∀ v, endpointMultiplicity D v ≤ 2) ∧
      D.card + (vanished T).card = k ∧ (inactive D).card = (vanished T).card := by
  classical
  obtain ⟨D,hD,hne,hcard,hends⟩ := project_system T hp
  have hb (v : V) : endpointMultiplicity D v ≤ 2 :=
    (hends v).trans (by split_ifs <;> omega)
  have hc := normal_count hD hne hb
  have hk := T.twice_card
  have hs : Fintype.card ({v : V | Even (Nat.card (G.neighborSet v))}) =
      (Finset.univ.filter fun v ↦ Even (G.degree v)).card := by
    have he : {v : V | Even (Nat.card (G.neighborSet v))} = {v | Even (G.degree v)} := by
      ext v
      simp only [Set.mem_setOf_eq,Nat.card_eq_fintype_card,card_neighborSet_eq_degree]
    calc
      _ = Fintype.card ({v : V | Even (G.degree v)}) := Fintype.card_congr (Equiv.setCongr he)
      _ = _ := Fintype.card_subtype _
  rw [Fintype.card_sum,hs] at hk
  exact ⟨D,hD,hne,hb,hcard,by omega⟩

open scoped Classical in
/-- Enough whole leaf-edge members suffice for Gallai. This only consumes an
explicit simultaneous-purification witness; it does not assert one exists. -/
lemma gallai_of_purification {V : Type*} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {k : ℕ}
    (T : NormalTrailSystem (leafCompletion G {v | Even (Nat.card (G.neighborSet v))}) k)
    (hp : ∀ i, (T.walk i).IsPath)
    (hvanish : (Finset.univ.filter fun v ↦ Even (G.degree v)).card / 2 ≤ (vanished T).card) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card V : ℚ)/2⌉₊ := by
  obtain ⟨D,hD,hne,hb,_,hc⟩ := project_even_system T hp
  exact ⟨D,hD,(normal_gallai_iff hD hne hb).mpr (hc ▸ hvanish)⟩

end Erdos583PendantDevelopment
