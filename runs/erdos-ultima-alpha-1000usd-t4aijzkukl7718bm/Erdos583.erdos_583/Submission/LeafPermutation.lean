import Submission.Work

/-! Lifting permutation paths to one-leaf-per-member normal systems. -/

open SimpleGraph Erdos583Work Erdos583Work.PendantCompletion
open Erdos583Work.EulerianPermutation
namespace Erdos583LeafPermutationDevelopment
open scoped Classical

set_option maxHeartbeats 1200000

abbrev allLeafCompletion {V : Type*} (G : SimpleGraph V) := leafCompletion G Set.univ

def leafWalk {V : Type*} {G : SimpleGraph V} {a b : V} (p : G.Walk a b) :
    (allLeafCompletion G).Walk (.inl a) (.inr ⟨b,Set.mem_univ b⟩) :=
  (p.map (inclusion G Set.univ)).concat (show (allLeafCompletion G).Adj (.inl b) (.inr ⟨b,Set.mem_univ b⟩) from rfl)

lemma leafWalk_isPath {V : Type*} {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) (hp : p.IsPath) : (leafWalk p).IsPath := by
  apply (Walk.map_isPath_of_injective (f := inclusion G Set.univ) Sum.inl_injective hp).concat
  simp [Walk.support_map,inclusion]

lemma leafWalk_leaf_support {V : Type*} {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) (z : (Set.univ : Set V)) :
    Sum.inr z ∈ (leafWalk p).support ↔ z.val = b := by
  simp [leafWalk,Walk.support_map,inclusion,Subtype.ext_iff]

lemma leafWalk_edges {V : Type*} {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) (e : Sym2 (V ⊕ (Set.univ : Set V))) :
    e ∈ (leafWalk p).toSubgraph.edgeSet ↔
      (∃ d ∈ p.toSubgraph.edgeSet, Sym2.map Sum.inl d = e) ∨ e = s(Sum.inl b,Sum.inr ⟨b,Set.mem_univ b⟩) := by
  simp [leafWalk,Walk.edges_map,inclusion]

lemma leafWalk_project {V : Type*} {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) : projectWalk (leafWalk p) = p := by
  induction p with
  | nil => rfl
  | cons h p ih =>
    simpa only [leafWalk,Walk.map_cons,Walk.concat_cons,projectWalk,inclusion] using congrArg (Walk.cons h) ih

/-- Lift any permutation-path system to a normal path system of the all-leaf
completion. Every member has one leaf, and its core endpoints encode the original
permutation. Its score is a global maximum, not merely a restricted maximum. -/
lemma lift_permutation_system {V : Type*} [Fintype V] {G : SimpleGraph V}
    (P : PermutationPathSystem G) :
    ∃ T : NormalTrailSystem (allLeafCompletion G) (Fintype.card V),
      (∀ i, (T.walk i).IsPath) ∧
      (∀ U : NormalTrailSystem (allLeafCompletion G) (Fintype.card V), U.score ≤ T.score) ∧
      ∃ e : Fin (Fintype.card V) ≃ V,
        (∀ i, T.start i = Sum.inl (e i)) ∧
        (∀ i, T.finish i = Sum.inr ⟨P.perm (e i),Set.mem_univ _⟩) ∧
        (∀ i, HEq (projectWalk (T.walk i)) (P.walk (e i))) ∧
        ∀ i, ∀ z : (Set.univ : Set V), Sum.inr z ∈ (T.walk i).support ↔ z.val = P.perm (e i) := by
  classical
  let e : Fin (Fintype.card V) ≃ V := (Fintype.equivFin V).symm
  let a (i : Fin (Fintype.card V)) : V ⊕ (Set.univ : Set V) := Sum.inl (e i)
  let b (i : Fin (Fintype.card V)) : V ⊕ (Set.univ : Set V) := Sum.inr ⟨P.perm (e i),Set.mem_univ _⟩
  let q (i : Fin (Fintype.card V)) := leafWalk (P.walk (e i))
  have hq (i : Fin (Fintype.card V)) : (q i).IsPath := leafWalk_isPath _ (P.isPath _)
  have hends : Function.Bijective (fun x : Fin (Fintype.card V) × Bool ↦ if x.2 then a x.1 else b x.1) := by
    constructor
    · rintro ⟨i,c⟩ ⟨j,d⟩ he
      cases c <;> cases d
      · have hij : i = j := e.injective (P.perm.injective (congrArg Subtype.val (Sum.inr.inj he)))
        exact Prod.ext hij rfl
      · exact (Sum.inr_ne_inl he).elim
      · exact (Sum.inl_ne_inr he).elim
      · have hij : i = j := e.injective (Sum.inl.inj he)
        exact Prod.ext hij rfl
    · rintro (v|v)
      · exact ⟨(e.symm v,true),by simp [a]⟩
      · exact ⟨(e.symm (P.perm.symm v.val),false),by simp [b]⟩
  have hdis : Pairwise fun i j ↦ Disjoint (q i).toSubgraph.edgeSet (q j).toSubgraph.edgeSet := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro d hdi hdj
    rw [leafWalk_edges] at hdi hdj
    rcases hdi with ⟨x,hx,hxd⟩ | hdi
    · rcases hdj with ⟨y,hy,hyd⟩ | hdj
      · have hxy : x = y := inl_edge_injective (hxd.trans hyd.symm)
        exact Set.disjoint_left.mp (P.disjoint (fun hh ↦ hij (e.injective hh))) hx (hxy.symm ▸ hy)
      · exact inl_edge_ne_cross x (P.perm (e j)) ⟨P.perm (e j),Set.mem_univ _⟩ (hxd.trans hdj)
    · rcases hdj with ⟨y,hy,hyd⟩ | hdj
      · exact inl_edge_ne_cross y (P.perm (e i)) ⟨P.perm (e i),Set.mem_univ _⟩ (hyd.trans hdi)
      · have hh := hdi.symm.trans hdj
        have heq : P.perm (e i) = P.perm (e j) := by
          rcases Sym2.eq_iff.mp hh with hh | hh
          · exact Sum.inl.inj hh.1
          · exact (Sum.inl_ne_inr hh.1).elim
        exact hij (e.injective (P.perm.injective heq))
  have hcover (d : Sym2 (V ⊕ (Set.univ : Set V))) :
      d ∈ (allLeafCompletion G).edgeSet ↔ ∃ i, d ∈ (q i).toSubgraph.edgeSet := by
    constructor
    · intro hd
      induction d using Sym2.ind with
      | h x y =>
        cases x with
        | inl x =>
          cases y with
          | inl y =>
            obtain ⟨v,hv⟩ := (P.cover s(x,y)).mp hd
            refine ⟨e.symm v,?_⟩
            rw [leafWalk_edges]
            exact Or.inl ⟨s(x,y),by rw [e.apply_symm_apply]; exact hv,rfl⟩
          | inr y =>
            have hxy : x = y.val := hd
            refine ⟨e.symm (P.perm.symm x),?_⟩
            rw [leafWalk_edges]
            right
            simp [hxy]
        | inr x =>
          cases y with
          | inl y =>
            have hxy : x.val = y := hd
            refine ⟨e.symm (P.perm.symm y),?_⟩
            rw [leafWalk_edges]
            right
            simp only [Equiv.apply_symm_apply,Sym2.eq_swap]
            exact congrArg (fun z : (Set.univ : Set V) ↦ s(Sum.inl y,Sum.inr z)) (Subtype.ext hxy)
          | inr y => exact hd.elim
    · rintro ⟨i,hi⟩
      exact (q i).toSubgraph.edgeSet_subset hi
  let T : NormalTrailSystem (allLeafCompletion G) (Fintype.card V) :=
    { start := a,finish := b,walk := q,isTrail := fun i ↦ (hq i).isTrail,
      endpoint_bijective := hends,disjoint := hdis,cover := hcover }
  have hmax : ∀ U : NormalTrailSystem (allLeafCompletion G) (Fintype.card V), U.score ≤ T.score := by
    intro U
    rw [T.score_eq_edges_add_iff.mpr hq]
    exact U.score_le_edges_add
  refine ⟨T,hq,hmax,e,(fun _ ↦ rfl),(fun _ ↦ rfl),?_,?_⟩
  · intro i
    exact heq_of_eq (leafWalk_project (P.walk (e i)))
  · intro i z
    exact leafWalk_leaf_support _ z

/-- Under the lifted endpoint indexing, core and leaf owners coincide exactly
at the fixed points of the core permutation. -/
lemma same_owner_iff_fixed {V : Type*} [Fintype V] {G : SimpleGraph V}
    (P : PermutationPathSystem G)
    (T : NormalTrailSystem (allLeafCompletion G) (Fintype.card V))
    (e : Fin (Fintype.card V) ≃ V)
    (ha : ∀ i, T.start i = Sum.inl (e i))
    (hb : ∀ i, T.finish i = Sum.inr ⟨P.perm (e i),Set.mem_univ _⟩) (v : V) :
    NormalTrailSystem.owner T (Sum.inl v) = NormalTrailSystem.owner T (Sum.inr ⟨v,Set.mem_univ _⟩) ↔
      P.perm v = v := by
  let i := e.symm v
  have hai : T.start i = Sum.inl v := (ha i).trans (congrArg Sum.inl (e.apply_symm_apply v))
  have hbi : T.finish i = Sum.inr ⟨P.perm v,Set.mem_univ _⟩ := by
    exact (hb i).trans (congrArg (fun w : V ↦ Sum.inr (⟨P.perm w,Set.mem_univ _⟩ : (Set.univ : Set V))) (e.apply_symm_apply v))
  have hc : NormalTrailSystem.owner T (Sum.inl v) = i :=
    (NormalTrailSystem.endpoint_iff_owner T _ i).mp (Or.inl hai.symm)
  rw [hc]
  constructor
  · intro hh
    have hown := (NormalTrailSystem.endpoint_iff_owner T _ i).mpr hh.symm
    rcases hown with hs | hs
    · rw [hai] at hs
      exact (Sum.inr_ne_inl hs).elim
    · rw [hbi] at hs
      exact (congrArg Subtype.val (Sum.inr.inj hs)).symm
  · intro hh
    symm
    apply (NormalTrailSystem.endpoint_iff_owner T _ i).mp
    right
    rw [hbi,hh]

end Erdos583LeafPermutationDevelopment
