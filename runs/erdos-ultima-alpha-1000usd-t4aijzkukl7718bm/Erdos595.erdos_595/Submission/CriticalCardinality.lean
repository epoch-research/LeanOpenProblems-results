import Submission.VertexCoverFilter

/-!
A cardinal-minimal obstruction, if one exists, has cofinality greater than
continuum. This is a necessary condition, not a reflection bound or a
settlement of Erdős 595.
-/

set_option autoImplicit false
open Set SimpleGraph Cardinal
namespace Erdos595CriticalCardinality
open Erdos595Work Erdos595VertexCoverFilter

variable {V : Type} (G : SimpleGraph V)

/-- A small cofinal family of smaller induced graphs suffices. No clique
assumption is required for this closure assertion. -/
theorem cover_of_small_cofinality [Infinite V]
    (hsmall : ∀ S : Set V, Cardinal.mk S < Cardinal.mk V → On G S)
    (hcof : (Cardinal.mk V).ord.cof ≤ Cardinal.continuum) :
    IsCountableUnionOfTriangleFree G := by
  classical
  let κ := Cardinal.mk V
  let A := κ.ord.ToType
  let e : V ≃ A := (Cardinal.eq.mp (Cardinal.mk_ord_toType κ).symm).some
  have hκ : Cardinal.aleph0 ≤ κ := Cardinal.infinite_iff.mp inferInstance
  obtain ⟨S,hS,hcard⟩ := Ordinal.cof_eq (α := A) (· < ·)
  have hcard' : Cardinal.mk S ≤ Cardinal.continuum := by
    rw [hcard,Ordinal.type_toType]
    exact hcof
  obtain ⟨enc⟩ := binary_embedding hcard'
  let T : S → Set V := fun s => {v | e v ≤ s.val}
  have hT : ∀ s, On G (T s) := by
    intro s
    apply hsmall
    have hi : Cardinal.mk (Set.Iic s.val) < κ := by
      have he : Set.Iic s.val = insert s.val (Set.Iio s.val) := by
        ext x
        simp [le_iff_lt_or_eq]
      rw [he]
      exact Cardinal.mk_insert_le.trans_lt (Cardinal.add_lt_of_lt hκ
        (Cardinal.mk_Iio_ord_toType s.val)
        (Cardinal.one_lt_aleph0.trans_le hκ))
    let f : T s ↪ Set.Iic s.val :=
      ⟨fun v => ⟨e v.val,v.property⟩,fun v w h => Subtype.ext
        (e.injective (congrArg Subtype.val h))⟩
    exact (Cardinal.mk_le_of_injective f.injective).trans_lt hi
  have hall : (⋃ s, T s) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro v
    obtain ⟨s,hs,hvs⟩ := hS (e v)
    exact Set.mem_iUnion.mpr ⟨⟨s,hs⟩,le_of_not_gt hvs⟩
  have hc := on_iUnion G enc T hT
  rw [hall,on_univ_iff] at hc
  exact hc

/-- This does not assert that an obstruction exists, nor that it reflects
to a graph below any fixed cardinal. -/
theorem critical_cofinality [Infinite V]
    (hsmall : ∀ S : Set V, Cardinal.mk S < Cardinal.mk V → On G S)
    (hbad : ¬IsCountableUnionOfTriangleFree G) :
    Cardinal.continuum < (Cardinal.mk V).ord.cof := by
  exact lt_of_not_ge (fun h => hbad (cover_of_small_cofinality G hsmall h))

/-- The elementary size bound does not use the clique restriction. -/
theorem continuum_lt_size (hbad : ¬IsCountableUnionOfTriangleFree G) :
    Cardinal.continuum < Cardinal.mk V := by
  apply lt_of_not_ge
  intro h
  obtain ⟨e⟩ := binary_embedding h
  exact hbad (countable_union_of_binary_encoding G e e.injective)

lemma on_induce_of_image (S : Set V) (T : Set S)
    (h : On G (Subtype.val '' T)) : On (G.induce S) T := by
  apply (on_iff_induce (G.induce S) T).mpr
  let f : ((G.induce S).induce T) →g G.induce (Subtype.val '' T) :=
    ⟨fun v => ⟨v.val.val,⟨v.val,v.property,rfl⟩⟩,fun h => h⟩
  exact countable_union_of_hom f ((on_iff_induce G _).mp h)

/-- Minimize only among induced subgraphs of the given obstruction. No
proper-class choice of a graph, or global reflection hypothesis, is used. -/
theorem exists_minimal_induced (hbad : ¬IsCountableUnionOfTriangleFree G) :
    ∃ S : Set V, ¬On G S ∧
      ∀ T : Set V, Cardinal.mk T < Cardinal.mk S → On G T := by
  classical
  let C : Set Cardinal := {κ | ∃ S : Set V, Cardinal.mk S = κ ∧ ¬On G S}
  have hC : C.Nonempty :=
    ⟨Cardinal.mk (Set.univ : Set V),Set.univ,rfl,by
      simpa only [on_univ_iff] using hbad⟩
  obtain ⟨S,hS,hbadS⟩ := Cardinal.lt_wf.min_mem C hC
  refine ⟨S,hbadS,?_⟩
  intro T hTS
  by_contra hT
  exact Cardinal.lt_wf.not_lt_min C hC ⟨T,rfl,hT⟩ (hTS.trans_eq hS)

/-- Every hypothetical obstruction contains a cardinal-minimal induced
obstruction with cofinality strictly above the continuum. This is conditional
on the input obstruction and is not an existence proof for one. -/
theorem exists_critical_induced (hbad : ¬IsCountableUnionOfTriangleFree G) :
    ∃ S : Set V,
      ¬IsCountableUnionOfTriangleFree (G.induce S) ∧
      (∀ T : Set S, Cardinal.mk T < Cardinal.mk S → On (G.induce S) T) ∧
      Cardinal.continuum < (Cardinal.mk S).ord.cof := by
  classical
  obtain ⟨S,hS,hmin⟩ := exists_minimal_induced G hbad
  have hbadS : ¬IsCountableUnionOfTriangleFree (G.induce S) :=
    fun h => hS ((on_iff_induce G S).mpr h)
  have hsmall : ∀ T : Set S, Cardinal.mk T < Cardinal.mk S → On (G.induce S) T := by
    intro T hT
    apply on_induce_of_image
    apply hmin
    exact Cardinal.mk_image_le.trans_lt hT
  haveI : Infinite S := Cardinal.infinite_iff.mpr
    (Cardinal.aleph0_lt_continuum.trans (continuum_lt_size (G.induce S) hbadS)).le
  exact ⟨S,hbadS,hsmall,critical_cofinality (G.induce S) hsmall hbadS⟩

/-- The K4-free hypothesis is retained by taking this induced subgraph. -/
theorem exists_critical_cliqueFree (hG : G.CliqueFree 4)
    (hbad : ¬IsCountableUnionOfTriangleFree G) :
    ∃ S : Set V, (G.induce S).CliqueFree 4 ∧
      ¬IsCountableUnionOfTriangleFree (G.induce S) ∧
      (∀ T : Set S, Cardinal.mk T < Cardinal.mk S → On (G.induce S) T) ∧
      Cardinal.continuum < (Cardinal.mk S).ord.cof := by
  obtain ⟨S,hS,hmin,hcof⟩ := exists_critical_induced G hbad
  exact ⟨S,hG.comap (SimpleGraph.Embedding.induce S),hS,hmin,hcof⟩

#print axioms cover_of_small_cofinality
#print axioms critical_cofinality
#print axioms exists_critical_cliqueFree
end Erdos595CriticalCardinality
