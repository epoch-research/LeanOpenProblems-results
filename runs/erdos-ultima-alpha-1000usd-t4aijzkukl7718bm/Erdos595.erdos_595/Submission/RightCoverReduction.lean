import Submission.RightProperTransversal
import Submission.NegativeInner

/-! Two right-adjoint covering reductions: delete a countably properly
colored set, and restrict to vertices containing all base triangles. -/
set_option autoImplicit false
open Set SimpleGraph
namespace Erdos595RightCoverReduction
open Erdos595ArcAdjoint Erdos595Work Erdos595RightProperTransversal
variable {V C : Type*} (H : SimpleGraph V) (S : Set V)

def restrict (p : Biclique H) : Biclique (H.induce S) :=
  ⟨({x | x.val ∈ p.val.1},{x | x.val ∈ p.val.2}),fun _ hx _ hy => p.property _ hx _ hy⟩

lemma restrict_adj {p q : Biclique H} (h : (right H).Adj p q)
    (h₁ : h.1.choose ∈ S) (h₂ : h.2.choose ∈ S) :
    (right (H.induce S)).Adj (restrict H S p) (restrict H S q) :=
  ⟨⟨⟨h.1.choose,h₁⟩,h.1.choose_spec⟩,⟨⟨h.2.choose,h₂⟩,h.2.choose_spec⟩⟩

/-- Properly countably colored base vertices can be deleted when checking
countable coverability of the right adjoint. -/
theorem delete_colored [Countable C] (c : (H.induce S).Coloring C)
    (hJ : IsCountableUnionOfTriangleFree (right (H.induce Sᶜ))) :
    IsCountableUnionOfTriangleFree (right H) := by
  classical
  obtain ⟨e,he⟩ := exists_injective_nat C
  let enc : Set C ↪ (ℕ → Fin 2) :=
    (⟨fun T => e '' T,Set.image_injective.mpr he⟩ : Set C ↪ Set ℕ).trans Erdos595AllSecondShift.bits
  let f : Biclique H → ℕ → Fin 2 := fun p => enc (code H S c p)
  apply countable_union_of_vertex_pieces (right H) f
  intro i
  let g : vertexPiece (right H) f i →g right (H.induce Sᶜ) :=
    { toFun := restrict H Sᶜ
      map_rel' := by
        intro p q h
        have heq : code H S c p = code H S c q := enc.injective (h.2.1.trans h.2.2.symm)
        apply restrict_adj H Sᶜ h.1
        · exact witness_outside H S c p q heq _ h.1.1.choose_spec.1 h.1.1.choose_spec.2
        · exact witness_outside H S c q p heq.symm _ h.1.2.choose_spec.1 h.1.2.choose_spec.2 }
  exact countable_union_of_hom g hJ

/-- All six witnesses of a right-adjoint triangle lie on base triangles.
Thus a subset containing every base-triangle vertex suffices. -/
theorem triangle_core
    (hS : ∀ a b c, H.Adj a b → H.Adj a c → H.Adj b c → a ∈ S)
    (hJ : IsCountableUnionOfTriangleFree (right (H.induce S))) :
    IsCountableUnionOfTriangleFree (right H) := by
  classical
  obtain ⟨col,hcol⟩ := (countable_union_iff_edge_coloring _).mp hJ
  letI : LinearOrder (Biclique H) := IsWellOrder.linearOrder WellOrderingRel
  let tag (p q : Biclique H) : Option ℕ :=
    if h : (right H).Adj p q then
      if h.1.choose ∈ S ∧ h.2.choose ∈ S then
        some (col s(restrict H S p,restrict H S q)) else none
    else none
  apply Erdos595NegativeInner.cover_of_ordered_patterns (right H) tag
  intro p q r _ _ hpq hpr hqr he
  have x := hpq.1.choose_spec
  have y := hqr.1.choose_spec
  have z := hpr.2.choose_spec
  have x' := hpq.2.choose_spec
  have y' := hqr.2.choose_spec
  have z' := hpr.1.choose_spec
  have hxy := q.property _ x.2 _ y.1
  have hxz := (p.property _ z.2 _ x.1).symm
  have hyz := r.property _ y.2 _ z.1
  have hxy' := (q.property _ y'.2 _ x'.1).symm
  have hxz' := p.property _ x'.2 _ z'.1
  have hyz' := (r.property _ z'.2 _ y'.1).symm
  have hxS := hS _ _ _ hxy hxz hyz
  have hyS := hS _ _ _ hxy.symm hyz hxz
  have hzS := hS _ _ _ hxz.symm hyz.symm hxy
  have hxS' := hS _ _ _ hxy' hxz' hyz'
  have hyS' := hS _ _ _ hxy'.symm hyz' hxz'
  have hzS' := hS _ _ _ hxz'.symm hyz'.symm hxy'
  simp only [tag,dif_pos hpq,dif_pos hpr,dif_pos hqr,
    hxS,hxS',hyS,hyS',hzS,hzS',and_self,if_true,Option.some.injEq] at he
  exact hcol _ _ _ (restrict_adj H S hpq hxS hxS')
    (restrict_adj H S hpr hzS' hzS) (restrict_adj H S hqr hyS hyS') he

#print axioms delete_colored
#print axioms triangle_core
end Erdos595RightCoverReduction
