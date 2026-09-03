import Submission.RightTowerCountableCover
import Submission.RightFiberCover

/-!
A countable locally finite base has a cone whose first biclique right adjoint
folds into a countable graph. Consequently its K4-free fourth right stage is
countably triangle-free edge-covered. This excludes a candidate family; it
does not settle Erdős 595.
-/

set_option autoImplicit false
open SimpleGraph Set
open scoped Classical
namespace Erdos595LocallyFiniteConeRight
open Erdos595Work Erdos595ArcAdjoint

variable {V : Type*} (B : SimpleGraph V)
abbrev P := Biclique (coneGraph B)

private def emptyPoint : P B := ⟨(∅,∅),by simp⟩

private def apexLeft : P B :=
  ⟨({none},{x | x ≠ none}),by
    intro a ha b hb
    have ha' : a = none := ha
    subst a
    cases b with
    | none => exact (hb rfl).elim
    | some b => trivial⟩

private def apexRight : P B :=
  ⟨({x | x ≠ none},{none}),by
    intro a ha b hb
    have hb' : b = none := hb
    subst b
    cases a with
    | none => exact (ha rfl).elim
    | some a => trivial⟩

abbrev Code (V : Type*) := (Finset (Option V) × Finset (Option V)) ⊕ Bool

private noncomputable def realize : Code V → P B
  | .inl s => if h : ∀ a ∈ s.1, ∀ b ∈ s.2, (coneGraph B).Adj a b
      then ⟨((s.1 : Set (Option V)),(s.2 : Set (Option V))),h⟩ else emptyPoint B
  | .inr false => apexLeft B
  | .inr true => apexRight B

private def FiniteSides (p : P B) : Prop := p.val.1.Finite ∧ p.val.2.Finite

private lemma finite_left (hB : ∀ v, (B.neighborSet v).Finite)
    (p : P B) {b : V} (hb : some b ∈ p.val.2) : p.val.1.Finite := by
  apply ((Set.finite_singleton none).union ((hB b).image some)).subset
  intro a ha
  cases a with
  | none => exact Or.inl rfl
  | some a =>
    apply Or.inr
    exact ⟨a,(p.property _ ha _ hb).symm,rfl⟩

private lemma finite_right (hB : ∀ v, (B.neighborSet v).Finite)
    (p : P B) {a : V} (ha : some a ∈ p.val.1) : p.val.2.Finite := by
  apply ((Set.finite_singleton none).union ((hB a).image some)).subset
  intro b hb
  cases b with
  | none => exact Or.inl rfl
  | some b => exact Or.inr ⟨b,p.property _ ha _ hb,rfl⟩

private lemma some_of_not_subset {S : Set (Option V)} (h : ¬S ⊆ {none}) :
    ∃ a : V, some a ∈ S := by
  classical
  obtain ⟨a,ha,hn⟩ := Set.not_subset.mp h
  cases a with
  | none => exact (hn rfl).elim
  | some a => exact ⟨a,ha⟩

private lemma classification (hB : ∀ v, (B.neighborSet v).Finite)
    (p : P B) (hp : ¬FiniteSides B p) :
    p.val.1 ⊆ {none} ∨ p.val.2 ⊆ {none} := by
  classical
  by_cases h : p.val.1 ⊆ {none}
  · exact Or.inl h
  · apply Or.inr
    by_contra h'
    obtain ⟨a,ha⟩ := some_of_not_subset h
    obtain ⟨b,hb⟩ := some_of_not_subset h'
    exact hp ⟨finite_left B hB p hb,finite_right B hB p ha⟩

private noncomputable def code (p : P B) : Code V := by
  classical
  exact if h : FiniteSides B p then .inl (h.1.toFinset,h.2.toFinset)
    else if p.val.1 ⊆ {none} then .inr false else .inr true

private lemma realize_finite (p : P B) (h : FiniteSides B p) :
    realize B (.inl (h.1.toFinset,h.2.toFinset)) = p := by
  classical
  have hc : ∀ a ∈ h.1.toFinset, ∀ b ∈ h.2.toFinset, (coneGraph B).Adj a b := by
    intro a ha b hb
    exact p.property a (h.1.mem_toFinset.mp ha) b (h.2.mem_toFinset.mp hb)
  simp only [realize,dif_pos hc]
  apply Subtype.ext
  exact Prod.ext h.1.coe_toFinset h.2.coe_toFinset

private lemma enlarged (hB : ∀ v, (B.neighborSet v).Finite)
    (p : P B) (hL : p.val.1.Nonempty) (hR : p.val.2.Nonempty) :
    p.val.1 ⊆ (realize B (code B p)).val.1 ∧
      p.val.2 ⊆ (realize B (code B p)).val.2 := by
  classical
  by_cases hf : FiniteSides B p
  · rw [code,dif_pos hf,realize_finite B p hf]
    exact ⟨Subset.rfl,Subset.rfl⟩
  · rw [code,dif_neg hf]
    by_cases hl : p.val.1 ⊆ {none}
    · rw [if_pos hl]
      change p.val.1 ⊆ {none} ∧ p.val.2 ⊆ {x | x ≠ none}
      refine ⟨hl,?_⟩
      obtain ⟨a,ha⟩ := hL
      have ha' : a = none := hl ha
      subst a
      intro b hb he
      subst b
      exact (coneGraph B).loopless none (p.property _ ha _ hb)
    · rw [if_neg hl]
      have hr : p.val.2 ⊆ {none} := (classification B hB p hf).resolve_left hl
      change p.val.1 ⊆ {x | x ≠ none} ∧ p.val.2 ⊆ {none}
      refine ⟨?_,hr⟩
      obtain ⟨b,hb⟩ := hR
      have hb' : b = none := hr hb
      subst b
      intro a ha he
      subst a
      exact (coneGraph B).loopless none (p.property _ ha _ hb)

/-- The target is explicitly countable when V is countable. -/
noncomputable def target : SimpleGraph (Code V) := (right (coneGraph B)).comap (realize B)

/-- Enlargement of both biclique sides preserves all mutual intersections. -/
noncomputable def fold (hB : ∀ v, (B.neighborSet v).Finite) :
    right (coneGraph B) →g target B where
  toFun := code B
  map_rel' := by
    intro p q hpq
    obtain ⟨a,haP,haQ⟩ := hpq.1
    obtain ⟨b,hbQ,hbP⟩ := hpq.2
    have hp := enlarged B hB p ⟨b,hbP⟩ ⟨a,haP⟩
    have hq := enlarged B hB q ⟨a,haQ⟩ ⟨b,hbQ⟩
    exact ⟨⟨a,hp.2 haP,hq.1 haQ⟩,⟨b,hq.2 hbQ,hp.1 hbP⟩⟩

/-- A reverse homomorphism is needed to transfer the clique hypothesis. -/
noncomputable def unfoldHom : target B →g right (coneGraph B) :=
  SimpleGraph.Hom.comap _ _

abbrev Fourth := right (right (right (right (coneGraph B))))

/-- A countable locally finite cone cannot be a witness at its fourth stage. -/
theorem fourth_cover [Countable V] (hB : ∀ v, (B.neighborSet v).Finite)
    (h4 : (Fourth B).CliqueFree 4) : IsCountableUnionOfTriangleFree (Fourth B) := by
  let f := Erdos595RightFiber.rightHom
    (Erdos595RightFiber.rightHom (Erdos595RightFiber.rightHom (fold B hB)))
  let g := Erdos595RightFiber.rightHom
    (Erdos595RightFiber.rightHom (Erdos595RightFiber.rightHom (unfoldHom B)))
  have ht : (right (right (right (target B)))).CliqueFree 4 := by
    classical
    by_contra hn
    let e := SimpleGraph.topEmbeddingOfNotCliqueFree hn
    let j := g.comp e.toHom
    exact no_adj_common_neighbors h4 (j.map_adj (show (0 : Fin 4) ≠ 1 by decide))
      (j.map_adj (show (0 : Fin 4) ≠ 2 by decide))
      (j.map_adj (show (1 : Fin 4) ≠ 2 by decide))
      (j.map_adj (show (0 : Fin 4) ≠ 3 by decide))
      (j.map_adj (show (1 : Fin 4) ≠ 3 by decide))
      (j.map_adj (show (2 : Fin 4) ≠ 3 by decide))
  exact countable_union_of_hom f
    (Erdos595RightTowerCountable.third_right_countable_cover (target B) ht)

#print axioms fold
#print axioms fourth_cover
end Erdos595LocallyFiniteConeRight
