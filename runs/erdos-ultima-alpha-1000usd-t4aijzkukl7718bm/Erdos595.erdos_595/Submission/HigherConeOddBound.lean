import Submission.RightThreeColor

/-! A finite odd-walk bound ensuring K4-freeness at any fixed right-cone stage.
This is only a clique bound, not a non-coverability theorem. -/
set_option autoImplicit false
open SimpleGraph Set
namespace Erdos595HigherConeOddBound
open Erdos595Work Erdos595ArcAdjoint
universe u

variable {A V : Type u}

/-- No odd closed walk shorter than the specified bound. -/
def NoShortOdd (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∀ v, ∀ w : G.Walk v v, w.length < n → ¬Odd w.length

lemma two_of_no_short_odd (H : SimpleGraph A) [Fintype A]
    (h : NoShortOdd H (2 * Fintype.card A)) : H.Colorable 2 := by
  classical
  apply SimpleGraph.colorable_iff_forall_connectedComponents.mpr
  intro c
  obtain ⟨v,hv⟩ := c.nonempty_supp
  let root : c.supp := ⟨v,hv⟩
  let p (a : c.supp) := ((c.connected_toSimpleGraph root a).exists_isPath).choose
  have hp (a : c.supp) : (p a).IsPath :=
    ((c.connected_toSimpleGraph root a).exists_isPath).choose_spec
  have hlen (a : c.supp) : (p a).length < Fintype.card A := by
    exact (hp a).length_lt.trans_le (Fintype.card_subtype_le c.supp)
  refine ⟨fun a => Fin.ofNat 2 (p a).length, ?_⟩
  intro a b hab he
  let w := (((p a).concat hab).append (p b).reverse).map c.toSimpleGraph_hom
  have hw : w.length = (p a).length + 1 + (p b).length := by
    simp [w]
  have he' : (p a).length % 2 = (p b).length % 2 := by
    simpa using congrArg Fin.val he
  apply h v w
  · rw [hw]
    have := hlen a
    have := hlen b
    omega
  · rw [hw]
    apply Nat.odd_iff.mpr
    omega

/-- A homomorphism into a cone with sufficiently large odd girth makes any
finite source three-colorable. -/
lemma three_of_cone_hom (F : SimpleGraph A) [Fintype A] (G : SimpleGraph V)
    (h : NoShortOdd G (2 * Fintype.card A)) (f : F →g coneGraph G) : F.Colorable 3 := by
  classical
  let S : Set A := {a | f a ≠ none}
  have hex (a : S) : ∃ v, f a.val = some v := by
    cases he : f a.val with
    | none => exact (a.property he).elim
    | some v => exact ⟨v,rfl⟩
  let g : (F.induce S) →g G :=
    ⟨fun a => (hex a).choose, by
      intro a b hab
      have hh := f.map_adj hab
      change (coneGraph G).Adj (f a.val) (f b.val) at hh
      rw [(hex a).choose_spec,(hex b).choose_spec] at hh
      exact hh⟩
  have hs : NoShortOdd (F.induce S) (2 * Fintype.card S) := by
    intro a w hw ho
    apply h (g a) (w.map g)
    · rw [SimpleGraph.Walk.length_map]
      exact hw.trans_le (Nat.mul_le_mul_left 2 (Fintype.card_le_of_injective (fun a : S => a.val) Subtype.val_injective))
    · simpa only [SimpleGraph.Walk.length_map] using ho
  obtain ⟨c⟩ := two_of_no_short_odd (F.induce S) hs
  let C : A → Fin 3 := fun a => if ha : f a = none then 2 else (c ⟨a,ha⟩).castSucc
  refine ⟨SimpleGraph.Coloring.mk C ?_⟩
  intro a b hab he
  by_cases ha : f a = none <;> by_cases hb : f b = none
  · have hh := f.map_adj hab
    rw [ha,hb] at hh
    exact hh
  · have hh : (2 : Fin 3) = (c ⟨b,hb⟩).castSucc := by simpa [C,ha,hb] using he
    have hi := (c ⟨b,hb⟩).isLt
    have hh' := congrArg Fin.val hh
    simp at hh'
    omega
  · have hh : (c ⟨a,ha⟩).castSucc = (2 : Fin 3) := by simpa [C,ha,hb] using he
    have hi := (c ⟨a,ha⟩).isLt
    have hh' := congrArg Fin.val hh
    simp at hh'
    omega
  · apply c.valid (show (F.induce S).Adj ⟨a,ha⟩ ⟨b,hb⟩ from hab)
    simpa [C,ha,hb] using he

lemma three_of_arc_three (G : SimpleGraph V) (h : (arcGraph G).Colorable 3) : G.Colorable 3 := by
  obtain ⟨c⟩ := h
  exact ⟨Erdos595RightThree.hom.comp (toRight c)⟩

abbrev Packed := Σ W : Type u, SimpleGraph W

def arcP (p : Packed) : Packed := ⟨Arc p.2,arcGraph p.2⟩
def rightP (p : Packed) : Packed := ⟨Biclique p.2,right p.2⟩
abbrev Hom (p q : Packed) := p.2 →g q.2

theorem iter_hom_iff (n : ℕ) (p q : Packed) :
    Nonempty (Hom ((arcP^[n]) p) q) ↔ Nonempty (Hom p ((rightP^[n]) q)) := by
  induction n generalizing p q with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply' arcP]
    change Nonempty ((arcGraph (((arcP^[n]) p).2)) →g q.2) ↔ _
    rw [Erdos595ArcAdjoint.hom_iff]
    change Nonempty (Hom ((arcP^[n]) p) (rightP q)) ↔ _
    rw [ih,Function.iterate_succ_apply rightP]

lemma iter_finite (n : ℕ) (p : Packed) [Finite p.1] : Finite (((arcP^[n]) p).1) := by
  induction n with
  | zero => assumption
  | succ n ih =>
    rw [Function.iterate_succ_apply' arcP]
    letI := ih
    exact inferInstanceAs (Finite (Arc (((arcP^[n]) p).2)))

lemma iter_three (n : ℕ) (p : Packed) (h : (((arcP^[n]) p).2).Colorable 3) :
    p.2.Colorable 3 := by
  induction n with
  | zero => exact h
  | succ n ih =>
    rw [Function.iterate_succ_apply' arcP] at h
    exact ih (three_of_arc_three _ h)

/-- The fourth clique lives in the same universe as the cone base. -/
abbrev four : Packed := ⟨ULift.{u} (Fin 4), ⊤⟩

lemma four_not_three : ¬four.2.Colorable 3 := by
  intro h
  have hh := h.cliqueFree (by decide : 3 < 4)
  let e : (⊤ : SimpleGraph (Fin 4)) ↪g four.2 :=
    { toFun := ULift.up
      inj' := ULift.up_injective
      map_rel_iff' := by intro a b; simp }
  exact SimpleGraph.not_cliqueFree_of_top_embedding e hh

noncomputable def bound (n : ℕ) : ℕ := 2 * Nat.card (((arcP^[n]) four.{u}).1)

/-- For each fixed n the bound is finite, and no restriction on the cardinality
of G is imposed. This does not assert that the target is non-covered. -/
theorem cliqueFree (n : ℕ) (G : SimpleGraph V) (h : NoShortOdd G (bound.{u} n)) :
    (((rightP^[n]) ⟨Option V,coneGraph G⟩).2).CliqueFree 4 := by
  classical
  haveI := iter_finite n four
  letI : Fintype (((arcP^[n]) four).1) := Fintype.ofFinite _
  by_contra hn
  let e := SimpleGraph.topEmbeddingOfNotCliqueFree hn
  let f : Hom four ((rightP^[n]) ⟨Option V,coneGraph G⟩) :=
    e.toHom.comp ⟨ULift.down,by intro a b hab he; exact hab (ULift.ext _ _ he)⟩
  obtain ⟨g⟩ := (iter_hom_iff n four ⟨Option V,coneGraph G⟩).mpr ⟨f⟩
  apply four_not_three
  apply iter_three n four
  apply three_of_cone_hom (((arcP^[n]) four).2) G _ g
  simpa only [bound,Nat.card_eq_fintype_card] using h

#print axioms three_of_cone_hom
#print axioms cliqueFree
end Erdos595HigherConeOddBound
