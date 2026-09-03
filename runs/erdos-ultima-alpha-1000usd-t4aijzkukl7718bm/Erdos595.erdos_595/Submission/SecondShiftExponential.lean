import Submission.DirectedRightTower
import Submission.ExponentialCandidate
import Submission.MiddleCornerObstruction

/-!
The second ordered-shift exponential has a directed two-stage profile.
For a triangle-free countable target and a suitable canonical index order,
this gives a countable proper vertex coloring. No conclusion for a general
K4-free target, and no settlement of Erdős 595, is asserted.
-/

set_option autoImplicit false
open SimpleGraph Set
namespace Erdos595SecondShiftExponential
open Erdos595DirectedRight Erdos595Exponential Erdos595MiddleCorner

variable {A W : Type*} [LinearOrder A] [Countable W]
    (H : SimpleGraph W) (hB : IsEmpty ((oneGraph A).Coloring ℕ))

abbrev F := exponential H (oneGraph A) hB
abbrev Word := Triple A → W

def productRel (x y : Word (A := A) (W := W) × A) : Prop :=
  (F H hB).Adj x.1 y.1 ∧ x.2 < y.2

abbrev PArc := Erdos595DirectedRight.Arc (productRel H hB)
abbrev PArc₂ := Erdos595DirectedRight.Arc (arc (productRel H hB))

def triple (e : PArc₂ H hB) : Triple A :=
  ⟨e.val.1.val.1.2,e.val.1.val.2.2,e.val.2.val.2.2,e.val.1.property.2,by
    have he : e.val.1.val.2 = e.val.2.val.1 := e.property
    rw [he]
    exact e.val.2.property.2⟩

def eval (e : PArc₂ H hB) : W := e.val.2.val.2.1 (triple H hB e)

lemma eval_rel (e d : PArc₂ H hB) (hed : arc (arc (productRel H hB)) e d) :
    H.Adj (eval H hB e) (eval H hB d) := by
  have hed' : e.val.2 = d.val.1 := hed
  have he : e.val.1.val.2 = e.val.2.val.1 := e.property
  have hd : d.val.1.val.2 = d.val.2.val.1 := d.property
  have hlast : e.val.2.val.2 = d.val.2.val.1 := by rw [hed']; exact hd
  have hfg : (F H hB).Adj e.val.2.val.2.1 d.val.2.val.2.1 := by
    rw [hlast]
    exact d.val.2.property.1
  apply hfg (triple H hB e) (triple H hB d)
  apply Or.inl
  constructor
  · change e.val.1.val.2.2 = d.val.1.val.1.2
    rw [he,hed']
  · change e.val.2.val.2.2 = d.val.1.val.2.2
    rw [hed']

def firstProfile (e : PArc H hB) : Erdos595DirectedRight.Biclique H.Adj :=
  curry (eval H hB) (eval_rel H hB) e

lemma firstProfile_rel (e d : PArc H hB) (hed : arc (productRel H hB) e d) :
    right H.Adj (firstProfile H hB e) (firstProfile H hB d) :=
  curry_rel (eval H hB) (eval_rel H hB) hed

def profile (x : Word (A := A) (W := W) × A) :
    Erdos595DirectedRight.Biclique (right H.Adj) :=
  curry (firstProfile H hB) (firstProfile_rel H hB) x

lemma profile_rel {x y : Word (A := A) (W := W) × A} (hxy : productRel H hB x y) :
    right (right H.Adj) (profile H hB x) (profile H hB y) :=
  curry_rel (firstProfile H hB) (firstProfile_rel H hB) hxy

/-- A repeated value occurs arbitrarily far to the right. -/
def CofinalRepeats (A C : Type*) [LT A] : Prop :=
  ∀ f : A → C, ∃ c, ∀ a, ∃ b, a < b ∧ f b = c

/-- Cofinal profiles give both arrows, so final mutualization is justified. -/
noncomputable def profileHom [Nonempty A]
    (hA : CofinalRepeats A (Erdos595DirectedRight.Biclique (right H.Adj))) :
    F H hB →g twice H := by
  classical
  choose p hp using fun f : Word (A := A) (W := W) => hA (fun a => profile H hB (f,a))
  refine ⟨p,?_⟩
  intro f g hfg
  have hdir : ∀ f g, (F H hB).Adj f g → right (right H.Adj) (p f) (p g) := by
    intro f g hfg
    obtain ⟨a,_,ha⟩ := hp f (Classical.arbitrary A)
    obtain ⟨b,hab,hb⟩ := hp g a
    rw [← ha,← hb]
    exact profile_rel H hB ⟨hfg,hab⟩
  exact ⟨hdir f g hfg,hdir g f hfg.symm⟩

/-- This is a proper VERTEX coloring, not merely a triangle-free edge cover. -/
theorem countable_coloring_of_cofinal [Nonempty A]
    (hH : H.CliqueFree 3)
    (hA : CofinalRepeats A (Erdos595DirectedRight.Biclique (right H.Adj))) :
    Nonempty ((F H hB).Coloring ℕ) := by
  obtain ⟨c⟩ := twice_countable_coloring H hH
  exact ⟨c.comp (profileHom H hB hA)⟩

/-- A successor-cardinal index provides cofinal repetition for the given palette. -/
abbrev Index (C : Type) := (Order.succ (max Cardinal.aleph0 (Cardinal.mk C))).ord.ToType

noncomputable instance (C : Type) : LinearOrder (Index C) := inferInstance

lemma index_card (C : Type) : Cardinal.mk (Index C) = Order.succ (max Cardinal.aleph0 (Cardinal.mk C)) :=
  Cardinal.mk_ord_toType _

instance index_infinite (C : Type) : Infinite (Index C) := by
  apply Cardinal.infinite_iff.mpr
  rw [index_card]
  exact (le_max_left _ _).trans (Order.le_succ _)

instance index_noMax (C : Type) : NoMaxOrder (Index C) :=
  Cardinal.noMaxOrder ((le_max_left _ _).trans (Order.le_succ _))

lemma index_cofinal (C : Type) : CofinalRepeats (Index C) C := by
  classical
  let κ := Order.succ (max Cardinal.aleph0 (Cardinal.mk C))
  have hk : Cardinal.IsRegular κ := Cardinal.isRegular_succ (le_max_left _ _)
  intro f
  have hInf : Cardinal.aleph0 ≤ Cardinal.mk (Index C) :=
    Cardinal.infinite_iff.mp inferInstance
  have hCod : Cardinal.mk C < (Cardinal.mk (Index C)).ord.cof := by
    rw [index_card]
    change Cardinal.mk C < κ.ord.cof
    rw [hk.cof_eq]
    exact (le_max_right _ _).trans_lt (Order.lt_succ _)
  obtain ⟨c,hc⟩ := Cardinal.infinite_pigeonhole f hInf hCod
  refine ⟨c,?_⟩
  intro a
  obtain ⟨b,hab⟩ := exists_gt a
  by_contra hn
  push_neg at hn
  have hi : ∀ x : f ⁻¹' {c}, x.val < b := by
    intro x
    by_contra hxb
    exact hn x.val (hab.trans_le (le_of_not_gt hxb)) x.property
  let e : (f ⁻¹' {c}) ↪ Set.Iio b :=
    ⟨fun x => ⟨x.val,hi x⟩,by
      intro x y h
      apply Subtype.ext
      exact congrArg (fun z : Set.Iio b => (z : Index C)) h⟩
  have hle := Cardinal.mk_le_of_injective e.injective
  rw [hc,index_card] at hle
  exact (Cardinal.mk_Iio_ord_toType b).not_ge hle

/-- The two-fold profile palette, with enough extra coordinates to make the
second-shift domain uncountably chromatic. -/
abbrev Palette {W : Type} (H : SimpleGraph W) :=
  Erdos595DirectedRight.Biclique (right H.Adj) × Set (Set ℕ)

abbrev CanonicalIndex {W : Type} (H : SimpleGraph W) := Index (Palette H)

lemma canonical_not_colorable {W : Type} (H : SimpleGraph W) :
    IsEmpty ((oneGraph (CanonicalIndex H)).Coloring ℕ) := by
  classical
  refine ⟨fun c => ?_⟩
  obtain ⟨d⟩ := triple_gives_shift_coloring c (by
    intro a b x y hab hbx hxy
    exact c.valid (Or.inl ⟨rfl,rfl⟩))
  obtain ⟨e⟩ := Erdos595Work.orderedShiftGraph_coloring_injection d
  have hle := Cardinal.mk_le_of_injective e.injective
  let p : Erdos595DirectedRight.Biclique (right H.Adj) := ⟨(∅,∅),by simp⟩
  have hp : Cardinal.mk (Set (Set ℕ)) ≤ Cardinal.mk (Palette H) :=
    Cardinal.mk_le_of_injective (show Function.Injective (fun s : Set (Set ℕ) => (p,s))
      from fun _ _ h => congrArg Prod.snd h)
  rw [index_card] at hle
  exact (Order.lt_succ (max Cardinal.aleph0 (Cardinal.mk (Palette H)))).not_ge
    (hle.trans (hp.trans (le_max_right _ _)))

lemma canonical_cofinal {W : Type} (H : SimpleGraph W) :
    CofinalRepeats (CanonicalIndex H) (Erdos595DirectedRight.Biclique (right H.Adj)) := by
  intro f
  obtain ⟨c,hc⟩ := index_cofinal (Palette H) (fun a => (f a,∅))
  refine ⟨c.1,fun a => ?_⟩
  obtain ⟨b,hab,hb⟩ := hc a
  exact ⟨b,hab,congrArg Prod.fst hb⟩

/-- An explicit second-shift exponential has a countable proper vertex
coloring whenever its countable target is triangle-free. -/
theorem canonical_countable_coloring {W : Type} [Countable W]
    (H : SimpleGraph W) (hH : H.CliqueFree 3) :
    Nonempty ((F H (canonical_not_colorable H)).Coloring ℕ) :=
  countable_coloring_of_cofinal H (canonical_not_colorable H) hH (canonical_cofinal H)

#print axioms canonical_not_colorable
#print axioms canonical_countable_coloring


#print axioms profileHom
#print axioms countable_coloring_of_cofinal
#print axioms index_cofinal
end Erdos595SecondShiftExponential
