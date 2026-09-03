import Submission.ExponentialCandidate
import Submission.ArcAdjoint

/-!
Ordered-shift domains do not give a witness through the countable-target
exponential construction. Repeated incoming/outgoing biclique profiles give
a proper vertex palette of size at most the continuum.
-/

open SimpleGraph Set
namespace Erdos595ShiftExponential
open Erdos595Work Erdos595Exponential Erdos595ArcAdjoint

variable {A W : Type*} [LinearOrder A] [Countable W]
    (H : SimpleGraph W) (hB : IsEmpty ((orderedShiftGraph A).Coloring ℕ))

abbrev F := exponential H (orderedShiftGraph A) hB
abbrev Word := {p : A × A // p.1 < p.2} → W

/-- Incoming values may use a neighboring function, while outgoing values
use f itself. This asymmetry makes the two sides a genuine H-biclique. -/
def profile (f : Word (A := A) (W := W)) (a : A) : Biclique H :=
  ⟨({w | ∃ g : Word (A := A) (W := W), (F H hB).Adj g f ∧
      ∃ x, ∃ hx : x < a, g ⟨(x,a),hx⟩ = w},
    {w | ∃ y, ∃ hy : a < y, f ⟨(a,y),hy⟩ = w}), by
      rintro u ⟨g,hgf,x,hx,rfl⟩ v ⟨y,hy,rfl⟩
      exact hgf ⟨(x,a),hx⟩ ⟨(a,y),hy⟩ (Or.inl rfl)⟩

/-- At different indices, profiles of adjacent functions cannot coincide. -/
lemma profile_eq_index {f g : Word (A := A) (W := W)}
    (hfg : (F H hB).Adj f g) {a b : A}
    (he : profile H hB f a = profile H hB g b) : a = b := by
  have hlt : ∀ (f g : Word (A := A) (W := W)), (F H hB).Adj f g →
      ∀ a b, a < b → profile H hB f a ≠ profile H hB g b := by
    intro f g hfg a b hab he
    let w := f ⟨(a,b),hab⟩
    have hwB : w ∈ (profile H hB f a).val.2 := ⟨b,hab,rfl⟩
    have hwA : w ∈ (profile H hB g b).val.1 := ⟨f,hfg,a,hab,rfl⟩
    rw [← he] at hwA
    exact H.loopless w ((profile H hB f a).property w hwA w hwB)
  rcases lt_trichotomy a b with hab | heq | hba
  · exact (hlt f g hfg a b hab he).elim
  · exact heq
  · exact (hlt g f hfg.symm b a hba he.symm).elim

def bicliqueCode (p : Biclique H) : Set (Bool × W) :=
  {x | if x.1 then x.2 ∈ p.val.2 else x.2 ∈ p.val.1}

lemma bicliqueCode_injective : Function.Injective (bicliqueCode H) := by
  intro p q he
  apply Subtype.ext
  apply Prod.ext
  · ext w
    have hh := congrArg (fun S : Set (Bool × W) => (false,w) ∈ S) he
    simpa only [bicliqueCode,mem_setOf_eq,Bool.false_eq_true,if_false] using Iff.of_eq hh
  · ext w
    have hh := congrArg (fun S : Set (Bool × W) => (true,w) ∈ S) he
    simpa only [bicliqueCode,mem_setOf_eq,if_true] using Iff.of_eq hh

/-- Two occurrences of a profile suffice to make that profile a proper
vertex color. The argument does not require H to be K4-free. -/
theorem profile_coloring
    (hA : ∀ t : A → Set (Bool × W), ¬Function.Injective t) :
    Nonempty ((F H hB).Coloring (Set (Bool × W))) := by
  classical
  have hrep : ∀ f : Word (A := A) (W := W),
      ∃ a b, profile H hB f a = profile H hB f b ∧ a ≠ b := by
    intro f
    obtain ⟨a,b,he,hne⟩ := Function.not_injective_iff.mp
      (hA (fun a => bicliqueCode H (profile H hB f a)))
    exact ⟨a,b,bicliqueCode_injective H he,hne⟩
  choose a b he hne using hrep
  refine ⟨SimpleGraph.Coloring.mk (fun f => bicliqueCode H (profile H hB f (a f))) ?_⟩
  intro f g hfg hc
  have hp := bicliqueCode_injective H hc
  have h₁ := profile_eq_index H hB hfg hp
  have h₂ := profile_eq_index H hB hfg ((he f).symm.trans hp)
  exact hne f (h₁.trans h₂.symm)

/-- A countable target makes the profile palette no larger than the continuum. -/
theorem countable_cover {A W : Type} [LinearOrder A] [Countable W]
    (H : SimpleGraph W) (hB : IsEmpty ((orderedShiftGraph A).Coloring ℕ))
    (hA : ∀ t : A → Set (Bool × W), ¬Function.Injective t) :
    IsCountableUnionOfTriangleFree (F H hB) := by
  classical
  have hcard : Cardinal.mk (Set (Bool × W)) ≤ Cardinal.mk (ℕ → Fin 2) := by
    simp only [Cardinal.mk_set,Cardinal.mk_arrow,Cardinal.mk_fin,Cardinal.mk_nat,
      Cardinal.lift_uzero,Nat.cast_ofNat]
    exact Cardinal.power_le_power_left (by simp) Cardinal.mk_le_aleph0
  let e : Set (Bool × W) ↪ (ℕ → Fin 2) :=
    (Cardinal.lift_mk_le'.mp (by simpa only [Cardinal.lift_uzero] using hcard)).some
  exact countable_union_of_coloring _
    ((F H hB).recolorOfEmbedding e (profile_coloring H hB hA).some)

abbrev Index := Set (Set ℕ)
noncomputable instance : LinearOrder Index := IsWellOrder.linearOrder WellOrderingRel

lemma shift_not_colorable : IsEmpty ((orderedShiftGraph Index).Coloring ℕ) := by
  refine ⟨fun c => ?_⟩
  obtain ⟨e⟩ := orderedShiftGraph_coloring_injection c
  exact Function.cantor_injective e e.injective

/-- The standard arbitrarily-high-chromatic shift-domain choice is covered. -/
theorem standard_shift_cover {W : Type} [Countable W] (H : SimpleGraph W) :
    IsCountableUnionOfTriangleFree (F H shift_not_colorable) := by
  classical
  apply countable_cover H shift_not_colorable
  intro t ht
  obtain ⟨e,he⟩ := exists_injective_nat (Bool × W)
  have hs : Function.Injective (fun S : Set (Bool × W) => e '' S) := by
    intro S T hh
    exact (Set.image_injective.mpr he) hh
  exact Function.cantor_injective (fun a : Index => e '' t a) (hs.comp ht)

#print axioms profile_coloring
#print axioms countable_cover
#print axioms standard_shift_cover


/-- A binary encoding of the index order gives a countable proper coloring
of its ordered shift graph. No minimum differing coordinate is needed. -/
theorem shift_coloring_of_binary {A : Type*} [LinearOrder A]
    (e : A → ℕ → Fin 2) (he : Function.Injective e) :
    Nonempty ((orderedShiftGraph A).Coloring ℕ) := by
  classical
  let P := {p : A × A // p.1 < p.2}
  have hd : ∀ p : P, ∃ n, e p.val.1 n ≠ e p.val.2 n := by
    intro p
    by_contra hn
    push_neg at hn
    exact p.property.ne (he (funext hn))
  choose n hn using hd
  obtain ⟨enc,henc⟩ := exists_injective_nat (ℕ × Fin 2)
  refine ⟨SimpleGraph.Coloring.mk (fun p => enc (n p,e p.val.1 (n p))) ?_⟩
  intro p q hpq hpcol
  have hp := henc hpcol
  have hnq : n p = n q := congrArg Prod.fst hp
  have hb : e p.val.1 (n p) = e q.val.1 (n q) := congrArg Prod.snd hp
  rcases hpq with hpq | hqp
  · apply hn p
    simpa only [← hnq,← hpq] using hb
  · apply hn q
    simpa only [hnq,← hqp] using hb.symm

/-- Hence EVERY ordered-shift domain satisfying the exponential's
uncountable-chromatic hypothesis is ruled out, not just the standard index. -/
theorem all_shift_domains_cover {A W : Type} [LinearOrder A] [Countable W]
    (H : SimpleGraph W) (hB : IsEmpty ((orderedShiftGraph A).Coloring ℕ)) :
    IsCountableUnionOfTriangleFree (F H hB) := by
  classical
  apply countable_cover H hB
  intro t ht
  have hcard : Cardinal.mk (Set (Bool × W)) ≤ Cardinal.mk (ℕ → Fin 2) := by
    simp only [Cardinal.mk_set,Cardinal.mk_arrow,Cardinal.mk_fin,Cardinal.mk_nat,
      Cardinal.lift_uzero,Nat.cast_ofNat]
    exact Cardinal.power_le_power_left (by simp) Cardinal.mk_le_aleph0
  let e : Set (Bool × W) ↪ (ℕ → Fin 2) :=
    (Cardinal.lift_mk_le'.mp (by simpa only [Cardinal.lift_uzero] using hcard)).some
  exact hB.false (shift_coloring_of_binary (e ∘ t) (e.injective.comp ht)).some

/-- Exponential graphs are contravariant in the domain. -/
def precomposeHom {U V W : Type*} [Countable W]
    (H : SimpleGraph W) (B : SimpleGraph V) (D : SimpleGraph U)
    (hB : IsEmpty (B.Coloring ℕ)) (hD : IsEmpty (D.Coloring ℕ))
    (j : D →g B) : exponential H B hB →g exponential H D hD where
  toFun f := f ∘ j
  map_rel' := by
    intro f g hfg x y hxy
    exact hfg (j x) (j y) (j.map_adj hxy)

/-- More generally, any domain receiving a high-chromatic ordered-shift
homomorphism is ruled out for every countable target. -/
theorem cover_of_shift_hom {A V W : Type} [LinearOrder A] [Countable W]
    (H : SimpleGraph W) (B : SimpleGraph V) (hB : IsEmpty (B.Coloring ℕ))
    (hS : IsEmpty ((orderedShiftGraph A).Coloring ℕ))
    (j : orderedShiftGraph A →g B) :
    IsCountableUnionOfTriangleFree (exponential H B hB) :=
  countable_union_of_hom (precomposeHom H B (orderedShiftGraph A) hB hS j)
    (all_shift_domains_cover H hS)

#print axioms shift_coloring_of_binary
#print axioms all_shift_domains_cover
#print axioms cover_of_shift_hom

end Erdos595ShiftExponential
