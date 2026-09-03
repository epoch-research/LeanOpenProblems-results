import Submission.ExponentialNeighborhoodTransfer
import Submission.InfiniteTripleRamsey

/-!
Sufficiently large second-shift exponentials with countable K4-free targets
have countable triangle-free edge covers. This is a candidate exclusion,
not a proof of universal coverability or a settlement of Erdős 595.
-/
set_option autoImplicit false
open SimpleGraph Set
namespace Erdos595LargeSecondShiftExponential
open Erdos595Exponential Erdos595MiddleCorner Erdos595SecondShiftExponential
open Erdos595ExponentialNeighborhood

universe u

theorem order_family_from_noninjection {I : Type u} (T : I → Type u)
    [∀ i, LinearOrder (T i)] [∀ i, WellFoundedLT (T i)] (X : Type u)
    (hX : ¬Nonempty (X ↪ Sigma T)) :
    ∃ (_ : LinearOrder X) (_ : WellFoundedLT X), ∀ i, Nonempty (T i ↪o X) := by
  classical
  letI : LinearOrder X := IsWellOrder.linearOrder WellOrderingRel
  letI : WellFoundedLT X := ⟨(inferInstance : IsWellOrder X WellOrderingRel).wf⟩
  refine ⟨inferInstance,inferInstance,fun i => ?_⟩
  rcases InitialSeg.total (fun a b : T i => a < b) (fun a b : X => a < b) with e | e
  · exact ⟨OrderEmbedding.ofStrictMono e (fun _ _ h => e.map_rel_iff.mpr h)⟩
  · apply False.elim
    apply hX
    refine ⟨⟨fun x => ⟨i,e x⟩,?_⟩⟩
    intro x y h
    apply e.injective
    simpa only [Sigma.mk.inj_iff,heq_eq_eq,true_and] using h

/-- A single well order contains ordered copies of every member of a family. -/
theorem order_family_host {I : Type u} (T : I → Type u)
    [∀ i, LinearOrder (T i)] [∀ i, WellFoundedLT (T i)] :
    ∃ (X : Type u) (_ : LinearOrder X) (_ : WellFoundedLT X),
      ∀ i, Nonempty (T i ↪o X) := by
  obtain ⟨o,w,h⟩ := order_family_from_noninjection T (Set (Sigma T)) (by
    rintro ⟨e⟩
    exact Function.cantor_injective e e.injective)
  exact ⟨_,o,w,h⟩

def oneGraphMap {A X : Type*} [LinearOrder A] [LinearOrder X] (e : A ↪o X) :
    oneGraph A →g oneGraph X where
  toFun x := ⟨e x.a,e x.b,e x.c,e.strictMono x.ab,e.strictMono x.bc⟩
  map_rel' := by
    intro x y h
    rcases h with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
    · exact Or.inl ⟨congrArg e h₁,congrArg e h₂⟩
    · exact Or.inr ⟨congrArg e h₁,congrArg e h₂⟩

/-- An actual domain map gives the contravariant restriction homomorphism. -/
def precomposeHom {U V W : Type*} [Countable W]
    (H : SimpleGraph W) (B : SimpleGraph U) (D : SimpleGraph V)
    (hB : IsEmpty (B.Coloring ℕ)) (hD : IsEmpty (D.Coloring ℕ)) (j : B →g D) :
    exponential H D hD →g exponential H B hB where
  toFun f := f ∘ j
  map_rel' := fun h a b hab => h (j a) (j b) (j.map_adj hab)

theorem cover_of_domain_hom {U V W : Type*} [Countable W]
    (H : SimpleGraph W) (B : SimpleGraph U) (D : SimpleGraph V)
    (hB : IsEmpty (B.Coloring ℕ)) (hD : IsEmpty (D.Coloring ℕ)) (j : B →g D)
    (hc : Erdos595Work.IsCountableUnionOfTriangleFree (exponential H B hB)) :
    Erdos595Work.IsCountableUnionOfTriangleFree (exponential H D hD) :=
  Erdos595Work.countable_union_of_hom (precomposeHom H B D hB hD j) hc

/-- A uniform host for monochromatic copies of all canonical neighborhood
indices. Infinite-target triple Ramsey, rather than finite Ramsey, is used. -/
theorem homogeneous_triples_host {W : Type} [Countable W] [Nonempty W]
    (H : SimpleGraph W) :
    ∃ (A : Type) (_ : LinearOrder A) (_ : WellFoundedLT A),
      ∀ g : Triple A → W, ∃ (w : W)
        (e : CanonicalIndex (H.induce (H.neighborSet w)) ↪o A),
        ∀ a b c (hab : a < b) (hbc : b < c),
          g ⟨e a,e b,e c,e.strictMono hab,e.strictMono hbc⟩ = w := by
  classical
  obtain ⟨X,oX,wX,hX⟩ := order_family_host
    (fun w => CanonicalIndex (H.induce (H.neighborSet w)))
  letI : LinearOrder X := oX
  letI : WellFoundedLT X := wX
  obtain ⟨A,oA,wA,hA⟩ := Erdos595InfiniteTripleRamsey.triple_ramsey_host X W
  letI : LinearOrder A := oA
  letI : WellFoundedLT A := wA
  refine ⟨A,oA,wA,?_⟩
  intro g
  let c : A → A → A → W := fun a b t =>
    if h : a < b ∧ b < t then g ⟨a,b,t,h.1,h.2⟩ else Classical.arbitrary W
  obtain ⟨f,w,hf⟩ := hA c
  obtain ⟨e⟩ := hX w
  refine ⟨w,e.trans f,?_⟩
  intro a b t hab hbt
  have h := hf (e a) (e b) (e t) (e.strictMono hab) (e.strictMono hbt)
  have hlt : f (e a) < f (e b) ∧ f (e b) < f (e t) :=
    ⟨f.strictMono (e.strictMono hab),f.strictMono (e.strictMono hbt)⟩
  simpa only [c,dif_pos hlt] using h

/-- For every countable nonempty K4-free target, at least one genuinely
uncountably chromatic second-shift domain has a coverable exponential. -/
theorem exists_covered_domain {W : Type} [Countable W] [Nonempty W]
    (H : SimpleGraph W) (hH : H.CliqueFree 4) :
    ∃ (A : Type) (_ : LinearOrder A) (_ : WellFoundedLT A)
      (hB : IsEmpty ((oneGraph A).Coloring ℕ)),
      Erdos595Work.IsCountableUnionOfTriangleFree (exponential H (oneGraph A) hB) := by
  classical
  obtain ⟨A,oA,wA,hA⟩ := homogeneous_triples_host H
  letI : LinearOrder A := oA
  letI : WellFoundedLT A := wA
  obtain ⟨w,e,_⟩ := hA (fun _ => Classical.arbitrary W)
  have hB : IsEmpty ((oneGraph A).Coloring ℕ) := ⟨fun c =>
    (canonical_not_colorable (H.induce (H.neighborSet w))).false
      (c.comp (oneGraphMap e))⟩
  exact ⟨A,oA,wA,hB,secondShift_cover_of_homogeneous_triples H hH hB hA⟩

/-- All larger ordered domains containing this host are excluded as well.
There is deliberately no conclusion for smaller or intermediate domains. -/
theorem exists_eventual_cover {W : Type} [Countable W] [Nonempty W]
    (H : SimpleGraph W) (hH : H.CliqueFree 4) :
    ∃ (A : Type) (_ : LinearOrder A) (_ : WellFoundedLT A),
      IsEmpty ((oneGraph A).Coloring ℕ) ∧
      ∀ (X : Type) (_ : LinearOrder X) (_e : A ↪o X),
        ∃ hX : IsEmpty ((oneGraph X).Coloring ℕ),
          Erdos595Work.IsCountableUnionOfTriangleFree (exponential H (oneGraph X) hX) := by
  obtain ⟨A,oA,wA,hA,hcover⟩ := exists_covered_domain H hH
  letI : LinearOrder A := oA
  letI : WellFoundedLT A := wA
  refine ⟨A,oA,wA,hA,?_⟩
  intro X oX e
  letI : LinearOrder X := oX
  have hX : IsEmpty ((oneGraph X).Coloring ℕ) :=
    ⟨fun c => hA.false (c.comp (oneGraphMap e))⟩
  exact ⟨hX,cover_of_domain_hom H (oneGraph A) (oneGraph X) hA hX
    (oneGraphMap e) hcover⟩

#print axioms order_family_host
#print axioms homogeneous_triples_host
#print axioms exists_covered_domain
#print axioms exists_eventual_cover
end Erdos595LargeSecondShiftExponential
