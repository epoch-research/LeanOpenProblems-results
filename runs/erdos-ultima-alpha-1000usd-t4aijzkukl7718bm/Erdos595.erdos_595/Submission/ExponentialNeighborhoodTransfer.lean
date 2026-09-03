import Submission.SecondShiftExponential
import Submission.LocalChromaticProduct

/-!
Restriction of exponential neighborhoods to monochromatic domain copies.
The second-shift application below is conditional on a homogeneous-copy
hypothesis; no infinite Erdős--Rado theorem or settlement is asserted.
-/

set_option autoImplicit false
open SimpleGraph Set
namespace Erdos595ExponentialNeighborhood
open Erdos595Exponential

variable {U V W : Type*} [Countable W]

/-- Restriction lands in the target neighborhood because every domain
vertex has a neighbor. No external profile vertices are used. -/
def restrictionHom (H : SimpleGraph W) (B : SimpleGraph V)
    (hB : IsEmpty (B.Coloring ℕ)) (D : SimpleGraph U)
    (hD : IsEmpty (D.Coloring ℕ)) (hno : ∀ x, ∃ y, D.Adj y x)
    (g : V → W) (w : W) (j : D →g B) (hj : ∀ x, g (j x) = w) :
    ((exponential H B hB).induce ((exponential H B hB).neighborSet g)) →g
      exponential (H.induce (H.neighborSet w)) D hD where
  toFun f x := ⟨f.val (j x), by
    obtain ⟨y,hy⟩ := hno x
    have h := f.property (j y) (j x) (j.map_adj hy)
    simpa only [hj y] using h⟩
  map_rel' := by
    intro f₁ f₂ h x y hxy
    exact h (j x) (j y) (j.map_adj hxy)

theorem neighborhood_coloring (H : SimpleGraph W) (B : SimpleGraph V)
    (hB : IsEmpty (B.Coloring ℕ)) (D : SimpleGraph U)
    (hD : IsEmpty (D.Coloring ℕ)) (hno : ∀ x, ∃ y, D.Adj y x)
    (g : V → W) (w : W) (j : D →g B) (hj : ∀ x, g (j x) = w)
    (hc : Nonempty ((exponential (H.induce (H.neighborSet w)) D hD).Coloring ℕ)) :
    Nonempty (((exponential H B hB).induce
      ((exponential H B hB).neighborSet g)).Coloring ℕ) := by
  obtain ⟨c⟩ := hc
  exact ⟨c.comp (restrictionHom H B hB D hD hno g w j hj)⟩

/-- The monochromatic domain and its carrier may depend on the target value. -/
theorem cover_of_homogeneous_domains {U : W → Type*}
    (H : SimpleGraph W) (B : SimpleGraph V) (hB : IsEmpty (B.Coloring ℕ))
    (D : ∀ w, SimpleGraph (U w)) (hD : ∀ w, IsEmpty ((D w).Coloring ℕ))
    (hno : ∀ w x, ∃ y, (D w).Adj y x)
    (hc : ∀ w, Nonempty ((exponential (H.induce (H.neighborSet w))
      (D w) (hD w)).Coloring ℕ))
    (hRamsey : ∀ g : V → W, ∃ (w : W) (j : D w →g B), ∀ x, g (j x) = w) :
    Erdos595Work.IsCountableUnionOfTriangleFree (exponential H B hB) := by
  apply Erdos595LocalChromaticProduct.cover_of_neighborhood_colorings
  intro g
  obtain ⟨w,j,hj⟩ := hRamsey g
  exact neighborhood_coloring H B hB (D w) (hD w) (hno w) g w j hj (hc w)

open Erdos595MiddleCorner Erdos595SecondShiftExponential

lemma oneGraph_no_isolated {A : Type*} [LinearOrder A] [NoMaxOrder A]
    (x : Triple A) : ∃ y, (oneGraph A).Adj y x := by
  obtain ⟨d,hd⟩ := exists_gt x.c
  exact ⟨⟨x.b,x.c,d,x.bc,hd⟩,Or.inr ⟨rfl,rfl⟩⟩

omit [Countable W] in
lemma neighborhood_triangleFree (H : SimpleGraph W) (hH : H.CliqueFree 4) (w : W) :
    (H.induce (H.neighborSet w)).CliqueFree 3 := by
  classical
  intro s hs
  obtain ⟨a,b,c,hab,hac,hbc,_⟩ := SimpleGraph.is3Clique_iff.mp hs
  have hcl : H.IsNClique 4 {w,a.val,b.val,c.val} := by
    refine ⟨?_,?_⟩
    · intro x hx y hy hxy
      simp only [Finset.mem_coe,Finset.mem_insert,Finset.mem_singleton] at hx hy
      rcases hx with rfl | rfl | rfl | rfl <;>
        rcases hy with rfl | rfl | rfl | rfl <;>
        first | exact (hxy rfl).elim | exact a.property | exact b.property |
          exact c.property | exact a.property.symm | exact b.property.symm |
          exact c.property.symm | exact hab | exact hab.symm | exact hac |
          exact hac.symm | exact hbc | exact hbc.symm
    · have hwa := a.property.ne
      have hwb := b.property.ne
      have hwc := c.property.ne
      have hab' : a.val ≠ b.val := (show H.Adj a.val b.val from hab).ne
      have hac' : a.val ≠ c.val := (show H.Adj a.val c.val from hac).ne
      have hbc' : b.val ≠ c.val := (show H.Adj b.val c.val from hbc).ne
      simp [hwa,hwb,hwc,hab',hac',hbc']
  exact hH _ hcl

/-- The sufficient Ramsey hypothesis is about increasing triples, with an
order embedding of a genuinely large canonical index for each target
neighborhood. It is stronger than finite homogeneous-set Ramsey. -/
theorem secondShift_cover_of_homogeneous_triples {W : Type} [Countable W]
    {A : Type*} [LinearOrder A] (H : SimpleGraph W) (hH : H.CliqueFree 4)
    (hB : IsEmpty ((oneGraph A).Coloring ℕ))
    (hRamsey : ∀ g : Triple A → W, ∃ (w : W)
      (e : CanonicalIndex (H.induce (H.neighborSet w)) ↪o A),
      ∀ a b c (hab : a < b) (hbc : b < c),
        g ⟨e a,e b,e c,e.strictMono hab,e.strictMono hbc⟩ = w) :
    Erdos595Work.IsCountableUnionOfTriangleFree (exponential H (oneGraph A) hB) := by
  apply cover_of_homogeneous_domains H (oneGraph A) hB
    (fun w => oneGraph (CanonicalIndex (H.induce (H.neighborSet w))))
    (fun w => canonical_not_colorable (H.induce (H.neighborSet w)))
    (fun _ => oneGraph_no_isolated)
    (fun w => canonical_countable_coloring _ (neighborhood_triangleFree H hH w))
  intro g
  obtain ⟨w,e,he⟩ := hRamsey g
  let j : oneGraph (CanonicalIndex (H.induce (H.neighborSet w))) →g oneGraph A :=
    { toFun := fun x => ⟨e x.a,e x.b,e x.c,e.strictMono x.ab,e.strictMono x.bc⟩
      map_rel' := by
        intro x y h
        rcases h with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
        · exact Or.inl ⟨congrArg e h₁,congrArg e h₂⟩
        · exact Or.inr ⟨congrArg e h₁,congrArg e h₂⟩ }
  exact ⟨w,j,fun x => he x.a x.b x.c x.ab x.bc⟩

#print axioms restrictionHom
#print axioms cover_of_homogeneous_domains
#print axioms secondShift_cover_of_homogeneous_triples
end Erdos595ExponentialNeighborhood
