import Submission.ArcShiftCertificateChunked
import Submission.ArcTwoCover

/-!
A K4-preserving construction for the biclique right adjoint. Triangles of a
base graph may be confined to separate fibers; a four-clique in the right
adjoint must then already occur over one fiber. The cross-fiber construction
below does not produce a witness: the companion RightFiberCover.lean also
proves preservation of countable coverability.
-/

open SimpleGraph Set
namespace Erdos595TriangleFiber
open Erdos595ArcAdjoint Erdos595Work

variable {V W I C : Type*}

/-- Each triangle lies entirely in a fiber of f. -/
def TrianglesInFibers (G : SimpleGraph V) (f : V → I) : Prop :=
  ∀ a b c, G.Adj a b → G.Adj a c → G.Adj b c → f a = f b ∧ f a = f c

private abbrev E (a b : Fin 4) (h : a ≠ b) : Arc (⊤ : SimpleGraph (Fin 4)) :=
  ⟨(a,b),h⟩

/-- The triangles of arc(K4) are connected through their vertices. -/
theorem arc_four_triangle_constant
    (f : Arc (⊤ : SimpleGraph (Fin 4)) → I)
    (hf : TrianglesInFibers (arcGraph (⊤ : SimpleGraph (Fin 4))) f) :
    ∀ e, f e = f (E 0 1 (by decide)) := by
  have h012 := hf (E 0 1 (by decide)) (E 1 2 (by decide)) (E 2 0 (by decide))
    (by simp [arcGraph, E]) (by simp [arcGraph, E]) (by simp [arcGraph, E])
  have h013 := hf (E 0 1 (by decide)) (E 1 3 (by decide)) (E 3 0 (by decide))
    (by simp [arcGraph, E]) (by simp [arcGraph, E]) (by simp [arcGraph, E])
  have h123 := hf (E 1 2 (by decide)) (E 2 3 (by decide)) (E 3 1 (by decide))
    (by simp [arcGraph, E]) (by simp [arcGraph, E]) (by simp [arcGraph, E])
  have h203 := hf (E 2 0 (by decide)) (E 0 3 (by decide)) (E 3 2 (by decide))
    (by simp [arcGraph, E]) (by simp [arcGraph, E]) (by simp [arcGraph, E])
  have h132 := hf (E 1 3 (by decide)) (E 3 2 (by decide)) (E 2 1 (by decide))
    (by simp [arcGraph, E]) (by simp [arcGraph, E]) (by simp [arcGraph, E])
  have h302 := hf (E 3 0 (by decide)) (E 0 2 (by decide)) (E 2 3 (by decide))
    (by simp [arcGraph, E]) (by simp [arcGraph, E]) (by simp [arcGraph, E])
  have h021 := hf (E 0 2 (by decide)) (E 2 1 (by decide)) (E 1 0 (by decide))
    (by simp [arcGraph, E]) (by simp [arcGraph, E]) (by simp [arcGraph, E])
  rintro ⟨⟨a,b⟩,hab⟩
  change a ≠ b at hab
  fin_cases a <;> fin_cases b <;> first | exact (hab rfl).elim | grind only

/-- If all triangles lie in individual fibers, the right-adjoint K4 test
reduces to those fibers. This allows arbitrary additional cross-fiber edges
as long as they do not create a mixed triangle. -/
theorem right_cliqueFree_of_fibers (G : SimpleGraph V) (f : V → I)
    (hf : TrianglesInFibers G f)
    (hG : ∀ i, (right (G.induce {a | f a = i})).CliqueFree 4) :
    (right G).CliqueFree 4 := by
  by_contra hn
  obtain ⟨F⟩ := (right_not_cliqueFree_iff G 4).mp hn
  have hconst : ∀ e, f (F e) = f (F (E 0 1 (by decide))) :=
    arc_four_triangle_constant (f ∘ F) (fun a b c hab hac hbc =>
      hf (F a) (F b) (F c) (F.map_adj hab) (F.map_adj hac) (F.map_adj hbc))
  let F' : arcGraph (⊤ : SimpleGraph (Fin 4)) →g
      G.induce {a | f a = f (F (E 0 1 (by decide)))} :=
    { toFun e := ⟨F e,hconst e⟩
      map_rel' h := F.map_adj h }
  exact ((right_not_cliqueFree_iff _ 4).mpr ⟨F'⟩) (hG _)

lemma right_cliqueFree_of_hom {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G →g H) (hH : (right H).CliqueFree 4) : (right G).CliqueFree 4 := by
  by_contra hn
  obtain ⟨F⟩ := (right_not_cliqueFree_iff G 4).mp hn
  exact ((right_not_cliqueFree_iff H 4).mpr ⟨f.comp F⟩) hH

/-- Copies of H indexed by B, with cross-edges joining equal c-colors.
The map c will be assumed proper on H, but its palette can be arbitrary. -/
def glue (H : SimpleGraph V) (B : SimpleGraph I) (c : V → C) :
    SimpleGraph (V × I) where
  Adj p q := (p.2 = q.2 ∧ H.Adj p.1 q.1) ∨ (B.Adj p.2 q.2 ∧ c p.1 = c q.1)
  symm := fun _ _ h => h.elim
    (fun h => Or.inl ⟨h.1.symm,h.2.symm⟩)
    (fun h => Or.inr ⟨h.1.symm,h.2.symm⟩)
  loopless := fun _ h => h.elim (fun h => H.loopless _ h.2) (fun h => B.loopless _ h.1)

lemma glue_same_fiber (H : SimpleGraph V) (B : SimpleGraph I) (c : V → C)
    {p q : V × I} (he : p.2 = q.2) (h : (glue H B c).Adj p q) : H.Adj p.1 q.1 := by
  rcases h with h | h
  · exact h.2
  · exact (h.1.ne he).elim

/-- Properness of c rules out triangles using two fibers, and triangle-
freeness of B rules out triangles using three fibers. -/
theorem glue_triangles (H : SimpleGraph V) (B : SimpleGraph I) (c : V → C)
    (hc : ∀ a b, H.Adj a b → c a ≠ c b) (hB : B.CliqueFree 3) :
    TrianglesInFibers (glue H B c) Prod.snd := by
  classical
  intro p q r hpq hpr hqr
  rcases hpq with hpq | hpq <;> rcases hpr with hpr | hpr <;>
    rcases hqr with hqr | hqr
  · exact ⟨hpq.1,hpr.1⟩
  · exact ⟨hpq.1,hpr.1⟩
  · exact ⟨hpq.1,hpq.1.trans hqr.1⟩
  · exact (hc _ _ hpq.2 (hpr.2.trans hqr.2.symm)).elim
  · exact ⟨hpr.1.trans hqr.1.symm,hpr.1⟩
  · exact (hc _ _ hpr.2 (hpq.2.trans hqr.2)).elim
  · exact (hc _ _ hqr.2 (hpq.2.symm.trans hpr.2)).elim
  · exact (hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨hpq.1,hpr.1,hqr.1⟩)).elim

/-- The cross-fiber gluing preserves K4-freeness AFTER taking the right
adjoint, provided it held for the right adjoint of H. -/
theorem right_glue_cliqueFree (H : SimpleGraph V) (B : SimpleGraph I) (c : V → C)
    (hc : ∀ a b, H.Adj a b → c a ≠ c b) (hB : B.CliqueFree 3)
    (hH : (right H).CliqueFree 4) : (right (glue H B c)).CliqueFree 4 := by
  apply right_cliqueFree_of_fibers _ Prod.snd (glue_triangles H B c hc hB)
  intro i
  let F : (glue H B c).induce {p | p.2 = i} →g H :=
    { toFun p := p.1.1
      map_rel' := by
        intro p q hpq
        exact glue_same_fiber H B c (p.2.trans q.2.symm) hpq }
  exact right_cliqueFree_of_hom F hH

/-- The base gluing remains coverable whenever H is. This says nothing
about covering its right adjoint. -/
theorem glue_cover (H : SimpleGraph V) (B : SimpleGraph I) (c : V → C)
    (hc : ∀ a b, H.Adj a b → c a ≠ c b) (hB : B.CliqueFree 3)
    (hH : IsCountableUnionOfTriangleFree H) :
    IsCountableUnionOfTriangleFree (glue H B c) := by
  obtain ⟨col,hcol⟩ := (countable_union_iff_edge_coloring H).mp hH
  apply (countable_union_iff_edge_coloring _).mpr
  refine ⟨fun e => col (e.map Prod.fst), ?_⟩
  intro p q r hpq hpr hqr he
  obtain ⟨h₁,h₂⟩ := glue_triangles H B c hc hB p q r hpq hpr hqr
  exact hcol p.1 q.1 r.1 (glue_same_fiber H B c h₁ hpq)
    (glue_same_fiber H B c h₂ hpr)
    (glue_same_fiber H B c (h₁.symm.trans h₂) hqr) he

/-- Taking the source of a directed arc is a graph homomorphism. -/
def sourceHom (R : SimpleGraph V) : arcGraph R →g R where
  toFun p := p.1.1
  map_rel' := by
    intro p q h
    rcases h with h | h
    · simpa only [h] using p.2
    · simpa only [h] using q.2.symm

abbrev arcSourceGlue (R : SimpleGraph V) (B : SimpleGraph I) :=
  glue (arcGraph R) B (fun p => p.1.1)

/-- A concrete family whose right adjoint is rigorously K4-free. The source
palette and triangle-free index graph may both have arbitrarily large size. -/
theorem right_arcSourceGlue_cliqueFree (R : SimpleGraph V) (B : SimpleGraph I)
    (hR : (right R).CliqueFree 4) (hB : B.CliqueFree 3) :
    (right (arcSourceGlue R B)).CliqueFree 4 := by
  apply right_glue_cliqueFree _ _ _ (fun a b h => ((sourceHom R).map_adj h).ne) hB
  exact right_cliqueFree_of_hom (sourceHom R) hR

theorem right_arcSourceGlue_shift_cliqueFree (A : Type*) [LinearOrder A]
    (B : SimpleGraph I) (hB : B.CliqueFree 3) :
    (right (arcSourceGlue (Erdos595MiddleCorner.graph A) B)).CliqueFree 4 :=
  right_arcSourceGlue_cliqueFree _ B (Erdos595ArcShift.right_shift_cliqueFree A) hB

#print axioms arc_four_triangle_constant
#print axioms right_cliqueFree_of_fibers
#print axioms right_glue_cliqueFree
#print axioms glue_cover
#print axioms right_arcSourceGlue_shift_cliqueFree
end Erdos595TriangleFiber
