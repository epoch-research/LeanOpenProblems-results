import Submission.ExponentialCandidate
import Submission.FinitePaletteCompactness
import Submission.CountableProductObstruction
import Submission.LocalTupleCover

/-!
Additional restrictions on countable-target exponential candidates. These
are covering theorems for candidate families, not a settlement of Erdős 595.
-/

open SimpleGraph Set
namespace Erdos595ExponentialCompactness
open Erdos595Work Erdos595Exponential Erdos595FinitePalette

/-- Uncountable vertex chromatic number gives a monochromatic edge for
any countable palette. -/
lemma mono_edge {V C : Type*} [Countable C] (B : SimpleGraph V)
    (hB : IsEmpty (B.Coloring ℕ)) (f : V → C) :
    ∃ a b, B.Adj a b ∧ f a = f b := by
  classical
  obtain ⟨enc,henc⟩ := exists_injective_nat C
  by_contra hn
  apply hB.false
  exact SimpleGraph.Coloring.mk (enc ∘ f) (by
    intro a b hab he
    exact hn ⟨a,b,hab,henc he⟩)

/-- Every finite subgraph of the exponential maps to its countable target.
The chosen evaluation point may depend on the finite subgraph. -/
theorem finite_evaluation {V W : Type*} [Countable W]
    (H : SimpleGraph W) (B : SimpleGraph V) (hB : IsEmpty (B.Coloring ℕ))
    (S : Finset (V → W)) :
    Nonempty ((exponential H B hB).induce (S : Set (V → W)) →g H) := by
  classical
  obtain ⟨a,b,hab,he⟩ := mono_edge B hB (fun x => fun f : S => f.val x)
  refine ⟨{ toFun := fun f => f.val a, map_rel' := ?_ }⟩
  intro f g hfg
  have hg : g.val a = g.val b := congrFun he g
  exact hg ▸ hfg a b hab

/-- A finite triangle-free edge palette of the target transfers by compactness.
This statement is deliberately restricted to FINITE palettes. -/
theorem finite_palette {V W C : Type*} [Countable W] [Finite C] [Nonempty C]
    (H : SimpleGraph W) (B : SimpleGraph V) (hB : IsEmpty (B.Coloring ℕ))
    (hH : HasColoring H C) : HasColoring (exponential H B hB) C := by
  apply Erdos595FinitePalette.compactness
  intro S
  exact hH.comap (finite_evaluation H B hB S).some

/-- A countable homomorphism obstruction in the domain already rules out the
candidate. Restrictions give a proper continuum-sized vertex palette. -/
theorem cover_of_countable_obstruction {U V W : Type} [Countable U] [Countable W]
    (K : SimpleGraph U) (H : SimpleGraph W) (B : SimpleGraph V)
    (hB : IsEmpty (B.Coloring ℕ)) (ι : K →g B) (hK : IsEmpty (K →g H)) :
    IsCountableUnionOfTriangleFree (exponential H B hB) := by
  classical
  have hcol : Nonempty ((exponential H B hB).Coloring (U → W)) := by
    refine ⟨SimpleGraph.Coloring.mk (fun f => f ∘ ι) ?_⟩
    intro f g hfg he
    apply hK.false
    refine ⟨f ∘ ι,?_⟩
    intro a b hab
    have hb : f (ι b) = g (ι b) := congrFun he b
    simpa only [Function.comp_apply,← hb] using hfg (ι a) (ι b) (ι.map_adj hab)
  have hcard : Cardinal.mk (U → W) ≤ Cardinal.mk (ℕ → Fin 2) := by
    simpa only [Cardinal.mk_arrow,Cardinal.mk_fin,Cardinal.mk_nat,
      Cardinal.lift_uzero,Nat.cast_ofNat,Cardinal.two_power_aleph0]
      using Erdos595CountableProduct.mk_pi_le_continuum (fun _ : U => W)
  let e : (U → W) ↪ (ℕ → Fin 2) :=
    (Cardinal.lift_mk_le'.mp (by simpa only [Cardinal.lift_uzero] using hcard)).some
  exact countable_union_of_coloring _ ((exponential H B hB).recolorOfEmbedding e hcol.some)

/-- If a domain neighborhood has uncountable vertex chromatic number, then
an exponential triangle cannot have a common value at its center. -/
theorem no_triangle_equal_at_center {V W : Type*} [Countable W]
    (H : SimpleGraph W) (hH : H.CliqueFree 4) (B : SimpleGraph V)
    (hB : IsEmpty (B.Coloring ℕ)) (v : V)
    (hN : IsEmpty ((B.induce (B.neighborSet v)).Coloring ℕ))
    (f g k : V → W) (hfg : (exponential H B hB).Adj f g)
    (hfk : (exponential H B hB).Adj f k)
    (hgk : (exponential H B hB).Adj g k)
    (he₁ : f v = g v) : False := by
  obtain ⟨x,y,hxy,he⟩ := mono_edge (B.induce (B.neighborSet v)) hN
    (fun x => (f x.val,g x.val,k x.val))
  have hg : g x.val = g y.val := congrArg (fun t => t.2.1) he
  have hk : k x.val = k y.val := congrArg (fun t => t.2.2) he
  have hfg' : H.Adj (f x.val) (g x.val) := hg ▸ hfg x.val y.val hxy
  have hfk' : H.Adj (f x.val) (k x.val) := hk ▸ hfk x.val y.val hxy
  have hgk' : H.Adj (g x.val) (k x.val) := hk ▸ hgk x.val y.val hxy
  have hxf : H.Adj (f v) (f x.val) := he₁ ▸ hfg.symm v x.val x.property
  have hxg : H.Adj (f v) (g x.val) := hfg v x.val x.property
  have hxk : H.Adj (f v) (k x.val) := hfk v x.val x.property
  exact no_adj_common_neighbors hH hxf hxg hfg' hxk hfk' hgk'

/-- Therefore a useful domain must have countably vertex-colorable
neighborhoods at every vertex. Triangle-free domains do meet that condition. -/
theorem cover_of_uncountable_neighborhood {V W : Type*} [Countable W]
    (H : SimpleGraph W) (hH : H.CliqueFree 4) (B : SimpleGraph V)
    (hB : IsEmpty (B.Coloring ℕ)) (v : V)
    (hN : IsEmpty ((B.induce (B.neighborSet v)).Coloring ℕ)) :
    IsCountableUnionOfTriangleFree (exponential H B hB) := by
  classical
  apply Erdos595LocalTuple.cover_of_countable_fibers (exponential H B hB) (fun f => f v)
  intro w
  let K := (exponential H B hB).induce {f | f v = w}
  have hK : K.CliqueFree 3 := by
    intro S hS
    obtain ⟨f,g,k,hfg,hfk,hgk,_⟩ := SimpleGraph.is3Clique_iff.mp hS
    exact no_triangle_equal_at_center H hH B hB v hN f.val g.val k.val hfg hfk hgk
      (f.property.trans g.property.symm)
  exact ⟨fun _ => K,fun _ => hK,by simp only [iSup_const]; rfl⟩

#print axioms finite_evaluation
#print axioms finite_palette
#print axioms cover_of_countable_obstruction
#print axioms no_triangle_equal_at_center
#print axioms cover_of_uncountable_neighborhood
end Erdos595ExponentialCompactness
