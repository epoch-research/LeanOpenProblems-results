import Submission.CountableCoordinateRepresentation
import Submission.CountableGenericUniversality

/-!
A constant-target reduced-power normal form for arbitrary K4-free graphs.
The filter is proper and countably complete, but is NOT claimed to be an
ultrafilter. This is a reduction, not a settlement of Erdős 595.
-/

open SimpleGraph Set Filter
namespace Erdos595FixedGenericReducedPower

open Erdos595Work
namespace Coordinate
open Erdos595CountableCoordinate

variable {V : Type*} (G : SimpleGraph V) (hG : G.CliqueFree 4) (v₀ : V)

/-- Countable universality is applied to each countable induced coordinate,
not to a merely countably vertex-colorable graph. -/
noncomputable def model (s : Index V) :
    coordinate G v₀ s ↪g Erdos595CountableExtension.G :=
  (Erdos595CountableGenericUniversality.universal_countable
    (coordinate G v₀ s) (coordinate_cliqueFree G v₀ hG s)).some

/-- Unlike the earlier representation, every factor is the SAME graph. -/
def power : SimpleGraph (Index V → Erdos595CountableExtension.Vertex) :=
  Erdos595CompleteFilterProduct.graph (fine V) (fun _ => Erdos595CountableExtension.G)

noncomputable def point (x : V) (s : Index V) : Erdos595CountableExtension.Vertex :=
  model G hG v₀ s (project v₀ x s)

lemma point_adj_iff (x y : V) :
    (power (V := V)).Adj (point G hG v₀ x) (point G hG v₀ y) ↔ G.Adj x y := by
  have he : (power (V := V)).Adj (point G hG v₀ x) (point G hG v₀ y) ↔
      (product G v₀).Adj (project v₀ x) (project v₀ y) := by
    change (∀ᶠ s in fine V,
        Erdos595CountableExtension.G.Adj (model G hG v₀ s (project v₀ x s))
          (model G hG v₀ s (project v₀ y s))) ↔
      (∀ᶠ s in fine V, (coordinate G v₀ s).Adj (project v₀ x s) (project v₀ y s))
    simp only [RelEmbedding.map_rel_iff]
  exact he.trans (project_adj_iff G v₀ x y)

lemma point_injective : Function.Injective (point G hG v₀) := by
  intro x y h
  let s : Index V := ⟨{x,y},by simp⟩
  have he := (model G hG v₀ s).injective (congrFun h s)
  have hv := congrArg Subtype.val he
  simpa only [project_of_mem v₀ x s (by simp [s]),
    project_of_mem v₀ y s (by simp [s])] using hv

noncomputable def embedding : G ↪g power (V := V) where
  toFun := point G hG v₀
  inj' := point_injective G hG v₀
  map_rel_iff' := point_adj_iff G hG v₀ _ _

lemma power_cliqueFree : (power (V := V)).CliqueFree 4 :=
  product_cliqueFree (fine V) (fun _ => Erdos595CountableExtension.G) 4
    (fun _ => Erdos595CountableExtension.G_cliqueFree)

include hG v₀ in
lemma no_cover_preserved (h : ¬IsCountableUnionOfTriangleFree G) :
    ¬IsCountableUnionOfTriangleFree (power (V := V)) :=
  fun hp => h (countable_union_of_hom (embedding G hG v₀).toHom hp)

end Coordinate

universe u

/-- Universal coverability is equivalent to coverability of proper
countably complete reduced powers of ONE fixed countable K4-free graph.
Neither side of this equivalence is established here. -/
theorem all_cover_iff_fixed_reduced_powers :
    (∀ (V : Type u) (G : SimpleGraph V), G.CliqueFree 4 →
      IsCountableUnionOfTriangleFree G) ↔
    (∀ (I : Type u) (F : Filter I) [F.NeBot] [CountableInterFilter F],
      IsCountableUnionOfTriangleFree
        (Erdos595CompleteFilterProduct.graph F
          (fun _ => Erdos595CountableExtension.G))) := by
  constructor
  · intro h I F hF hC
    exact h _ _ (Erdos595CountableCoordinate.product_cliqueFree F
      (fun _ => Erdos595CountableExtension.G) 4
      (fun _ => Erdos595CountableExtension.G_cliqueFree))
  · intro h V G hG
    classical
    cases isEmpty_or_nonempty V with
    | inl hv =>
      refine ⟨fun _ => G,?_,by simp⟩
      intro n s hs
      obtain ⟨a,b,c,hab,hac,hbc,he⟩ := SimpleGraph.is3Clique_iff.mp hs
      exact isEmptyElim a
    | inr hv =>
      exact countable_union_of_hom
        (Coordinate.embedding G hG (Classical.choice hv)).toHom
        (h (Erdos595CountableCoordinate.Index V) (Erdos595CountableCoordinate.fine V))


/-- It is enough even to use the canonical fine filter on countable
subsets, one reduced power for each index carrier V. The power itself is
independent of the graph to be embedded. -/
theorem all_cover_iff_fine_powers :
    (∀ (V : Type u) (G : SimpleGraph V), G.CliqueFree 4 →
      IsCountableUnionOfTriangleFree G) ↔
    (∀ (V : Type u), IsCountableUnionOfTriangleFree (Coordinate.power (V := V))) := by
  constructor
  · intro h V
    exact h _ _ Coordinate.power_cliqueFree
  · intro h V G hG
    classical
    cases isEmpty_or_nonempty V with
    | inl hv =>
      refine ⟨fun _ => G,?_,by simp⟩
      intro n s hs
      obtain ⟨a,b,c,hab,hac,hbc,he⟩ := SimpleGraph.is3Clique_iff.mp hs
      exact isEmptyElim a
    | inr hv =>
      exact countable_union_of_hom
        (Coordinate.embedding G hG (Classical.choice hv)).toHom (h V)

#print axioms all_cover_iff_fine_powers

#print axioms Coordinate.embedding
#print axioms Coordinate.power_cliqueFree
#print axioms Coordinate.no_cover_preserved
#print axioms all_cover_iff_fixed_reduced_powers
end Erdos595FixedGenericReducedPower
