import Submission.FiniteRankUltrafilterFold
import Submission.NoCountableK4Target

/-!
The countable generic K4-free graph has no homomorphism into ANY K4-free
graph with an exact finite-dimensional bilinear orthogonality representation.
The field and target can have arbitrary cardinality. This rules out a proposed
universal geometric representation, not the conjecture in Spec.lean.
-/
set_option autoImplicit false
open SimpleGraph Set Filter
namespace Erdos595GenericFiniteRank
open Erdos595Work Erdos595FiniteRankFold

variable {K E W : Type*} [Field K] [AddCommGroup E] [Module K E]
    [FiniteDimensional K E]

/-- Restrict to the countable image before applying the no-countable-target
obstruction. No cardinal bound on the ambient field or graph is assumed. -/
theorem no_hom (H : SimpleGraph W) (hH : H.CliqueFree 4)
    (B : LinearMap.BilinForm K E) (r : W → E)
    (hr : ∀ a b, H.Adj a b ↔ B (r a) (r b) = 0) :
    ¬Nonempty (Erdos595CountableExtension.G →g H) := by
  classical
  rintro ⟨f⟩
  let S := Set.range f
  haveI : Countable S := (Set.countable_range f).to_subtype
  let T := H.induce S
  have hT : T.CliqueFree 4 := hH.comap (SimpleGraph.Embedding.induce S)
  let f' : Erdos595CountableExtension.G →g T :=
    ⟨fun v => ⟨f v,⟨v,rfl⟩⟩,fun h => f.map_adj h⟩
  have hfin : Erdos595Noetherian.FiniteCommonNeighbors T :=
    finite_common T B (fun v => r v.val) (fun a b => hr a.val b.val)
  let g := (foldHom T hT hfin).comp
    (ultrafilterGraphHom Erdos595CountableExtension.G_cliqueFree hT f')
  exact Erdos595NoCountableK4Target.generic_first_no_countable_target T hT ⟨g⟩

section Unit
open Erdos595IndefiniteUnit
variable (F : Type*) [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- In particular, NONE of the signatures (3,n), over any ordered field,
receives even a non-induced homomorphism from the countable generic graph. -/
theorem no_hom_unit (n : ℕ) :
    ¬Nonempty (Erdos595CountableExtension.G →g graph F 3 n) :=
  no_hom (graph F 3 n) (cliqueFree_four F n) Erdos595IndefiniteFive.bilin
    Subtype.val (fun _ _ => Iff.rfl)
end Unit

#print axioms no_hom
#print axioms no_hom_unit
end Erdos595GenericFiniteRank
