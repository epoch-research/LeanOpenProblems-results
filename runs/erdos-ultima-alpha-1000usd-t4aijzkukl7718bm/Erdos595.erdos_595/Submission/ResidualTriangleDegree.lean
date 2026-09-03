import Submission.CanonicalPositiveRestriction

/-!
Residual common-neighbor abundance for the canonical edge filter.
This does not construct a proper filter, nor assert that its conditional
fibers are positive for the original edge filter.
-/
set_option autoImplicit false
open Set Filter SimpleGraph
namespace Erdos595ResidualTriangleDegree
open Erdos595Work Erdos595CountableBadEdge Erdos595CanonicalPositive

variable {V : Type} (G R : SimpleGraph V)

/-- Edges with at most continuum many triangle extensions in R. -/
def lowDegree : SimpleGraph V where
  Adj a b := R.Adj a b ∧
    Cardinal.mk {v | R.Adj a v ∧ R.Adj b v} ≤ Cardinal.continuum
  symm := by
    intro a b h
    refine ⟨h.1.symm, ?_⟩
    simpa only [and_comm] using h.2
  loopless := fun a h => h.1.ne rfl

lemma lowDegree_le : lowDegree R ≤ R := fun _ _ h => h.1

/-- This uses the common-neighbor criterion on the low-degree subgraph,
not on all of R. No clique hypothesis is required. -/
theorem lowDegree_cover : IsCountableUnionOfTriangleFree (lowDegree R) := by
  apply countable_union_of_common_neighbors_le_continuum
  intro a b hab
  apply (Cardinal.mk_le_mk_of_subset (show
    {v | (lowDegree R).Adj a v ∧ (lowDegree R).Adj b v} ⊆
      {v | R.Adj a v ∧ R.Adj b v} from ?_)).trans hab.2
  intro v hv
  exact ⟨hv.1.1, hv.2.1⟩

/-- Uniformly for any residual graph, the canonical filter avoids its
low-degree edges. The residual graph need not be a subgraph of G. -/
theorem eventually_not_lowDegree :
    ∀ᶠ e : Edge G in coveringFilter G, ¬(lowDegree R).Adj e.val.1 e.val.2 :=
  avoids_coverable G (coveringFilter G) (coveringFilter_avoids G)
    (lowDegree R) (lowDegree_cover R)

/-- If the residual edge set is large, then almost every original edge has
more than continuum many common neighbors *inside the residual graph*. -/
theorem eventually_many_extensions
    (hR : edges G R ∈ coveringFilter G) :
    ∀ᶠ e : Edge G in coveringFilter G,
      R.Adj e.val.1 e.val.2 ∧
      Cardinal.continuum < Cardinal.mk {v | R.Adj e.val.1 v ∧ R.Adj e.val.2 v} := by
  filter_upwards [hR, eventually_not_lowDegree G R] with e he hn
  exact ⟨he, lt_of_not_ge (fun h => hn ⟨he,h⟩)⟩

/-- The original graph is a special case. Properness is not assumed here;
without it the eventual statement may be vacuous. -/
theorem eventually_many_common_neighbors :
    ∀ᶠ e : Edge G in coveringFilter G,
      Cardinal.continuum < Cardinal.mk {v | G.Adj e.val.1 v ∧ G.Adj e.val.2 v} := by
  have hG : edges G G ∈ coveringFilter G :=
    Filter.Eventually.of_forall fun e => e.property
  filter_upwards [eventually_many_extensions G G hG] with e he
  exact he.2

/-- On a canonically positive residual graph, the same conclusion holds
for its own canonical filter. Exact restriction identifies that filter with
the original filter restricted to the residual edges. -/
theorem positive_residual_many_extensions (hRG : R ≤ G)
    (hR : (coveringFilter G ⊓ Filter.principal (edges G R)).NeBot) :
    ∃ a b, R.Adj a b ∧
      Cardinal.continuum < Cardinal.mk {v | R.Adj a v ∧ R.Adj b v} := by
  have hn : ¬IsCountableUnionOfTriangleFree R :=
    (positive_subgraph_iff G R hRG).mp hR
  letI : (coveringFilter R).NeBot := (coveringFilter_neBot_iff R).mpr hn
  obtain ⟨e,he⟩ := (eventually_many_common_neighbors R).exists
  exact ⟨e.val.1,e.val.2,e.property,he⟩

#print axioms lowDegree_cover
#print axioms eventually_many_extensions
#print axioms positive_residual_many_extensions
end Erdos595ResidualTriangleDegree
