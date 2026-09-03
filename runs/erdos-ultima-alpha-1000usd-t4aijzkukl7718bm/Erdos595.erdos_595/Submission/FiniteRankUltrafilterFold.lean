import Submission.IndefiniteFiveCover
import Submission.NoetherianNeighborhoods
import Submission.GenericUltrafilterUniversality

/-!
Finite-dimensional bilinear orthogonality has finitely determined common
neighborhoods. Every finite mutual-ultrafilter tower folds back to its base.
In particular iteration does not amplify the unresolved signature (3,3)
candidate. This is not a covering theorem for that base and does not settle
Erdős 595.
-/
set_option autoImplicit false
open SimpleGraph Set Filter
namespace Erdos595FiniteRankFold
open Erdos595Work Erdos595Noetherian Erdos595GenericUltrafilterUniversality

variable {K E V : Type*} [Field K] [AddCommGroup E] [Module K E]
    [FiniteDimensional K E]

/-- Only an exact orthogonality representation is required; the vector map
need not be injective and the bilinear form need not be nondegenerate. -/
theorem finite_common (G : SimpleGraph V) (B : LinearMap.BilinForm K E)
    (r : V → E) (h : ∀ a b, G.Adj a b ↔ B (r a) (r b) = 0) :
    FiniteCommonNeighbors G := by
  classical
  intro S
  have hfg : (Submodule.span K (r '' S)).FG :=
    (Submodule.fg_iff_finiteDimensional _).mpr inferInstance
  obtain ⟨T,hT,hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset (r '' S)).mp hfg
  have hex (x : T) : ∃ a : S, r a.val = x.val := by
    obtain ⟨a,ha,he⟩ := hT x.property
    exact ⟨⟨a,ha⟩,he⟩
  choose f hf using hex
  let t : Finset S := Finset.univ.image f
  refine ⟨t,fun w => ⟨?_,?_⟩⟩
  · intro ht a ha
    have hk : Submodule.span K (T : Set E) ≤ LinearMap.ker (B.flip (r w)) := by
      apply Submodule.span_le.mpr
      intro x hx
      change B x (r w) = 0
      have he : r (f ⟨x,hx⟩).val = x := hf ⟨x,hx⟩
      rw [← he]
      exact (h _ w).mp (ht (f ⟨x,hx⟩) (Finset.mem_image.mpr
        ⟨⟨x,hx⟩,Finset.mem_univ _,rfl⟩))
    apply (h a w).mpr
    exact hk (hspan ▸ Submodule.subset_span (show r a ∈ r '' S from ⟨a,ha,rfl⟩))
  · intro ht a _
    exact ht a.val a.property

section Folding
variable (G : SimpleGraph V) (hG : G.CliqueFree 4) (hfin : FiniteCommonNeighbors G)

noncomputable def foldPoint (p : Ultrafilter V) : V := by
  classical
  exact if h : ∃ a, p = pure a then h.choose else
    (trace_has_common_neighbor G hfin p).choose

lemma fold_pure (a : V) : foldPoint G hfin (pure a) = a := by
  classical
  have h : ∃ b : V, (pure a : Ultrafilter V) = pure b := ⟨a,rfl⟩
  rw [foldPoint,dif_pos h]
  exact Ultrafilter.pure_injective h.choose_spec.symm

lemma fold_spec (p : Ultrafilter V) (a : V) (ha : G.neighborSet a ∈ p) :
    G.Adj a (foldPoint G hfin p) := by
  classical
  by_cases hp : ∃ b, p = pure b
  · rw [foldPoint,dif_pos hp]
    rw [hp.choose_spec,Ultrafilter.mem_pure] at ha
    exact ha
  · rw [foldPoint,dif_neg hp]
    exact (trace_has_common_neighbor G hfin p).choose_spec a ha

/-- The fold is chosen to fix all principal points. -/
noncomputable def foldHom : ultrafilterGraph G hG →g G where
  toFun := foldPoint G hfin
  map_rel' := by
    intro p q hpq
    have hm : G.neighborSet (foldPoint G hfin p) ∈ q :=
      Filter.mem_of_superset hpq.2 (fun a ha => (fold_spec G hfin p a ha).symm)
    exact fold_spec G hfin q _ hm

def pureHom : G →g ultrafilterGraph G hG where
  toFun := pure
  map_rel' := by
    intro a b hab
    change fubiniAdj G (pure a) (pure b) ∧ fubiniAdj G (pure b) (pure a)
    simpa only [fubiniAdj,Ultrafilter.mem_pure,Set.mem_setOf_eq,
      SimpleGraph.mem_neighborSet] using And.intro hab hab.symm

noncomputable def towerFold : (n : ℕ) → (tower G hG n).val →g G
  | 0 => SimpleGraph.Hom.id
  | n+1 => (foldHom G hG hfin).comp
      (ultrafilterGraphHom (tower G hG n).property hG (towerFold n))

def intoTower : (n : ℕ) → G →g (tower G hG n).val
  | 0 => SimpleGraph.Hom.id
  | n+1 => (pureHom (tower G hG n).val (tower G hG n).property).comp (intoTower n)

/-- This is a genuine retraction along the iterated principal embedding. -/
theorem retract (n : ℕ) (v : V) : towerFold G hG hfin n (intoTower G hG n v) = v := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change foldPoint G hfin
      (Ultrafilter.map (towerFold G hG hfin n)
        (pure (intoTower G hG n v))) = v
    rw [Ultrafilter.map_pure,fold_pure,ih]

include hfin in
/-- Every finite stage has exactly the same countable-coverability status
as its base, not just an upper bound inherited in one direction. -/
theorem tower_cover_iff (n : ℕ) :
    IsCountableUnionOfTriangleFree (tower G hG n).val ↔ IsCountableUnionOfTriangleFree G :=
  ⟨countable_union_of_hom (intoTower G hG n),countable_union_of_hom (towerFold G hG hfin n)⟩
end Folding

section Indefinite
open Erdos595IndefiniteUnit
variable (F : Type*) [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- No Archimedean or cardinality bound on the ordered field is needed. -/
theorem unit_finite_common (m n : ℕ) : FiniteCommonNeighbors (graph F m n) :=
  finite_common (graph F m n) Erdos595IndefiniteFive.bilin Subtype.val (fun _ _ => Iff.rfl)

noncomputable def unitTowerFold (n k : ℕ) :
    (tower (graph F 3 n) (cliqueFree_four F n) k).val →g graph F 3 n :=
  towerFold (graph F 3 n) (cliqueFree_four F n) (unit_finite_common F 3 n) k

/-- In particular k iterations over signature (3,3) do not improve on the
original unresolved candidate. This does NOT assert either side. -/
theorem unit_tower_cover_iff (n k : ℕ) :
    IsCountableUnionOfTriangleFree (tower (graph F 3 n) (cliqueFree_four F n) k).val ↔
      IsCountableUnionOfTriangleFree (graph F 3 n) :=
  tower_cover_iff _ _ (unit_finite_common F 3 n) k
end Indefinite

#print axioms finite_common
#print axioms retract
#print axioms unit_tower_cover_iff
end Erdos595FiniteRankFold
