import Submission.TriangleComponentProduct
import Submission.SampledFilterProduct

/-!
Countable-coordinate reduced products are coverable when each coordinate
triangle component is countably properly vertex-colorable. The filter
need NOT be countably complete or countably generated. A more general
positive-countable-range hypothesis is sufficient. This is a candidate
exclusion, not a settlement of Erdős 595.
-/
set_option autoImplicit false
open SimpleGraph Set Filter
namespace Erdos595CountableComponentProduct
open Erdos595Work Erdos595CompleteFilterProduct Erdos595TriangleComponentProduct

variable {I : Type*} {A : I → Type*}

/-- Recording countably many coordinate colors only requires that the
sample range MEET every filter-large set; convergence is not required. -/
theorem cover_of_positive_range (F : Filter I) [F.NeBot]
    (G : ∀ i, SimpleGraph (A i)) (hG : ∀ i, Nonempty ((G i).Coloring ℕ))
    (s : ℕ → I) (hs : (F ⊓ Filter.principal (Set.range s)).NeBot) :
    IsCountableUnionOfTriangleFree (graph F G) := by
  classical
  letI : (F ⊓ Filter.principal (Set.range s)).NeBot := hs
  let c : (i : I) → (G i).Coloring ℕ := fun i => (hG i).some
  let label : (∀ i, A i) → ℕ → ℕ := fun x n => c (s n) (x (s n))
  let code : (∀ i, A i) → ℕ → Fin 2 :=
    fun x k => if label x (Nat.unpair k).1 = (Nat.unpair k).2 then 1 else 0
  apply countable_union_of_coloring (graph F G)
  refine SimpleGraph.Coloring.mk code ?_
  intro x y hxy he
  have hAdj : ∀ᶠ i in F ⊓ Filter.principal (Set.range s), (G i).Adj (x i) (y i) :=
    (show F ⊓ Filter.principal (Set.range s) ≤ F from inf_le_left) hxy
  have hRange : ∀ᶠ i in F ⊓ Filter.principal (Set.range s), i ∈ Set.range s :=
    (show F ⊓ Filter.principal (Set.range s) ≤ Filter.principal (Set.range s)
      from inf_le_right) (Filter.mem_principal_self _)
  obtain ⟨i,hi,n,rfl⟩ := (hAdj.and hRange).exists
  have hne : label y n ≠ label x n := fun h => (c (s n)).valid hi h.symm
  have hh := congrFun he (Nat.pair n (label x n))
  simp only [code,Nat.unpair_pair,if_pos rfl,if_neg hne] at hh
  exact (by decide : (1 : Fin 2) ≠ 0) hh

/-- In particular ANY proper filter on a countable index set is covered
by the preceding argument, including nonprincipal ultrafilters. -/
theorem countable_index_cover [Countable I] (F : Filter I) [F.NeBot]
    (G : ∀ i, SimpleGraph (A i)) (hG : ∀ i, Nonempty ((G i).Coloring ℕ)) :
    IsCountableUnionOfTriangleFree (graph F G) := by
  classical
  haveI : Nonempty I := F.nonempty_of_mem Filter.univ_mem |>.to_subtype |>.map Subtype.val
  obtain ⟨s,hs⟩ := exists_surjective_nat I
  apply cover_of_positive_range F G hG s
  simpa only [hs.range_eq,Filter.principal_univ,inf_top_eq] using
    (inferInstance : F.NeBot)

/-- Countable proper colorings are needed only on coordinate TRIANGLE
components, not on the whole coordinate graphs. Different components may
share vertices and there may be arbitrarily many components. -/
theorem components_cover_of_positive_range (F : Filter I) [F.NeBot]
    (G : ∀ i, SimpleGraph (A i))
    (hG : ∀ i q, Nonempty ((piece (G i) q).Coloring ℕ))
    (s : ℕ → I) (hs : (F ⊓ Filter.principal (Set.range s)).NeBot) :
    IsCountableUnionOfTriangleFree (graph F G) := by
  apply cover_of_pieces
  intro q
  obtain ⟨e,rfl⟩ := Quot.exists_rep q
  apply countable_union_of_hom (anchorHom F G e)
  apply cover_of_positive_range F (anchorGraph F G e) ?_ s hs
  intro i
  unfold anchorGraph
  split
  · exact ⟨SimpleGraph.Coloring.mk (fun _ => 0) (fun h => h.elim)⟩
  · exact hG i _

theorem countable_index_components [Countable I] (F : Filter I) [F.NeBot]
    (G : ∀ i, SimpleGraph (A i))
    (hG : ∀ i q, Nonempty ((piece (G i) q).Coloring ℕ)) :
    IsCountableUnionOfTriangleFree (graph F G) := by
  apply cover_of_pieces
  intro q
  obtain ⟨e,rfl⟩ := Quot.exists_rep q
  apply countable_union_of_hom (anchorHom F G e)
  apply countable_index_cover F (anchorGraph F G e)
  intro i
  unfold anchorGraph
  split
  · exact ⟨SimpleGraph.Coloring.mk (fun _ => 0) (fun h => h.elim)⟩
  · exact hG i _

/-- The same componentwise result applies with a convergent sampling
sequence, even when the index set is uncountable. -/
theorem components_cover_of_sampler (F : Filter I) [F.NeBot]
    (G : ∀ i, SimpleGraph (A i))
    (hG : ∀ i q, Nonempty ((piece (G i) q).Coloring ℕ))
    (s : ℕ → I) (hs : Tendsto s atTop F) :
    IsCountableUnionOfTriangleFree (graph F G) := by
  apply cover_of_pieces
  intro q
  obtain ⟨e,rfl⟩ := Quot.exists_rep q
  apply countable_union_of_hom (anchorHom F G e)
  apply Erdos595SampledProduct.cover_of_sampler F (anchorGraph F G e) ?_ s hs
  intro i
  unfold anchorGraph
  split
  · exact ⟨SimpleGraph.Coloring.mk (fun _ => 0) (fun h => h.elim)⟩
  · exact hG i _

#print axioms cover_of_positive_range
#print axioms countable_index_cover
#print axioms countable_index_components
#print axioms components_cover_of_sampler
end Erdos595CountableComponentProduct
