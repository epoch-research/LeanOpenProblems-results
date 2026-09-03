import Submission.CompleteFilterProduct

/-!
A countable sampling sequence rules out reduced-product witnesses with
countably vertex-colourable coordinates. This includes countably generated
proper filters on arbitrarily large index sets. Auxiliary to Erdős 595.
-/

set_option autoImplicit false
open Set Filter SimpleGraph
namespace Erdos595SampledProduct
open Erdos595CompleteFilterProduct

variable {I : Type*} {A : I → Type*}

/-- A proper countably generated filter has a sequence converging to it. -/
theorem exists_sampler (F : Filter I) [F.NeBot] [F.IsCountablyGenerated] :
    ∃ s : ℕ → I, Tendsto s atTop F := by
  classical
  obtain ⟨B,hB⟩ := F.exists_antitone_basis
  have hne (n : ℕ) : (B n).Nonempty := Filter.nonempty_of_mem (hB.mem n)
  let s : ℕ → I := fun n => (hne n).choose
  refine ⟨s,?_⟩
  intro U hU
  change ∀ᶠ n in atTop, s n ∈ U
  obtain ⟨k,hk⟩ := hB.mem_iff.mp hU
  apply Filter.eventually_atTop.mpr
  exact ⟨k,fun n hkn => hk (hB.antitone hkn (hne n).choose_spec)⟩

/-- Sampling along a countable sequence and recording coordinate vertex
colours gives a continuum-sized proper colouring, hence a countable
triangle-free edge cover. The original index set can be arbitrarily large. -/
theorem cover_of_sampler (F : Filter I) [F.NeBot]
    (G : ∀ i, SimpleGraph (A i))
    (hG : ∀ i, Nonempty ((G i).Coloring ℕ))
    (s : ℕ → I) (hs : Tendsto s atTop F) :
    Erdos595Work.IsCountableUnionOfTriangleFree (graph F G) := by
  classical
  let c : (i : I) → (G i).Coloring ℕ := fun i => (hG i).some
  let label : (∀ i, A i) → ℕ → ℕ := fun x n => c (s n) (x (s n))
  let code : (∀ i, A i) → ℕ → Fin 2 :=
    fun x k => if label x (Nat.unpair k).1 = (Nat.unpair k).2 then 1 else 0
  apply Erdos595Work.countable_union_of_coloring (graph F G)
  refine SimpleGraph.Coloring.mk code ?_
  intro x y hxy heq
  obtain ⟨n,hn⟩ := (hs.eventually hxy).exists
  have hne : label y n ≠ label x n := fun h => (c (s n)).valid hn h.symm
  have hh := congrFun heq (Nat.pair n (label x n))
  simp [code,Nat.unpair_pair,hne] at hh

/-- Countably generated proper filters cannot amplify countably
vertex-colourable coordinates into a witness. -/
theorem countably_generated_cover (F : Filter I) [F.NeBot] [F.IsCountablyGenerated]
    (G : ∀ i, SimpleGraph (A i))
    (hG : ∀ i, Nonempty ((G i).Coloring ℕ)) :
    Erdos595Work.IsCountableUnionOfTriangleFree (graph F G) := by
  obtain ⟨s,hs⟩ := exists_sampler F
  exact cover_of_sampler F G hG s hs

#print axioms exists_sampler
#print axioms cover_of_sampler
#print axioms countably_generated_cover
end Erdos595SampledProduct
