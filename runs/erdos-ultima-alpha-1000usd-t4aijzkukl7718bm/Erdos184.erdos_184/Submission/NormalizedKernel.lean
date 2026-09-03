import Submission.OrderNormalizationTheory
import Submission.LabelKernelEmbedding
import Submission.ContactKernel

/-! Color-preserving transport from recursively marked kernels to ordinary
cyclic vertex words. All numbers of colors and markers are allowed. -/
open scoped Classical
namespace Erdos184Work.NormalizedKernel
open CycleSegments LabelKernel Erdos184Serial SmallOrderNormalization
set_option maxHeartbeats 1500000
set_option linter.unusedSectionVars false
variable {K W : Type*} [Fintype K] {n : K → ℕ}
    (place : ∀ i, Fin (n i+2) → W) (o : ∀ i, Marked.Order (n i))

noncomputable local instance {m : K → ℕ} : DecidableEq (Σ i, Fin (m i)) := Classical.decEq _

noncomputable def edgeEquiv : (Σ i, Fin (n i+2)) ≃ (Σ i, Fin (n i+2)) :=
  Equiv.sigmaCongrRight fun i => Equiv.ofBijective (normalized (n i) (o i)).edge
    ⟨(normalized_valid_all (n i) (o i)).1,
      Finite.surjective_of_injective (normalized_valid_all (n i) (o i)).1⟩

lemma edgeEquiv_apply (j : Σ i, Fin (n i+2)) :
    edgeEquiv o j = ⟨j.1,(normalized (n j.1) (o j.1)).edge j.2⟩ := rfl

lemma edgeEquiv_fst (j : Σ i, Fin (n i+2)) : (edgeEquiv o j).1 = j.1 := rfl

def word (i : K) (j : Fin (n i+2)) : W :=
  place i ((normalized (n i) (o i)).vertex j)

def src (j : Σ i, Fin (n i+2)) : W := word place o j.1 j.2

def dst (j : Σ i, Fin (n i+2)) : W := word place o j.1 (j.2+1)

noncomputable def embedding : Embedding (src place o) (dst place o)
    (fun j : Σ i, Fin (n i+2) => place j.1 j.2)
    (fun j : Σ i, Fin (n i+2) => place j.1 (Marked.nextFin (n j.1) (o j.1) j.2)) where
  edge := (edgeEquiv o).toEmbedding
  vertex := Function.Embedding.refl W
  endpoints j := by
    change s(place j.1 ((normalized (n j.1) (o j.1)).vertex j.2),
        place j.1 ((normalized (n j.1) (o j.1)).vertex (j.2+(1 : Fin (n j.1+2))))) =
      s(place j.1 ((normalized (n j.1) (o j.1)).edge j.2),
        place j.1 (Marked.nextFin (n j.1) (o j.1) ((normalized (n j.1) (o j.1)).edge j.2)))
    rcases (normalized_valid_all (n j.1) (o j.1)).2.2 j.2 with ⟨hs,ht⟩ | ⟨ht,hs⟩
    · change (normalized (n j.1) (o j.1)).edge j.2 = _ at hs
      rw [ht,hs]
    · change (normalized (n j.1) (o j.1)).edge j.2 = _ at hs
      rw [ht,hs]
      exact Sym2.eq_swap

lemma word_injective (h : ∀ i, Function.Injective (place i)) (i : K) :
    Function.Injective (word place o i) :=
  (h i).comp (normalized_valid_all (n i) (o i)).2.1

lemma word_first (i : K) : word place o i 0 = place i 0 := by
  rw [word,normalized_first_all]

lemma map_univ : (Finset.univ : Finset (Σ i, Fin (n i+2))).map
    (embedding place o).edge = Finset.univ :=
  Finset.map_univ_equiv (edgeEquiv o)

lemma map_colors (A : Finset K) :
    (PathSubstitution.Family.colorLabels (m := fun i => n i+2) A).map (embedding place o).edge =
      PathSubstitution.Family.colorLabels A := by
  ext j
  simp only [Finset.mem_map,PathSubstitution.Family.colorLabels,Finset.mem_filter,
    Finset.mem_univ,true_and]
  constructor
  · rintro ⟨i,hi,hij⟩
    have he := congrArg Sigma.fst hij
    change i.1 = j.1 at he
    rwa [← he]
  · intro hj
    refine ⟨(edgeEquiv o).symm j,?_,(edgeEquiv o).apply_symm_apply j⟩
    have he := edgeEquiv_fst o ((edgeEquiv o).symm j)
    rw [(edgeEquiv o).apply_symm_apply] at he
    rwa [← he]

lemma number_univ_iff (k : ℕ) :
    HasNumber (code (fun j : Σ i, Fin (n i+2) => place j.1 j.2)
      (fun j => place j.1 (Marked.nextFin (n j.1) (o j.1) j.2))) Finset.univ k ↔
    HasNumber (code (src place o) (dst place o)) Finset.univ k := by
  have h := (embedding place o).hasNumber_map_iff Finset.univ k
  rwa [map_univ] at h

lemma minimal_univ_iff (k : ℕ) :
    MinimalCore (code (fun j : Σ i, Fin (n i+2) => place j.1 j.2)
      (fun j => place j.1 (Marked.nextFin (n j.1) (o j.1) j.2))) Finset.univ k ↔
    MinimalCore (code (src place o) (dst place o)) Finset.univ k := by
  have h := (embedding place o).minimalCore_map_iff Finset.univ k
  rwa [map_univ] at h

lemma rigid_univ_iff (k : ℕ) :
    Rigid (code (fun j : Σ i, Fin (n i+2) => place j.1 j.2)
      (fun j => place j.1 (Marked.nextFin (n j.1) (o j.1) j.2))) Finset.univ k ↔
    Rigid (code (src place o) (dst place o)) Finset.univ k := by
  have h := (embedding place o).rigid_map_iff Finset.univ k
  rwa [map_univ] at h

lemma upper_colors_iff (A : Finset K) (k : ℕ) :
    (∀ P, Partition (code (fun j : Σ i, Fin (n i+2) => place j.1 j.2)
      (fun j => place j.1 (Marked.nextFin (n j.1) (o j.1) j.2)))
      (PathSubstitution.Family.colorLabels A) P → P.card ≤ k) ↔
    (∀ P, Partition (code (src place o) (dst place o))
      (PathSubstitution.Family.colorLabels A) P → P.card ≤ k) := by
  have h := (embedding place o).upper_bound_map_iff
    (PathSubstitution.Family.colorLabels A) k
  rwa [map_colors] at h

lemma exists_colors_iff (A : Finset K) (k : ℕ) :
    (∃ P, Partition (code (fun j : Σ i, Fin (n i+2) => place j.1 j.2)
      (fun j => place j.1 (Marked.nextFin (n j.1) (o j.1) j.2)))
      (PathSubstitution.Family.colorLabels A) P ∧ P.card ≤ k) ↔
    (∃ P, Partition (code (src place o) (dst place o))
      (PathSubstitution.Family.colorLabels A) P ∧ P.card ≤ k) := by
  constructor
  · rintro ⟨P,hP,hc⟩
    rw [← map_colors place o A] at hP
    obtain ⟨Q,hQ,hcq⟩ := unmap_partition_exists (embedding place o).edge
      (embedding place o).valid_map hP
    exact ⟨Q,hQ,hcq.trans_le hc⟩
  · rintro ⟨P,hP,hc⟩
    obtain ⟨Q,hQ,hcq⟩ := map_partition_exists (embedding place o).edge
      (embedding place o).valid_map hP
    rw [map_colors] at hQ
    exact ⟨Q,hQ,hcq.trans_le hc⟩

#print axioms minimal_univ_iff
#print axioms exists_colors_iff
end Erdos184Work.NormalizedKernel
