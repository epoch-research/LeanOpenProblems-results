import Submission.Compactness

/-! Elementary lower-density transfer through inclusion and finite trimming. -/
namespace Erdos1206.PositiveDensityTransfer
open Finset
open scoped Classical

lemma prefix_card (A : Set ℕ) (N : ℕ) :
    ((range N).filter (fun n => n ∈ A)).card=(A ∩ Set.Iio N).ncard := by
  have he : A ∩ Set.Iio N=(((range N).filter (fun n => n ∈ A)) : Set ℕ) := by
    ext n
    simp only [Set.mem_inter_iff,Set.mem_Iio,mem_coe,mem_filter,mem_range]
    tauto
  rw [he,Set.ncard_coe_finset]

lemma superset {A B : Set ℕ} (hA : 0 < A.lowerDensity) (hAB : A ⊆ B) :
    0 < B.lowerDensity := by
  obtain ⟨δ,hδ,C,hpre⟩ := prefix_bound_of_positive_lowerDensity hA
  apply positive_lowerDensity_of_prefix_bound hδ (C := C)
  intro N
  have hh := hpre N
  have hc : (A ∩ Set.Iio N).ncard ≤ (B ∩ Set.Iio N).ncard :=
    Set.ncard_le_ncard (Set.inter_subset_inter_left _ hAB) (Set.finite_Iio N |>.subset Set.inter_subset_right)
  have hcR : ((A ∩ Set.Iio N).ncard:ℝ) ≤ (B ∩ Set.Iio N).ncard := by exact_mod_cast hc
  linarith

lemma trim {A : Set ℕ} (hA : 0 < A.lowerDensity) (M : ℕ) :
    0 < (A ∩ Set.Ici M).lowerDensity := by
  obtain ⟨δ,hδ,C,hpre⟩ := prefix_bound_of_positive_lowerDensity hA
  apply positive_lowerDensity_of_prefix_bound hδ (C := C+M)
  intro N
  let U := (range N).filter (fun n => n ∈ A)
  let V := (range N).filter (fun n => n ∈ A ∩ Set.Ici M)
  have hsub : U ⊆ V ∪ range M := by
    intro n hn
    by_cases hm : M ≤ n
    · exact mem_union_left _ (mem_filter.mpr ⟨(mem_filter.mp hn).1,(mem_filter.mp hn).2,hm⟩)
    · exact mem_union_right _ (mem_range.mpr (lt_of_not_ge hm))
  have hc := (card_le_card hsub).trans (card_union_le V (range M))
  have hu : U.card=(A ∩ Set.Iio N).ncard := prefix_card A N
  have hv : V.card=((A ∩ Set.Ici M) ∩ Set.Iio N).ncard := by simpa [V] using prefix_card (A ∩ Set.Ici M) N
  rw [hu,hv,card_range] at hc
  have hcR : ((A ∩ Set.Iio N).ncard:ℝ) ≤ ((A ∩ Set.Ici M) ∩ Set.Iio N).ncard+M := by exact_mod_cast hc
  linarith [hpre N]

#print axioms superset
#print axioms trim
end Erdos1206.PositiveDensityTransfer
