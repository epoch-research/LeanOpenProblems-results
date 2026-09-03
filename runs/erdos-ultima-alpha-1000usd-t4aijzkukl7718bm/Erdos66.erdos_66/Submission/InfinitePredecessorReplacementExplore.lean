import Submission.PredecessorCellExplore

/-! Simultaneous replacement in arbitrarily many distinct original
predecessor cells preserves all prefix counts within one. This theorem is
about compatibility of moves, not existence of suitable packet choices. -/
namespace Erdos66InfinitePredecessorReplacement
open AdditiveCombinatorics Erdos66Counting Erdos66PredecessorCell
  Erdos66OrderedPartialReplacement
open scoped Classical
set_option maxHeartbeats 1800000

noncomputable def replacement (A F : Set ℕ) : Set ℕ :=
  (A \ (predecessor A '' F)) ∪ F

lemma active_finite (A F : Set ℕ) (hinj : Set.InjOn (predecessor A) F) (N : ℕ) :
    {u | u ∈ F ∧ predecessor A u < N}.Finite := by
  apply Set.Finite.of_injOn (f := predecessor A) (t := Set.Iio N)
  · intro u hu
    exact hu.2
  · intro u hu v hv he
    exact hinj hu.1 hv.1 he
  · exact Set.finite_Iio N

lemma finite_replacement_agrees (A F : Set ℕ) (hinj : Set.InjOn (predecessor A) F) (N : ℕ) :
    ∃ C : Finset ℕ, (C : Set ℕ) ⊆ F ∧
      (∀ u ∈ C, predecessor A u < N) ∧
      ∀ i < N, i ∈ replacement A F ↔ i ∈ swap A (C.image (predecessor A)) C := by
  let hfin := active_finite A F hinj N
  let C := hfin.toFinset
  have hC (u : ℕ) : u ∈ C ↔ u ∈ F ∧ predecessor A u < N := hfin.mem_toFinset
  have hsub : (C : Set ℕ) ⊆ F := fun u hu ↦ (hC u).mp hu |>.1
  refine ⟨C, hsub, fun u hu ↦ (hC u).mp hu |>.2, ?_⟩
  intro i hi
  have hins : i ∈ C ↔ i ∈ F := by
    rw [hC]
    have hh := predecessor_le A i
    constructor
    · exact And.left
    · intro h
      exact ⟨h, by omega⟩
  have hdel : i ∈ predecessor A '' F ↔ i ∈ C.image (predecessor A) := by
    constructor
    · rintro ⟨u, hu, he⟩
      exact Finset.mem_image.mpr ⟨u, (hC u).mpr ⟨hu, by omega⟩, he⟩
    · intro h
      obtain ⟨u, hu, he⟩ := Finset.mem_image.mp h
      exact ⟨u, hsub hu, he⟩
  simp only [replacement, swap, Set.mem_union, Set.mem_diff, Finset.mem_coe, hdel, hins]

lemma count_eq_of_agree (A B : Set ℕ) (N : ℕ) (h : ∀ i < N, i ∈ A ↔ i ∈ B) :
    count A N = count B N := by
  unfold count
  congr 1
  ext i
  rw [mem_cutoff, mem_cutoff]
  by_cases hi : i < N
  · simp only [hi, true_and, h i hi]
  · simp only [hi, false_and]

lemma sumRep_eq_of_agree (A B : Set ℕ) (n : ℕ)
    (h : ∀ i ≤ n, i ∈ A ↔ i ∈ B) : sumRep A n = sumRep B n := by
  rw [sumRep_def, sumRep_def]
  congr 1
  apply Finset.filter_congr
  intro p hp
  have hp' := Finset.mem_antidiagonal.mp hp
  have h1 := h p.1 (by omega)
  have h2 := h p.2 (by omega)
  simp only [h1, h2]

/-- This uses injectivity across the whole infinite inserted set, not merely
inside each packet. It therefore does not accumulate one unit per packet. -/
theorem infinite_replacement_prefix (A F : Set ℕ)
    (hmem : ∀ u ∈ F, predecessor A u ∈ A) (hnew : Disjoint F A)
    (hinj : Set.InjOn (predecessor A) F) (N : ℕ) :
    -1 ≤ (count (replacement A F) N : ℝ)-count A N ∧
      (count (replacement A F) N : ℝ)-count A N ≤ 0 := by
  obtain ⟨C,hCF,hCN,he⟩ := finite_replacement_agrees A F hinj N
  have hc := count_eq_of_agree (replacement A F) (swap A (C.image (predecessor A)) C) N he
  rw [hc]
  exact predecessor_swap_prefix A C (fun u hu ↦ hmem u (hCF hu))
    (fun u hu hA ↦ Set.disjoint_left.mp hnew (hCF hu) hA)
    (fun u hu v hv he ↦ hinj (hCF hu) (hCF hv) he) N

lemma infinite_replacement_discrepancy (A F : Set ℕ)
    (hmem : ∀ u ∈ F, predecessor A u ∈ A) (hnew : Disjoint F A)
    (hinj : Set.InjOn (predecessor A) F) (g : ℕ → ℝ) (D : ℝ)
    (hA : ∀ N, |(count A N : ℝ)-g N| ≤ D) :
    ∀ N, |(count (replacement A F) N : ℝ)-g N| ≤ D+1 := by
  intro N
  obtain ⟨hl,hu⟩ := infinite_replacement_prefix A F hmem hnew hinj N
  have hh := hA N
  rw [abs_le] at hh ⊢
  constructor <;> linarith

lemma finite_replacement_representation (A F : Set ℕ)
    (hinj : Set.InjOn (predecessor A) F) (n : ℕ) :
    ∃ C : Finset ℕ, (C : Set ℕ) ⊆ F ∧
      (∀ u ∈ C, predecessor A u ≤ n) ∧
      sumRep (replacement A F) n = sumRep (swap A (C.image (predecessor A)) C) n := by
  obtain ⟨C,hCF,hCN,he⟩ := finite_replacement_agrees A F hinj (n+1)
  exact ⟨C,hCF,fun u hu ↦ by have := hCN u hu; omega,
    sumRep_eq_of_agree _ _ n (fun i hi ↦ he i (by omega))⟩

end Erdos66InfinitePredecessorReplacement
