import Submission.PrimeWinnerCongruenceRuns
import Submission.PrimeLoserPrimeWeightedCollisions

/-!
A finite obstruction to bounding EACH actual loser group by its own diagonal.
This does not refute a global energy bound: cancellation or compensation
between different prime groups remains possible. It is not a disproof of
the natural-density conjecture.
-/
namespace Erdos371
open Finset
set_option autoImplicit false

private def edges5039 : Finset ℕ :=
  ((Icc 1 9).image (fun k => k*5039-1)) ∪
    ((Icc 1 9).image (fun k => k*5039))

private lemma maxPrimeFac5039_index (m : ℕ) (hm : m ≤ 45352)
    (hp : Nat.maxPrimeFac m=5039) :
    ∃ k ∈ Icc 1 9, m=k*5039 := by
  have hd : 5039 ∣ m := hp ▸ Nat.maxPrimeFac_dvd
  have hlow : 5039 ≤ m := hp ▸ Nat.maxPrimeFac_le
  obtain ⟨k,he⟩ := hd
  refine ⟨k,mem_Icc.mpr ⟨by omega,by omega⟩,by omega⟩

private lemma primeLoser5039_incidence_subset :
    primeLoserIncidences 5039 45352 ⊆ edges5039 := by
  intro n hn
  obtain ⟨hnN,hp⟩ := mem_filter.mp hn
  have hnN' := mem_range.mp hnN
  have hcase : Nat.maxPrimeFac n=5039 ∨ Nat.maxPrimeFac (n+1)=5039 := by
    unfold primeLoser at hp
    rcases min_cases (Nat.maxPrimeFac n) (Nat.maxPrimeFac (n+1)) with h | h
    · exact Or.inl (h.1.symm.trans hp)
    · exact Or.inr (h.1.symm.trans hp)
  rcases hcase with h | h
  · obtain ⟨k,hk,he⟩ := maxPrimeFac5039_index n (by omega) h
    exact mem_union_right _ (mem_image.mpr ⟨k,hk,he.symm⟩)
  · obtain ⟨k,hk,he⟩ := maxPrimeFac5039_index (n+1) (by omega) h
    exact mem_union_left _ (mem_image.mpr ⟨k,hk,by omega⟩)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- There are exactly seven incidences in this actual prime group. The
finite calculation is reduced to the eighteen edges adjoining its multiples. -/
lemma primeLoser5039_incidence_set :
    primeLoserIncidences 5039 45352 =
      {10078,15117,20156,25195,30234,35273,45351} := by
  have hbound : ∀ n ∈ edges5039, n < 45352 := by decide +kernel
  have he : primeLoserIncidences 5039 45352 =
      edges5039.filter (fun n => primeLoser n=5039) := by
    ext n
    simp only [primeLoserIncidences,mem_filter,mem_range]
    constructor
    · intro h
      exact ⟨primeLoser5039_incidence_subset (mem_filter.mpr ⟨mem_range.mpr h.1,h.2⟩),h.2⟩
    · intro h
      exact ⟨hbound n h.1,h.2⟩
  rw [he]
  decide +kernel

lemma primeLoser5039_incidence_card : (primeLoserIncidences 5039 45352).card=7 := by
  rw [primeLoser5039_incidence_set]
  decide +kernel

lemma primeLoserSum_5039_45352 : primeLoserSum 5039 45352=7 := by
  have h := primeWinnerSum_sub_primeLoserSum 5039 45352
  have hp : Nat.maxPrimeFac 45352 ≠ 5039 := by decide +kernel
  rw [primeWinnerSum_5039_45352,if_neg hp,Nat.maxPrimeFac_zero,
    if_neg (by omega : ¬ (0 : ℕ)=5039)] at h
  linarith

/-- A natural-order, single-group variance bound by the incidence count is
false. The prime-weighted version fails by exactly the same factor. -/
theorem actual_loser_group_exceeds_diagonal :
    ((primeLoserIncidences 5039 45352).card : ℝ) <
      (primeLoserSum 5039 45352)^2 := by
  rw [primeLoser5039_incidence_card,primeLoserSum_5039_45352]
  norm_num

theorem not_loser_group_square_le_incidence :
    ¬ ∀ p N : ℕ, (primeLoserSum p N)^2 ≤ (primeLoserIncidences p N).card := by
  intro h
  exact (not_le_of_gt actual_loser_group_exceeds_diagonal) (h 5039 45352)

#print axioms primeLoser5039_incidence_set
#print axioms primeLoserSum_5039_45352
#print axioms not_loser_group_square_le_incidence
end Erdos371
