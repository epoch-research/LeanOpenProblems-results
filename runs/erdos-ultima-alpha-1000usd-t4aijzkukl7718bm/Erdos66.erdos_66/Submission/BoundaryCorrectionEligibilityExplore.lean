import Submission.BoundarySparsePowerProfileExplore
import Submission.CentralTripleDeletionExplore

/-! Small boundary counts guarantee enough upper-half central endpoints for
an exact finite downward clipping. This is not a lower-envelope theorem. -/
namespace Erdos66BoundaryCorrectionEligibility
open AdditiveCombinatorics Erdos66BoundaryPairMean Erdos66BoundaryPairCounts
  Erdos66CentralTripleDeletion Erdos66NatPairAlgebra
open scoped Classical
set_option maxHeartbeats 1800000

lemma mem_upperEndpoints {A : Set ℕ} {N n a : ℕ} : a∈upperEndpoints A N n ↔
    a ≤ n ∧ N ≤ a ∧ N ≤ n-a ∧ a∈A ∧ n-a∈A ∧ n<2*a := by
  simp only [upperEndpoints,Finset.mem_filter,mem_endpoints]
  tauto

lemma sumRep_le_one_of_diagonal (B : Set ℕ) (n : ℕ)
    (h : ∀ a b, a+b=n → a∈B → b∈B → a=b) : sumRep B n ≤ 1 := by
  rw [sumRep_def]
  apply Finset.card_le_one.mpr
  intro p hp q hq
  obtain ⟨hp,hp1,hp2⟩ := Finset.mem_filter.mp hp
  obtain ⟨hq,hq1,hq2⟩ := Finset.mem_filter.mp hq
  have hp' := Finset.mem_antidiagonal.mp hp
  have hq' := Finset.mem_antidiagonal.mp hq
  have h1 := h p.1 p.2 hp' hp1 hp2
  have h2 := h q.1 q.2 hq' hq1 hq2
  exact Prod.ext (by omega) (by omega)

lemma remaining_at_most_one (A : Set ℕ) (n : ℕ) :
    sumRep (A\(upperEndpoints A 0 n : Set ℕ)) n ≤ 1 := by
  apply sumRep_le_one_of_diagonal
  intro a b he h1 h2
  have h1' : ¬n<2*a := by
    intro hlt
    apply h1.2
    exact mem_upperEndpoints.mpr ⟨by omega,by omega,by omega,h1.1,by
      simpa only [show n-a=b by omega] using h2.1,hlt⟩
  have h2' : ¬n<2*b := by
    intro hlt
    apply h2.2
    exact mem_upperEndpoints.mpr ⟨by omega,by omega,by omega,h2.1,by
      simpa only [show n-b=a by omega] using h1.1,hlt⟩
  omega

lemma upper_count_bounds_rep (A : Set ℕ) (n : ℕ) :
    sumRep A n ≤ 2*(upperEndpoints A 0 n).card+1 := by
  have he := upper_target_exact A (upperEndpoints A 0 n) 0 n (Finset.Subset.refl _)
  have hh := remaining_at_most_one A n
  omega

lemma split_upper_endpoints (A : Set ℕ) (d n : ℕ) (hd : 2 ≤ d) :
    upperEndpoints A 0 n ⊆ upperEndpoints A (n/d^2) n ∪ (boundary A d n).image (fun a ↦ n-a) := by
  intro a ha
  obtain ⟨han,_,_,haA,hbA,hlt⟩ := mem_upperEndpoints.mp ha
  have hh := quotient_half d n hd
  by_cases hb : n/d^2 ≤ n-a
  · exact Finset.mem_union_left _ (mem_upperEndpoints.mpr ⟨han,by omega,hb,haA,hbA,hlt⟩)
  · apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨n-a,Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by omega),hbA,by rwa [Nat.sub_sub_self han]⟩,Nat.sub_sub_self han⟩

lemma central_capacity (A : Set ℕ) (d n : ℕ) (hd : 2 ≤ d) :
    sumRep A n ≤ 2*(upperEndpoints A (n/d^2) n).card+2*(boundary A d n).card+1 := by
  have hs := (Finset.card_le_card (split_upper_endpoints A d n hd)).trans (Finset.card_union_le _ _)
  have hi := Finset.card_image_le (s := boundary A d n) (f := fun a ↦ n-a)
  have hh := upper_count_bounds_rep A n
  omega

 theorem exists_central_clipping (A : Set ℕ) (d n q : ℕ) (hd : 2 ≤ d)
    (hq : 2*(boundary A d n).card+2 ≤ q) :
    ∃ D : Finset ℕ, D ⊆ upperEndpoints A (n/d^2) n ∧
      sumRep (A\(D : Set ℕ)) n ≤ q ∧
      min (sumRep A n) (q-1) ≤ sumRep (A\(D : Set ℕ)) n := by
  by_cases hr : sumRep A n ≤ q
  · refine ⟨∅,Finset.empty_subset _,?_,?_⟩
    · simpa using hr
    · simpa using (min_le_left (sumRep A n) (q-1))
  let k := (sumRep A n-q+1)/2
  have hcap := central_capacity A d n hd
  have hk : k ≤ (upperEndpoints A (n/d^2) n).card := by dsimp only [k]; omega
  obtain ⟨D,hD,hcard,hexact,hloss⟩ := exists_exact_downward_correction A (n/d^2) n k hk
  refine ⟨D,hD,?_,?_⟩ <;> dsimp only [k] at hexact <;> omega

end Erdos66BoundaryCorrectionEligibility
