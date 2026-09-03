import Submission.PrimeLoserCollisions

/-! Bounding prime-winner energy by the exact second moment of prime-loser
incidences. The off-diagonal count still requires an arithmetic estimate. -/
namespace Erdos371
open Finset

lemma sum_card_sq_fibers_le_same_pairs {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (s : Finset ι) (t : Finset κ) (f : ι → κ) :
    (∑ p ∈ t, ((s.filter fun n => f n=p).card)^2) ≤
      ((s ×ˢ s).filter fun nm => f nm.1=f nm.2).card := by
  let U := (s ×ˢ s).filter fun nm => f nm.1=f nm.2
  have hrow (p : κ) : ((s.filter fun n => f n=p).card)^2 =
      (U.filter fun nm => f nm.1=p).card := by
    rw [pow_two, ← card_product]
    congr 1
    ext nm
    simp only [U,mem_product,mem_filter]
    aesop
  simp_rw [hrow]
  rw [sum_card_fiberwise_eq_card_filter]
  exact card_filter_le _ _

lemma card_same_pairs_eq_diagonal_add_offDiag {ι κ : Type*} [DecidableEq ι]
    [DecidableEq κ] (s : Finset ι) (f : ι → κ) :
    ((s ×ˢ s).filter fun nm => f nm.1=f nm.2).card =
      s.card + (s.offDiag.filter fun nm => f nm.1=f nm.2).card := by
  rw [← diag_union_offDiag,filter_union,
    card_union_of_disjoint (disjoint_filter_filter (disjoint_diag_offDiag s))]
  congr 1
  rw [filter_true_of_mem (fun nm hnm => congrArg f (mem_diag.mp hnm).2),diag_card]

lemma primeLoserIncidences_eq_high_filter (B N p : ℕ) (hp : B < p) :
    primeLoserIncidences p N = (bothAboveSet B N).filter fun n => primeLoser n=p := by
  ext n
  simp only [primeLoserIncidences,bothAboveSet,mem_filter]
  constructor
  · rintro ⟨hn,he⟩
    refine ⟨⟨hn,?_⟩,he⟩
    have hh : B < primeLoser n := he.symm ▸ hp
    exact lt_min_iff.mp hh
  · rintro ⟨⟨hn,_⟩,he⟩
    exact ⟨hn,he⟩

/-- The exact diagonal count plus the ordered off-diagonal incidence count
bounds the sum of squared incidence degrees. -/
lemma sum_primeLoserIncidences_sq_le (B N : ℕ) :
    (∑ p ∈ (primeWinnerLabels N).filter (B < ·), (primeLoserIncidences p N).card^2) ≤
      (bothAboveSet B N).card + (primeLoserCollisions B N).card := by
  have he : (∑ p ∈ (primeWinnerLabels N).filter (B < ·), (primeLoserIncidences p N).card^2) =
      ∑ p ∈ (primeWinnerLabels N).filter (B < ·),
        (((bothAboveSet B N).filter fun n => primeLoser n=p).card)^2 := by
    apply sum_congr rfl
    intro p hp
    rw [primeLoserIncidences_eq_high_filter B N p (mem_filter.mp hp).2]
  rw [he]
  exact (sum_card_sq_fibers_le_same_pairs (bothAboveSet B N)
    ((primeWinnerLabels N).filter (B < ·)) primeLoser).trans_eq
      (card_same_pairs_eq_diagonal_add_offDiag (bothAboveSet B N) primeLoser)

/-- This replaces a maximum-degree bound by a count of actual pairs of
incidences. The factor two accommodates the single endpoint correction. -/
theorem primeWinnerEnergyAbove_le_collisions (B N : ℕ) :
    primeWinnerEnergyAbove B N ≤
      2*((bothAboveSet B N).card : ℝ) + 2*(primeLoserCollisions B N).card + 2 := by
  let S := (primeWinnerLabels N).filter (B < ·)
  have hpoint (p : ℕ) (hp : p ∈ S) :
      (primeWinnerSum p N)^2 ≤ 2*((primeLoserIncidences p N).card : ℝ)^2+
        2*(if Nat.maxPrimeFac N=p then 1 else 0) := by
    have hh := primeWinnerSum_norm_le_loser_count p N
      (by have := (mem_filter.mp hp).2; omega)
    change ‖primeWinnerSum p N‖ ≤ (primeLoserIncidences p N).card + _ at hh
    have hh0 := norm_nonneg (primeWinnerSum p N)
    have hc0 : (0 : ℝ) ≤ (primeLoserIncidences p N).card := Nat.cast_nonneg _
    have heq : ‖primeWinnerSum p N‖^2=(primeWinnerSum p N)^2 := by
      rw [Real.norm_eq_abs,sq_abs]
    split_ifs at hh ⊢ <;> nlinarith [sq_nonneg ((primeLoserIncidences p N).card - (1 : ℝ))]
  have hsum := sum_le_sum hpoint
  rw [sum_add_distrib,← mul_sum,← mul_sum] at hsum
  have hend : (∑ p ∈ S, if Nat.maxPrimeFac N=p then (1 : ℝ) else 0) ≤ 1 := by
    rw [sum_ite_eq]
    split_ifs <;> norm_num
  have hinc : (∑ p ∈ S, ((primeLoserIncidences p N).card : ℝ)^2) ≤
      (bothAboveSet B N).card + (primeLoserCollisions B N).card := by
    exact_mod_cast sum_primeLoserIncidences_sq_le B N
  change primeWinnerEnergyAbove B N ≤ _ at hsum
  linarith

#print axioms sum_primeLoserIncidences_sq_le
#print axioms primeWinnerEnergyAbove_le_collisions
end Erdos371
