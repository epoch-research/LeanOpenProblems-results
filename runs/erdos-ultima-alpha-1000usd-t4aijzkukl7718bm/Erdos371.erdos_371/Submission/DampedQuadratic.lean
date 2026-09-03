import Submission.DampedCoefficients
import Submission.ShortPrimePairCancellation

/-! Exact bookkeeping for the quadratic damping coefficient. -/
namespace Erdos371
open Finset

lemma ordered_pair_count (P : Finset ℕ) :
    (∑ p ∈ P, ∑ q ∈ P, if p < q then (1 : ℝ) else 0) = P.card.choose 2 := by
  have hh := powersetCard_two_min_sum (fun _ => (1 : ℝ)) P
  have hs : (∑ E ∈ P.powersetCard 2, subsetMinTerm (fun _ => (1 : ℝ)) E) = P.card.choose 2 := by
    have he (E : Finset ℕ) (hE : E ∈ P.powersetCard 2) :
        subsetMinTerm (fun _ => (1 : ℝ)) E = 1 := by
      have hc := (mem_powersetCard.mp hE).2
      have hEn : E.Nonempty := card_pos.mp (by omega)
      simp [subsetMinTerm,hEn,hc]
    rw [sum_congr rfl he,sum_const,nsmul_eq_mul,mul_one,card_powersetCard]
  rw [hs,sum_filter,sum_product] at hh
  exact hh.symm

lemma dampedCoefficient_two_union (P Q : Finset ℕ) (hd : Disjoint P Q) :
    dampedCoefficient 2 (fun p => if p ∈ Q then 1 else -1) (P ∪ Q) =
      (P.card.choose 2 : ℝ)-Q.card.choose 2+
        ∑ p ∈ P, ∑ q ∈ Q, if p < q then (1 : ℝ) else -1 := by
  rw [dampedCoefficient_two,sum_filter,sum_product,sum_union hd]
  simp_rw [sum_union hd,sum_add_distrib]
  have hnot (p : ℕ) (hp : p ∈ P) : p ∉ Q := fun hq => disjoint_left.mp hd hp hq
  have hPP : (∑ p ∈ P, ∑ q ∈ P, if p < q then (if p ∈ Q then (1 : ℝ) else -1) else 0) =
      -(P.card.choose 2 : ℝ) := by
    rw [← ordered_pair_count,← sum_neg_distrib]
    apply sum_congr rfl
    intro p hp
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro q hq
    simp only [if_neg (hnot p hp)]
    split_ifs <;> norm_num
  have hQQ : (∑ p ∈ Q, ∑ q ∈ Q, if p < q then (if p ∈ Q then (1 : ℝ) else -1) else 0) =
      (Q.card.choose 2 : ℝ) := by
    rw [← ordered_pair_count]
    apply sum_congr rfl
    intro p hp
    simp only [if_pos hp]
  have hcross :
      (∑ p ∈ P, ∑ q ∈ Q, if p < q then (if p ∈ Q then (1 : ℝ) else -1) else 0)+
      (∑ q ∈ Q, ∑ p ∈ P, if q < p then (if q ∈ Q then (1 : ℝ) else -1) else 0) =
      -∑ p ∈ P, ∑ q ∈ Q, if p < q then (1 : ℝ) else -1 := by
    rw [sum_comm (s := Q) (t := P),← sum_add_distrib,← sum_neg_distrib]
    apply sum_congr rfl
    intro p hp
    rw [← sum_add_distrib,← sum_neg_distrib]
    apply sum_congr rfl
    intro q hq
    have hpq : p ≠ q := by intro he; exact hnot p hp (he ▸ hq)
    simp only [if_neg (hnot p hp),if_pos hq]
    rcases lt_or_gt_of_ne hpq with h | h
    · simp [h,not_lt.mpr h.le]
    · simp [h,not_lt.mpr h.le]
  rw [hPP,hQQ]
  linarith

noncomputable def crossPrimeSkew (n : ℕ) : ℝ :=
  ∑ p ∈ n.primeFactors, ∑ q ∈ (n+1).primeFactors, if p < q then 1 else -1

lemma dampedFactorSign_quadratic_coefficient (n : ℕ) (hn : 0 < n) :
    dampedCoefficient 2 (fun p => if p ∣ n+1 then 1 else -1) (n*(n+1)).primeFactors =
      (n.primeFactors.card.choose 2 : ℝ)-(n+1).primeFactors.card.choose 2+crossPrimeSkew n := by
  have hd : Disjoint n.primeFactors (n+1).primeFactors := by
    apply disjoint_left.mpr
    intro p hp hq
    exact (Nat.prime_of_mem_primeFactors hp).not_dvd_one
      ((Nat.dvd_add_iff_right (Nat.dvd_of_mem_primeFactors hp)).mpr
        (Nat.dvd_of_mem_primeFactors hq))
  have he : dampedCoefficient 2 (fun p => if p ∣ n+1 then 1 else -1) (n*(n+1)).primeFactors =
      dampedCoefficient 2 (fun p => if p ∈ (n+1).primeFactors then 1 else -1)
        (n.primeFactors ∪ (n+1).primeFactors) := by
    rw [Nat.primeFactors_mul (by omega) (by omega)]
    unfold dampedCoefficient
    congr 1
    apply sum_congr rfl
    intro E hE
    have hEP := (mem_powersetCard.mp hE).1
    have hEne : E.Nonempty := card_pos.mp (by have := (mem_powersetCard.mp hE).2; omega)
    have hp : (E.min' hEne).Prime := by
      rcases mem_union.mp (hEP (E.min'_mem hEne)) with h | h <;>
        exact Nat.prime_of_mem_primeFactors h
    have hiff : E.min' hEne ∈ (n+1).primeFactors ↔ E.min' hEne ∣ n+1 := by
      simp [Nat.mem_primeFactors,hp]
    simp only [subsetMinTerm,dif_pos hEne,hiff]
  rw [he,dampedCoefficient_two_union _ _ hd]
  rfl

#print axioms dampedFactorSign_quadratic_coefficient
end Erdos371
