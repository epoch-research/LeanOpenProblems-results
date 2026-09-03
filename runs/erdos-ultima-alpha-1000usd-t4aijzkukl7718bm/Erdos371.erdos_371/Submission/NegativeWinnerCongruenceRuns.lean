import Submission.PrimeWinnerCongruenceRuns

/-! Negative prime-winner contributions from a congruence run. These are
finite arithmetic identities and counterexamples to auxiliary positivity
bounds, not a disproof of the natural-density conjecture. -/
namespace Erdos371
open Finset

lemma maxPrimeFac_mul_add_one_lt_of_pred_dvd (p k : ℕ)
    (hk : 0 < k) (hkp : k+1 < p) (hd : k+1 ∣ p-1) :
    Nat.maxPrimeFac (k*p+1) < p := by
  have hp : 1 < p := by omega
  have he : k*p+1 = k*(p-1)+(k+1) := by
    have h := Nat.sub_add_cancel (show 1 ≤ p by omega)
    nlinarith
  have hdiv : k+1 ∣ k*p+1 := by
    rw [he]
    exact Nat.dvd_add (dvd_mul_of_dvd_right hd k) (dvd_refl (k+1))
  have hq : 0 < (k*p+1)/(k+1) := Nat.div_pos
    (Nat.le_of_dvd (by omega) hdiv) (by omega)
  have hlt : (k*p+1)/(k+1) < p :=
    (Nat.div_lt_iff_lt_mul (by omega : 0 < k+1)).mpr (by nlinarith)
  rw [← Nat.mul_div_cancel' hdiv, Nat.maxPrimeFac_mul (by omega) hq.ne']
  exact max_lt (Nat.maxPrimeFac_le.trans_lt hkp) (Nat.maxPrimeFac_le.trans_lt hlt)

def negativeRunQuotient (p k : ℕ) : ℕ := p+(p-1)/(k-1)

lemma negativeRunQuotient_factorization (p k : ℕ) (hp : 0 < p)
    (hk : 2 ≤ k) (hd : k-1 ∣ p-1) :
    (k-1)*negativeRunQuotient p k = k*p-1 := by
  have h := Nat.mul_div_cancel' hd
  dsimp [negativeRunQuotient]
  rw [Nat.mul_add,h]
  have hk' := Nat.sub_add_cancel (show 1 ≤ k by omega)
  have hp' := Nat.sub_add_cancel hp
  have hkp : 0 < k*p := mul_pos (by omega) hp
  have he := Nat.sub_add_cancel hkp
  nlinarith

lemma negativeRunQuotient_bounds (p k : ℕ) (hk : 2 ≤ k) (hkp : k ≤ p) :
    p < negativeRunQuotient p k ∧ negativeRunQuotient p k ≤ 2*p := by
  have hq : 0 < (p-1)/(k-1) := Nat.div_pos (by omega) (by omega)
  have hle := Nat.div_le_self (p-1) (k-1)
  dsimp [negativeRunQuotient]
  omega

lemma maxPrimeFac_mul_sub_one_gt_iff_negativeRunQuotient_prime (p k : ℕ)
    (hk : 2 ≤ k) (hkp : k < p) (hd : k-1 ∣ p-1) :
    p < Nat.maxPrimeFac (k*p-1) ↔ (negativeRunQuotient p k).Prime := by
  obtain ⟨hl,hu⟩ := negativeRunQuotient_bounds p k hk hkp.le
  have he := negativeRunQuotient_factorization p k (by omega) hk hd
  have hq : negativeRunQuotient p k ≠ 0 := by omega
  rw [← he,Nat.maxPrimeFac_mul (by omega) hq]
  constructor
  · intro h
    by_contra hn
    have hbound : Nat.maxPrimeFac (negativeRunQuotient p k) ≤ p := by
      obtain hb | hb := maxPrimeFac_le_half_of_not_prime _ hn
      · omega
      · exact Nat.maxPrimeFac_le.trans (by omega)
    have hm : Nat.maxPrimeFac (k-1) ≤ p := Nat.maxPrimeFac_le.trans (by omega)
    exact (not_lt_of_ge (max_le hm hbound)) h
  · intro hprime
    rw [hprime.maxPrimeFac_eq_self]
    exact hl.trans_le (le_max_right _ _)

/-- Both incident edges give zero or minus one in total. The negative
contribution occurs precisely at the displayed prime quotient. -/
theorem negative_congruence_run_pair_contribution (p k : ℕ)
    (hp : p.Prime) (hk : 2 ≤ k) (hkp : k+1 < p)
    (hd₁ : k+1 ∣ p-1) (hd₂ : k-1 ∣ p-1) :
    primeWinnerContribution p (k*p-1)+primeWinnerContribution p (k*p) =
      if (negativeRunQuotient p k).Prime then -1 else 0 := by
  have hm := maxPrimeFac_mul_small_cofactor p k hp (by omega) (by omega)
  have hright := maxPrimeFac_mul_add_one_lt_of_pred_dvd p k (by omega) hkp hd₁
  have hleft := maxPrimeFac_mul_sub_one_gt_iff_negativeRunQuotient_prime p k hk
    (by omega) hd₂
  have he : k*p-1+1 = k*p := Nat.sub_add_cancel (by nlinarith [hp.two_le])
  have hne : Nat.maxPrimeFac (k*p-1) ≠ p := by
    intro h
    have hh := consecutive_maxPrimeFac_ne (k*p-1)
    rw [he,hm,h] at hh
    exact hh rfl
  have hright' : primeWinnerContribution p (k*p) = -1 := by
    simp [primeWinnerContribution,primeWinner,factorSign,predicateSign,hm,
      max_eq_left hright.le,hright.not_gt]
  rw [hright']
  by_cases hq : (negativeRunQuotient p k).Prime
  · have h := hleft.mpr hq
    have hnp : primeWinner (k*p-1) ≠ p := by
      simp only [primeWinner,he,hm,max_eq_left h.le]
      omega
    simp [primeWinnerContribution,hnp,hq]
  · have h : Nat.maxPrimeFac (k*p-1) < p :=
      lt_of_le_of_ne (not_lt.mp (hleft.not.mpr hq)) hne
    simp [primeWinnerContribution,primeWinner,factorSign,predicateSign,he,hm,
      max_eq_right h.le,h,hq]

/-- An entire initial group can consist of nonpositive paired contributions.
The formula retains the primality test and makes no prime-values conjecture. -/
theorem primeWinnerSum_negative_congruence_run (p K : ℕ) (hp : p.Prime)
    (hK : 1 ≤ K) (hKp : K+1 < p)
    (hdiv : ∀ j : ℕ, 1 ≤ j → j ≤ K+1 → j ∣ p-1) :
    primeWinnerSum p (K*p+1) =
      -(((Icc 2 K).filter fun k => (negativeRunQuotient p k).Prime).card : ℝ) := by
  rw [primeWinnerSum_mul_endpoint p K hp]
  have hset : insert 1 (Icc 2 K) = Icc 1 K := insert_Icc_succ_left_eq_Icc hK
  rw [← hset,sum_insert (by simp)]
  simp only [one_mul]
  have hd2 : 2 ∣ p+1 := by
    have hh := Nat.dvd_add (hdiv 2 (by omega) (by omega)) (dvd_refl 2)
    convert hh using 1
    omega
  rw [primeWinnerContribution_first_pair p hp (by omega) hd2,zero_add]
  rw [← sum_boole,← sum_neg_distrib]
  apply sum_congr rfl
  intro k hk
  obtain ⟨hk2,hkK⟩ := mem_Icc.mp hk
  rw [negative_congruence_run_pair_contribution p k hp hk2 (by omega)
    (hdiv (k+1) (by omega) (by omega)) (hdiv (k-1) (by omega) (by omega))]
  split_ifs <;> norm_num

lemma primeWinner_31_187_counts :
    primeWinnerRises 31 187 = 3 ∧ primeWinnerFalls 31 187 = 5 := by
  decide +kernel

/-- A structured, exactly certified negative current, with only five
multiples to inspect after reindexing the prime group. -/
lemma primeWinnerSum_67801_339006 : primeWinnerSum 67801 339006 = -4 := by
  have hdiv : ∀ j ∈ Icc 1 6, j ∣ 67800 := by decide +kernel
  have h := primeWinnerSum_negative_congruence_run 67801 5 (by norm_num)
    (by omega) (by omega) (fun j hj hJ => hdiv j (mem_Icc.mpr ⟨hj,hJ⟩))
  have hc : ((Icc 2 5).filter fun k => (negativeRunQuotient 67801 k).Prime).card = 4 := by
    have hset : Icc 2 5 = ({2,3,4,5} : Finset ℕ) := by decide +kernel
    norm_num [hset,negativeRunQuotient,filter_insert,filter_singleton]
  rw [hc] at h
  exact h

/-- This refutes only a proposed lower bound for individual currents. -/
theorem not_primeWinnerSum_ge_neg_one :
    ¬ ∀ p N : ℕ, p.Prime → -1 ≤ primeWinnerSum p N := by
  intro h
  have hh := h 67801 339006 (by norm_num)
  rw [primeWinnerSum_67801_339006] at hh
  norm_num at hh

#print axioms negative_congruence_run_pair_contribution
#print axioms primeWinnerSum_negative_congruence_run
#print axioms primeWinnerSum_67801_339006
#print axioms not_primeWinnerSum_ge_neg_one
end Erdos371
