import Submission.PrimeWinnerEnergy

/-! Exact increments of prime-winner energy. These identities expose the
signed cross terms; no linear energy bound or cancellation is asserted. -/

namespace Erdos371
open Finset

lemma primeWinnerLabels_mono {M N : ℕ} (hMN : M ≤ N) :
    primeWinnerLabels M ⊆ primeWinnerLabels N := by
  intro p hp
  obtain hp | hp := mem_insert.mp hp
  · exact mem_insert.mpr (Or.inl hp)
  · apply mem_insert.mpr
    apply Or.inr
    obtain ⟨hpM,hprime⟩ := Nat.mem_primesBelow.mp hp
    exact Nat.mem_primesBelow.mpr ⟨by omega,hprime⟩

lemma primeWinnerSum_eq_zero_of_not_mem (p N : ℕ)
    (hp : p ∉ primeWinnerLabels N) : primeWinnerSum p N = 0 := by
  unfold primeWinnerSum
  apply sum_eq_zero
  intro n hn
  obtain ⟨hn,he⟩ := mem_filter.mp hn
  exact (hp (he ▸ primeWinner_mem_labels N n hn)).elim

lemma primeWinnerSum_succ (p N : ℕ) :
    primeWinnerSum p (N+1) = primeWinnerSum p N +
      if primeWinner N = p then factorSign N else 0 := by
  simp only [primeWinnerSum, sum_filter, sum_range_succ]

lemma primeWinnerEnergy_enlarge_labels {M N : ℕ} (hMN : M ≤ N) :
    primeWinnerEnergy M = ∑ p ∈ primeWinnerLabels N, (primeWinnerSum p M)^2 := by
  unfold primeWinnerEnergy
  apply sum_subset (primeWinnerLabels_mono hMN)
  intro p hpN hpM
  rw [primeWinnerSum_eq_zero_of_not_mem p M hpM]
  norm_num

lemma factorSign_sq (n : ℕ) : (factorSign n)^2 = 1 := by
  unfold factorSign predicateSign
  split_ifs <;> norm_num

/-- Each new comparison changes just one prime group. The mixed term can
have either sign; it is not discarded in this formula. -/
theorem primeWinnerEnergy_succ (N : ℕ) :
    primeWinnerEnergy (N+1) = primeWinnerEnergy N +
      2*factorSign N*primeWinnerSum (primeWinner N) N+1 := by
  rw [primeWinnerEnergy_enlarge_labels (show N ≤ N+1 by omega)]
  unfold primeWinnerEnergy
  simp_rw [primeWinnerSum_succ]
  have he (p : ℕ) :
      (primeWinnerSum p N + (if primeWinner N = p then factorSign N else 0))^2 =
        (primeWinnerSum p N)^2 +
          (if primeWinner N = p then
            2*factorSign N*primeWinnerSum (primeWinner N) N+1 else 0) := by
    by_cases hp : primeWinner N = p
    · subst p
      simp only [if_true]
      nlinarith [factorSign_sq N]
    · simp only [if_neg hp, add_zero]
  simp_rw [he, sum_add_distrib]
  rw [sum_ite_eq]
  have hw : primeWinner N ∈ primeWinnerLabels (N+1) :=
    primeWinner_mem_labels (N+1) N (mem_range.mpr (by omega))
  rw [if_pos hw]
  ring

noncomputable def primeWinnerCrossSum (N : ℕ) : ℝ :=
  ∑ n ∈ range N, factorSign n*primeWinnerSum (primeWinner n) n

/-- Exact diagonal/off-diagonal decomposition, with each off-diagonal
pair counted only once in the cross sum. -/
theorem primeWinnerEnergy_eq_diagonal_add_cross (N : ℕ) :
    primeWinnerEnergy N = (N : ℝ)+2*primeWinnerCrossSum N := by
  induction N with
  | zero => simp [primeWinnerEnergy,primeWinnerSum,primeWinnerCrossSum]
  | succ N ih =>
    rw [primeWinnerEnergy_succ,ih]
    simp only [primeWinnerCrossSum,sum_range_succ,Nat.cast_add,Nat.cast_one]
    ring

lemma primeWinnerCrossSum_pair_formula (N : ℕ) :
    primeWinnerCrossSum N = ∑ n ∈ range N,
      ∑ m ∈ range n, if primeWinner m = primeWinner n then
        factorSign n*factorSign m else 0 := by
  unfold primeWinnerCrossSum primeWinnerSum
  simp_rw [sum_filter,mul_sum]
  apply sum_congr rfl
  intro n hn
  apply sum_congr rfl
  intro m hm
  split_ifs <;> simp

/-- Thus the candidate finite bound E(N)<=N is exactly a nonpositive
cumulative signed cross-term assertion. That assertion remains unproved. -/
theorem primeWinnerEnergy_le_diagonal_iff (N : ℕ) :
    primeWinnerEnergy N ≤ N ↔ primeWinnerCrossSum N ≤ 0 := by
  rw [primeWinnerEnergy_eq_diagonal_add_cross]
  constructor <;> intro h <;> linarith

#print axioms primeWinnerEnergy_succ
#print axioms primeWinnerEnergy_eq_diagonal_add_cross
#print axioms primeWinnerEnergy_le_diagonal_iff

end Erdos371
