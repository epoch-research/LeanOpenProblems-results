import Submission.ComparisonAllocationApproximation
import Submission.CoprimeAllocationTuples

/-! Exact tuple expansion of the approximation weight. The expansion keeps
both product constraints and does not assert signed cancellation. -/
namespace Erdos371
open Finset RandomBins

lemma maxPrimeFac_finset_prod_lt_iff {ι : Type*} (s : Finset ι) (f : ι → ℕ)
    (hf : ∀ i ∈ s, 0 < f i) (p : ℕ) (hp : 1 < p) :
    Nat.maxPrimeFac (∏ i ∈ s, f i) < p ↔ ∀ i ∈ s, Nat.maxPrimeFac (f i) < p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hp]
  | @insert i s hi ih =>
    have hf' : ∀ j ∈ s, 0 < f j := fun j hj => hf j (mem_insert_of_mem hj)
    rw [prod_insert hi,Nat.maxPrimeFac_mul (hf i (mem_insert_self _ _)).ne'
      (prod_pos hf').ne',max_lt_iff,ih hf']
    simp

lemma maxPrimeFac_finset_prod_le_iff {ι : Type*} (s : Finset ι) (f : ι → ℕ)
    (hf : ∀ i ∈ s, 0 < f i) (p : ℕ) (hp : 1 ≤ p) :
    Nat.maxPrimeFac (∏ i ∈ s, f i) ≤ p ↔ ∀ i ∈ s, Nat.maxPrimeFac (f i) ≤ p := by
  simpa only [Nat.lt_succ_iff] using
    maxPrimeFac_finset_prod_lt_iff s f hf (p+1) (by omega)

/-- An exact two-sided tuple expansion. In particular the winning cofactor's
product equation is not dropped after introducing the congruence modulo p. -/
theorem comparisonAllocationWeight_eq_tuple_sum (K N n : ℕ) (δ : ℝ)
    (hn : 1 < n) (hnN : n < N) :
    comparisonAllocationWeight K N δ n =
      ∑ A ∈ (smallCoprimeTuples K N ((primeWinner n : ℝ)*(N : ℝ)^δ)).filter
        (fun A => ∏ c, A c = losingNumber n),
      ∑ B ∈ (smallCoprimeTuples K N ((primeWinner n : ℝ)*(N : ℝ)^δ)).filter
        (fun B => primeWinner n * ∏ c, B c = winningNumber n),
        (∏ c, allocationWeight K (A c)) * (∏ c, allocationWeight K (B c)) := by
  classical
  obtain ⟨hl,hw,hlN,hwN⟩ := comparison_numbers_bounds n hn
  obtain ⟨hp,hlp,hwp⟩ := comparison_numbers_prime_factors n hn
  have hd : primeWinner n ∣ winningNumber n := by rw [← hwp]; exact Nat.maxPrimeFac_dvd
  have hq : 0 < winningNumber n / primeWinner n :=
    Nat.div_pos (Nat.le_of_dvd (by omega) hd) hp.pos
  have heq : ∀ q : ℕ, q = winningNumber n / primeWinner n ↔ primeWinner n*q = winningNumber n := by
    intro q
    constructor
    · rintro rfl; exact Nat.mul_div_cancel' hd
    · intro h
      apply Nat.eq_of_mul_eq_mul_left hp.pos
      rw [Nat.mul_div_cancel' hd]
      exact h
  unfold comparisonAllocationWeight
  rw [primeAllocationRetention_eq_tuple_sum K N (losingNumber n) (by omega) (by omega),
    primeAllocationRetention_eq_tuple_sum K N (winningNumber n / primeWinner n) hq.ne'
      ((Nat.div_le_self _ _).trans (by omega)),sum_mul_sum]
  simp_rw [heq]

/-- All tuple entries in the losing fiber have prime factors below the winner;
all winning-cofactor entries have prime factors at most the winner. -/
lemma comparison_tuple_prime_bounds (K N n : ℕ) (δ : ℝ) (hn : 1 < n)
    (A B : Fin K → ℕ)
    (hA : A ∈ smallCoprimeTuples K N ((primeWinner n : ℝ)*(N : ℝ)^δ))
    (hB : B ∈ smallCoprimeTuples K N ((primeWinner n : ℝ)*(N : ℝ)^δ))
    (hprodA : ∏ c, A c = losingNumber n)
    (hprodB : primeWinner n * ∏ c, B c = winningNumber n) :
    (∀ c, Nat.maxPrimeFac (A c) < primeWinner n) ∧
    (∀ c, Nat.maxPrimeFac (B c) ≤ primeWinner n) := by
  obtain ⟨hp,hlp,hwp⟩ := comparison_numbers_prime_factors n hn
  have ha := (mem_smallCoprimeTuples _ _ _ _).mp hA
  have hb := (mem_smallCoprimeTuples _ _ _ _).mp hB
  constructor
  · have h := (maxPrimeFac_finset_prod_lt_iff univ A
      (fun c _ => (ha.1 c).1) (primeWinner n) hp.one_lt).mp (by rwa [hprodA])
    simpa using h
  · have hpos : 0 < ∏ c, B c := prod_pos (fun c _ => (hb.1 c).1)
    have hle : Nat.maxPrimeFac (∏ c, B c) ≤ primeWinner n := by
      rw [← hprodB,Nat.maxPrimeFac_mul hp.ne_zero hpos.ne',hp.maxPrimeFac_eq_self] at hwp
      exact (le_max_right _ _).trans_eq hwp
    have h := (maxPrimeFac_finset_prod_le_iff univ B
      (fun c _ => (hb.1 c).1) (primeWinner n) (by have := hp.two_le; omega)).mp hle
    simpa using h

/-- Conversely, the tuple prime-factor conditions and the plus product equation
identify a rising comparison and its winning prime. -/
lemma rising_of_tuple_equation (K p n : ℕ) (hp : p.Prime) (A B : Fin K → ℕ)
    (hA : ∀ c, 0 < A c) (hB : ∀ c, 0 < B c)
    (hAP : ∀ c, Nat.maxPrimeFac (A c) < p)
    (hBP : ∀ c, Nat.maxPrimeFac (B c) ≤ p)
    (hprodA : ∏ c, A c = n) (hprodB : p * ∏ c, B c = n+1) :
    Nat.maxPrimeFac n < Nat.maxPrimeFac (n+1) ∧ primeWinner n = p := by
  have hl : Nat.maxPrimeFac n < p := by
    rw [← hprodA]
    exact (maxPrimeFac_finset_prod_lt_iff univ A (fun c _ => hA c) p hp.one_lt).mpr
      (fun c _ => hAP c)
  have hw : Nat.maxPrimeFac (n+1) = p := by
    rw [← hprodB,Nat.maxPrimeFac_mul hp.ne_zero (prod_pos (fun c _ => hB c)).ne',
      hp.maxPrimeFac_eq_self,max_eq_left]
    exact (maxPrimeFac_finset_prod_le_iff univ B (fun c _ => hB c) p
      (by have := hp.two_le; omega)).mpr (fun c _ => hBP c)
  exact ⟨by rwa [hw],by simp only [primeWinner,hw,max_eq_right hl.le]⟩

/-- The minus equation instead identifies a falling comparison. It has the
same coefficient factors, but it is a different set of integer solutions. -/
lemma falling_of_tuple_equation (K p n : ℕ) (hp : p.Prime) (A B : Fin K → ℕ)
    (hA : ∀ c, 0 < A c) (hB : ∀ c, 0 < B c)
    (hAP : ∀ c, Nat.maxPrimeFac (A c) < p)
    (hBP : ∀ c, Nat.maxPrimeFac (B c) ≤ p)
    (hprodA : ∏ c, A c = n+1) (hprodB : p * ∏ c, B c = n) :
    Nat.maxPrimeFac (n+1) < Nat.maxPrimeFac n ∧ primeWinner n = p := by
  have hl : Nat.maxPrimeFac (n+1) < p := by
    rw [← hprodA]
    exact (maxPrimeFac_finset_prod_lt_iff univ A (fun c _ => hA c) p hp.one_lt).mpr
      (fun c _ => hAP c)
  have hw : Nat.maxPrimeFac n = p := by
    rw [← hprodB,Nat.maxPrimeFac_mul hp.ne_zero (prod_pos (fun c _ => hB c)).ne',
      hp.maxPrimeFac_eq_self,max_eq_left]
    exact (maxPrimeFac_finset_prod_le_iff univ B (fun c _ => hB c) p
      (by have := hp.two_le; omega)).mpr (fun c _ => hBP c)
  exact ⟨by rwa [hw],by simp only [primeWinner,hw,max_eq_left hl.le]⟩

#print axioms comparisonAllocationWeight_eq_tuple_sum
#print axioms comparison_tuple_prime_bounds
#print axioms rising_of_tuple_equation
#print axioms falling_of_tuple_equation
end Erdos371
