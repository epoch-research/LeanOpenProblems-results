import Submission.SameIntegerPrimeGap
import Submission.LargeRepeatedAtoms
import Submission.ComparisonAllocationApproximation
import Submission.LogNearTieRarity

/-! Positive power buffers for all atoms in the losing integer and winning
cofactor, away from explicit rare events. This allows uninflated box cutoffs. -/
namespace Erdos371
open Finset Filter RandomBins FiniteSieve
open scoped Topology

lemma losing_prime_power_separation (N n : ℕ) (η : ℝ) (hN : 1 ≤ N)
    (hη : 0 ≤ η) (hno : ¬logRatioEvent N η n) :
    (N : ℝ)^η * Nat.maxPrimeFac (losingNumber n) < primeWinner n := by
  have hpow : (1 : ℝ) ≤ (N : ℝ)^η := Real.one_le_rpow (by exact_mod_cast hN) hη
  have hn : (0 : ℝ) ≤ Nat.maxPrimeFac n := Nat.cast_nonneg _
  have hn' : (0 : ℝ) ≤ Nat.maxPrimeFac (n+1) := Nat.cast_nonneg _
  unfold logRatioEvent at hno
  unfold losingNumber primeWinner
  split_ifs with h
  · rw [max_eq_right h.le]
    push_neg at hno
    have hfirst : (Nat.maxPrimeFac n : ℝ) ≤ (N : ℝ)^η*Nat.maxPrimeFac (n+1) := by
      have hh : (Nat.maxPrimeFac n : ℝ) ≤ Nat.maxPrimeFac (n+1) := by exact_mod_cast h.le
      nlinarith
    exact hno hfirst
  · rw [max_eq_left (not_lt.mp h)]
    by_contra hbad
    apply hno
    constructor
    · exact le_of_not_gt hbad
    · have hh : (Nat.maxPrimeFac (n+1) : ℝ) ≤ Nat.maxPrimeFac n := by exact_mod_cast not_lt.mp h
      nlinarith

lemma prime_divisor_power_separation (N m p q : ℕ) (v η : ℝ)
    (hm : 0 < m) (hmN : m ≤ N) (hp : p.Prime) (hq : q.Prime) (hqp : q < p)
    (hpm : p ∣ m) (hqm : q ∣ m) (hpv : (N : ℝ)^v ≤ p)
    (hno : ¬sameIntegerPrimeGapEvent N v η m) : (N : ℝ)^η*q < p := by
  classical
  by_contra hbad
  apply hno
  have hpN : p ≤ N := (Nat.le_of_dvd hm hpm).trans hmN
  have hqN : q ≤ N := (Nat.le_of_dvd hm hqm).trans hmN
  refine ⟨p,mem_filter.mpr ⟨Nat.mem_primesBelow.mpr ⟨by omega,hp⟩,hpv⟩,
    q,mem_filter.mpr ⟨Nat.mem_primesBelow.mpr ⟨by omega,hq⟩,hqp,le_of_not_gt hbad⟩,?_⟩
  exact ((Nat.coprime_primes hp hq).mpr (by omega)).mul_dvd_of_dvd_of_dvd hpm hqm

lemma winning_prime_not_dvd_cofactor (m p : ℕ) (hm : 0 < m) (hp : p.Prime)
    (hpm : p ∣ m) (X : ℝ) (hXp : X < p) (hno : ¬largeRepeatedAtom X m) :
    ¬p ∣ m/p := by
  intro hd
  have hp2 : p^2 ∣ m := by
    rw [pow_two,← Nat.mul_div_cancel' hpm]
    exact Nat.mul_dvd_mul_left p hd
  have he : 2 ≤ m.factorization p := (hp.pow_dvd_iff_le_factorization hm.ne').mp hp2
  have hpow : p ≤ p^m.factorization p := by
    simpa only [pow_one] using Nat.pow_le_pow_right hp.pos (by omega : 1 ≤ m.factorization p)
  exact hno ⟨p,Nat.mem_primeFactors.mpr ⟨hp,hpm,hm.ne'⟩,he,
    hXp.trans_le (by exact_mod_cast hpow)⟩

/-- A buffer holds simultaneously for every atom in each of the two integers
being allocated. The hypotheses name every discarded arithmetic event. -/
theorem comparison_atoms_power_buffer (N n : ℕ) (hN : 1 < N) (hn : 1 < n) (hnN : n < N)
    (v η : ℝ) (hv : 0 < v) (hη : 0 < η) (hηv : η ≤ v/2)
    (hpv : (N : ℝ)^v ≤ primeWinner n)
    (hclose : ¬logRatioEvent N η n)
    (hrep : ¬largeRepeatedAtom ((N : ℝ)^η) n)
    (hrep' : ¬largeRepeatedAtom ((N : ℝ)^η) (n+1))
    (hgap : ¬sameIntegerPrimeGapEvent N v η (winningNumber n)) :
    (∀ i : PrimeAtomIndex (losingNumber n),
      (primePowerAtom (losingNumber n) i : ℝ) ≤ (primeWinner n : ℝ)/(N : ℝ)^η) ∧
    (∀ i : PrimeAtomIndex (winningNumber n / primeWinner n),
      (primePowerAtom (winningNumber n / primeWinner n) i : ℝ) ≤
        (primeWinner n : ℝ)/(N : ℝ)^η) := by
  obtain ⟨hl,hw,hlN,hwN⟩ := comparison_numbers_bounds n hn
  obtain ⟨hp,hlp,hwp⟩ := comparison_numbers_prime_factors n hn
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hNr1 : (1 : ℝ) < N := by exact_mod_cast hN
  have hpow : 0 < (N : ℝ)^η := Real.rpow_pos_of_pos hNr η
  have hsmall : (N : ℝ)^η ≤ (primeWinner n : ℝ)/(N : ℝ)^η := by
    apply (le_div_iff₀ hpow).mpr
    rw [← Real.rpow_add hNr]
    exact (Real.rpow_le_rpow_of_exponent_le hNr1.le (by linarith : η+η ≤ v)).trans hpv
  have hXp : (N : ℝ)^η < primeWinner n :=
    (Real.rpow_lt_rpow_of_exponent_lt hNr1 (by linarith : η < v)).trans_le hpv
  have hrepL : ¬largeRepeatedAtom ((N : ℝ)^η) (losingNumber n) := by
    unfold losingNumber
    split_ifs <;> assumption
  have hrepW : ¬largeRepeatedAtom ((N : ℝ)^η) (winningNumber n) := by
    unfold winningNumber
    split_ifs <;> assumption
  have hd : primeWinner n ∣ winningNumber n := by rw [← hwp]; exact Nat.maxPrimeFac_dvd
  have hq : 0 < winningNumber n / primeWinner n :=
    Nat.div_pos (Nat.le_of_dvd (by omega) hd) hp.pos
  have hnd := winning_prime_not_dvd_cofactor (winningNumber n) (primeWinner n)
    (by omega) hp hd ((N : ℝ)^η) hXp hrepW
  constructor
  · intro i
    rcases primePowerAtom_small_or_prime (losingNumber n) _ hrepL i with hi | hi
    · exact hi.trans hsmall
    · rw [hi]
      have himax : i.val ≤ Nat.maxPrimeFac (losingNumber n) :=
        Nat.le_maxPrimeFac (by omega) (primeAtom_prime _ i) (Nat.mem_primeFactors.mp i.property).2.1
      have hsep := losing_prime_power_separation N n η hN.le hη.le hclose
      apply (le_div_iff₀ hpow).mpr
      have himax' : (i.val : ℝ) ≤ Nat.maxPrimeFac (losingNumber n) := by exact_mod_cast himax
      nlinarith
  · intro i
    have hdiv : winningNumber n / primeWinner n ∣ winningNumber n := Nat.div_dvd_of_dvd hd
    rcases divisor_atom_small_or_prime _ _ hq (by omega) hdiv _ hrepW i with hi | hi
    · exact hi.trans hsmall
    · rw [hi]
      have hip : i.val.Prime := primeAtom_prime _ i
      have hid : i.val ∣ winningNumber n / primeWinner n := (Nat.mem_primeFactors.mp i.property).2.1
      have hiw : i.val ∣ winningNumber n := hid.trans hdiv
      have himax : i.val ≤ primeWinner n :=
        (Nat.le_maxPrimeFac (by omega) hip hiw).trans_eq hwp
      have hine : i.val ≠ primeWinner n := by intro he; exact hnd (by simpa only [he] using hid)
      have hsep := prime_divisor_power_separation N (winningNumber n) (primeWinner n) i.val
        v η (by omega) (by omega) hp hip (lt_of_le_of_ne himax hine) hd hiw hpv hgap
      apply (le_div_iff₀ hpow).mpr
      nlinarith

namespace RandomBins
lemma primeAllocationRetention_buffer_bound (K N n p : ℕ)
    (hK : 0 < K) (hN : 1 < N) (hn : 0 < n) (hnN : n ≤ N) (hp : 0 < p)
    (v η : ℝ) (hv : 0 < v) (hη : 0 < η) (hpN : (N : ℝ)^v ≤ p)
    (hatom : ∀ i : PrimeAtomIndex n, (primePowerAtom n i : ℝ) ≤ (p : ℝ)/(N : ℝ)^η) :
    1-primeAllocationRetention K p n ≤ 1/((K : ℝ)*v*η) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
  let u : ℝ := Real.log p / Real.log N
  have hvu : v ≤ u := by
    apply (le_div_iff₀ hlog).mpr
    have h := Real.log_le_log (Real.rpow_pos_of_pos hNr v) hpN
    simpa only [Real.log_rpow hNr] using h
  have he : (N : ℝ)^u = p := rpow_log_quotient N p hN hp
  have hatom' : ∀ i : PrimeAtomIndex n, (primePowerAtom n i : ℝ) ≤ (N : ℝ)^(u-η) := by
    intro i
    rw [Real.rpow_sub hNr,he]
    exact hatom i
  have hb := primeAllocationRetention_lower K N n hK hN hn hnN u η
    (hv.trans_le hvu) hη hatom'
  rw [he] at hb
  have hden : (K : ℝ)*v*η ≤ (K : ℝ)*u*η := by gcongr
  have hdiv := one_div_le_one_div_of_le (by positivity : 0 < (K : ℝ)*v*η) hden
  linarith
end RandomBins

/-- Pointwise control of loss at the exact, uninflated winning-prime cutoff. -/
theorem comparisonAllocationWeight_zero_loss (K N n : ℕ) (hK : 0 < K)
    (hN : 1 < N) (hn : 1 < n) (hnN : n < N)
    (v η : ℝ) (hv : 0 < v) (hη : 0 < η) (hηv : η ≤ v/2)
    (hpv : (N : ℝ)^v ≤ primeWinner n)
    (hclose : ¬logRatioEvent N η n)
    (hrep : ¬largeRepeatedAtom ((N : ℝ)^η) n)
    (hrep' : ¬largeRepeatedAtom ((N : ℝ)^η) (n+1))
    (hgap : ¬sameIntegerPrimeGapEvent N v η (winningNumber n)) :
    1-comparisonAllocationWeight K N 0 n ≤ 2/((K : ℝ)*v*η) := by
  obtain ⟨hla,hqa⟩ := comparison_atoms_power_buffer N n hN hn hnN v η hv hη hηv
    hpv hclose hrep hrep' hgap
  obtain ⟨hl,hw,hlN,hwN⟩ := comparison_numbers_bounds n hn
  obtain ⟨hp,hlp,hwp⟩ := comparison_numbers_prime_factors n hn
  have hd : primeWinner n ∣ winningNumber n := by rw [← hwp]; exact Nat.maxPrimeFac_dvd
  have hq : 0 < winningNumber n / primeWinner n :=
    Nat.div_pos (Nat.le_of_dvd (by omega) hd) hp.pos
  have h₁ := primeAllocationRetention_buffer_bound K N (losingNumber n) (primeWinner n)
    hK hN (by omega) (by omega) hp.pos v η hv hη hpv hla
  have h₂ := primeAllocationRetention_buffer_bound K N (winningNumber n / primeWinner n)
    (primeWinner n) hK hN hq ((Nat.div_le_self _ _).trans (by omega)) hp.pos v η hv hη hpv hqa
  have hl' := primeAllocationRetention_mem_unit K hK (primeWinner n) (losingNumber n)
  have hq' := primeAllocationRetention_mem_unit K hK (primeWinner n) (winningNumber n / primeWinner n)
  have hmul := mul_nonneg (sub_nonneg.mpr hl'.2) (sub_nonneg.mpr hq'.2)
  simp only [comparisonAllocationWeight,Real.rpow_zero,mul_one]
  have he : 2/((K : ℝ)*v*η) = 1/((K : ℝ)*v*η)+1/((K : ℝ)*v*η) := by ring
  rw [he]
  nlinarith

#print axioms comparison_atoms_power_buffer
#print axioms comparisonAllocationWeight_zero_loss
end Erdos371
