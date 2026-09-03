import Submission.PrimeBlockArithmetic

/-! Upper exponential moments from exact counts of multiples. No bound on
prime sizes, CRT rounding error, or independence of consecutive integers is
needed for these upper bounds. -/
namespace Erdos371.FiniteSieve
open Finset

lemma prime_finset_prod_dvd_iff (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (n : ℕ) :
    (∏ p ∈ S, p) ∣ n ↔ ∀ p ∈ S, p ∣ n := by
  have hc : (S : Set ℕ).Pairwise (Function.onFun Nat.Coprime id) := by
    intro p hp q hq hpq
    exact (Nat.coprime_primes (hS p hp) (hS q hq)).mpr hpq
  simpa only [Nat.modEq_zero_iff_dvd,id_eq] using modEq_finset_prod_iff S id hc n 0

lemma primeDivisorCountIn_power_expansion (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (z : ℝ) (n : ℕ) :
    z^(primeDivisorCountIn P n) =
      ∑ S ∈ P.powerset, if (∏ p ∈ S, p) ∣ n then (z-1)^S.card else 0 := by
  have he : (P.filter (fun p => p ∣ n)).powerset=
      P.powerset.filter (fun S => (∏ p ∈ S, p) ∣ n) := by
    ext S
    simp only [mem_powerset,mem_filter]
    constructor
    · intro hS
      refine ⟨hS.trans (filter_subset _ _),?_⟩
      apply (prime_finset_prod_dvd_iff S (fun p hp => hP p (mem_filter.mp (hS hp)).1) n).mpr
      exact fun p hp => (mem_filter.mp (hS hp)).2
    · rintro ⟨hSP,hprod⟩
      have hd := (prime_finset_prod_dvd_iff S (fun p hp => hP p (hSP hp)) n).mp hprod
      intro p hp
      exact mem_filter.mpr ⟨hSP hp,hd p hp⟩
  have h := prod_add_one (f := fun _p : ℕ => z-1) (P.filter (fun p => p ∣ n))
  simp only [sub_add_cancel,prod_const] at h
  rw [he,sum_filter] at h
  exact h

lemma primeDivisorCountIn_exp_moment_exact (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (z : ℝ) (N : ℕ) :
    (∑ n ∈ range N, z^(primeDivisorCountIn P (n+1))) =
      ∑ S ∈ P.powerset, (z-1)^S.card*((N/(∏ p ∈ S, p) : ℕ) : ℝ) := by
  simp_rw [primeDivisorCountIn_power_expansion P hP z]
  rw [sum_comm]
  apply sum_congr rfl
  intro S _
  rw [← sum_filter,sum_const,nsmul_eq_mul,Nat.card_multiples]
  ring

/-- A one-integer exponential moment with no error term and no upper bound
on the selected primes. -/
theorem primeDivisorCountIn_exp_moment_bound (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (z : ℝ) (hz : 1 ≤ z) (N : ℕ) :
    (∑ n ∈ range N, z^(primeDivisorCountIn P (n+1))) ≤
      N*Real.exp ((z-1)*primeReciprocalMass P) := by
  have hzm : 0 ≤ z-1 := by linarith
  rw [primeDivisorCountIn_exp_moment_exact P hP z N]
  calc
    _ ≤ ∑ S ∈ P.powerset, (z-1)^S.card*((N : ℝ)/(∏ p ∈ S, p : ℕ)) :=
      sum_le_sum fun S _ => mul_le_mul_of_nonneg_left Nat.cast_div_le (pow_nonneg (by linarith) _)
    _ = (N : ℝ)*∏ p ∈ P, (1+(z-1)/(p : ℝ)) := by
      rw [prod_one_add,mul_sum]
      apply sum_congr rfl
      intro S _
      rw [prod_div_distrib,prod_const,← Nat.cast_prod]
      ring
    _ ≤ (N : ℝ)*Real.exp ((z-1)*primeReciprocalMass P) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg N)
      rw [primeReciprocalMass,mul_sum,Real.exp_sum]
      apply prod_le_prod (fun p _ => by positivity)
      intro p _
      have h := Real.add_one_le_exp ((z-1)/(p : ℝ))
      simpa only [mul_one_div,add_comm] using h

lemma activeBlockPrimes_card_consecutive (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (n : ℕ) :
    (activeBlockPrimes P (activePrimeAtoms P n)).card =
      primeDivisorCountIn P n+primeDivisorCountIn P (n+1) := by
  rw [activeBlockPrimes_arithmetic P hP n]
  have he : P.filter (fun p => p ∣ n*(n+1))=
      P.filter (fun p => p ∣ n) ∪ P.filter (fun p => p ∣ n+1) := by
    rw [← filter_or]
    apply filter_congr
    intro p hp
    exact (hP p hp).dvd_mul
  rw [he,card_union_of_disjoint]
  · rfl
  · apply disjoint_left.mpr
    intro p hp hq
    have hpP := (mem_filter.mp hp).1
    have hd := (mem_filter.mp hp).2
    have hs := (mem_filter.mp hq).2
    exact (hP p hpP).not_dvd_one ((Nat.dvd_add_iff_right hd).mpr hs)

/-- Cauchy--Schwarz transfers one-integer moments to consecutive integers.
The endpoint loss N+1 is explicit, and all prime sizes are allowed. -/
theorem activeBlockPrimes_exp_moment_sum (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (z : ℝ) (hz : 1 ≤ z) (N : ℕ) :
    (∑ n ∈ range N, z^(activeBlockPrimes P (activePrimeAtoms P (n+1))).card) ≤
      (N+1 : ℝ)*Real.exp ((z^2-1)*primeReciprocalMass P) := by
  have hz0 : 0 ≤ z := by linarith
  have hz2 : 1 ≤ z^2 := one_le_pow₀ hz
  let E := Real.exp ((z^2-1)*primeReciprocalMass P)
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have ha : (∑ n ∈ range N, (z^(primeDivisorCountIn P (n+1)))^2) ≤ (N+1 : ℝ)*E := by
    have h := primeDivisorCountIn_exp_moment_bound P hP (z^2) hz2 N
    have he (m : ℕ) : (z^m)^2=(z^2)^m := by rw [← pow_mul,mul_comm m 2,pow_mul]
    simp_rw [he]
    exact h.trans (mul_le_mul_of_nonneg_right (by linarith) hE)
  have hb : (∑ n ∈ range N, (z^(primeDivisorCountIn P (n+2)))^2) ≤ (N+1 : ℝ)*E := by
    have h := primeDivisorCountIn_exp_moment_bound P hP (z^2) hz2 (N+1)
    have he (m : ℕ) : (z^m)^2=(z^2)^m := by rw [← pow_mul,mul_comm m 2,pow_mul]
    simp_rw [he]
    rw [sum_range_succ'] at h
    push_cast at h
    have h0 : 0 ≤ (z^2)^(primeDivisorCountIn P 1) := by positivity
    simpa only [Nat.add_assoc,Nat.reduceAdd] using (le_add_of_nonneg_right h0).trans h
  simp_rw [activeBlockPrimes_card_consecutive P hP,pow_add,Nat.add_assoc,Nat.reduceAdd]
  have hcs := sum_mul_sq_le_sq_mul_sq (range N)
    (fun n => z^(primeDivisorCountIn P (n+1))) (fun n => z^(primeDivisorCountIn P (n+2)))
  have hprod := mul_le_mul ha hb (sum_nonneg fun n _ => sq_nonneg _) (mul_nonneg (by positivity) hE)
  have hsnonneg : 0 ≤ ∑ n ∈ range N, z^(primeDivisorCountIn P (n+1))*z^(primeDivisorCountIn P (n+2)) := by positivity
  have hrnonneg : 0 ≤ (N+1 : ℝ)*E := by positivity
  nlinarith

#print axioms primeDivisorCountIn_exp_moment_bound
#print axioms activeBlockPrimes_exp_moment_sum
end Erdos371.FiniteSieve
