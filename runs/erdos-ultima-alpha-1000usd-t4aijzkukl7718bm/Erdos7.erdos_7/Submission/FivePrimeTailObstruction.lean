import Submission.ArithmeticReduction

/-! A bounded-prime-support obstruction, not a solution of Erdős problem 7. -/
namespace Erdos7FivePrimeTail
open Erdos7FiniteSieve Erdos7Reduction
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

lemma finite_three_capacity_le_one (E : ℕ) : finitePrimeCapacity 3 E ≤ 1 := by
  have hs : positivePowerSum 3 E ≤ (1 / 2 : ℚ) := by
    have hh := positive_geometric_sum_le 3 (by norm_num)
      ((Finset.range (E + 1)).erase 0) (by
        intro n hn
        have := (Finset.mem_erase.mp hn).1
        omega)
    convert hh using 1
    norm_num
  have hlt := positivePowerSum_lt_one 3 E (by norm_num)
  unfold finitePrimeCapacity
  apply (div_le_one (by linarith : 0 < 1 - positivePowerSum 3 E)).mpr
  linarith

lemma five_capacity_lt_one (E : ℕ) :
    mixedCapacity (fun i : Fin 5 =>
      finitePrimeCapacity (firstFiveOddPrimes i) (![E, 2, 1, 1, 1] i)) < 1 := by
  let z : Fin 5 → ℚ := ![1, 6 / 19, 1 / 6, 1 / 10, 1 / 12]
  have hle : mixedCapacity (fun i : Fin 5 =>
      finitePrimeCapacity (firstFiveOddPrimes i) (![E, 2, 1, 1, 1] i)) ≤ mixedCapacity z := by
    apply mixedCapacity_mono
    · intro i
      apply finitePrimeCapacity_nonneg
      fin_cases i <;> norm_num [firstFiveOddPrimes]
    · intro i
      fin_cases i
      · simpa [firstFiveOddPrimes, z] using finite_three_capacity_le_one E
      all_goals norm_num [firstFiveOddPrimes, z, finitePrimeCapacity,
        positivePowerSum_eq_sum, Finset.sum_range_succ]
  have hval : mixedCapacity z = (6791 / 6840 : ℚ) := by
    rw [mixedCapacity_eq]
    norm_num [z, Fin.prod_univ_succ, Fin.sum_univ_succ]
  rw [hval] at hle
  exact hle.trans_lt (by norm_num)

/-- No distinct nontrivial congruence cover on 3,5,7,11,13 can have
exponent at5 at most2 and exponents at7,11,13 at most1, even with
arbitrarily large (finite) exponent at3. -/
theorem not_cover {κ : Type*} [Fintype κ]
    (E : ℕ) (e : κ → Fin 5 → ℕ) (he : Function.Injective e)
    (he0 : ∀ k, ∃ i, e k i ≠ 0)
    (heE : ∀ k i, e k i ≤ (![E, 2, 1, 1, 1] : Fin 5 → ℕ) i)
    (a : κ → ℤ) :
    ¬ (∀ x : ℤ, ∃ k,
      ((∏ i, firstFiveOddPrimes i ^ e k i : ℕ) : ℤ) ∣ x - a k) := by
  intro hc
  have hp : ∀ i : Fin 5, 2 < firstFiveOddPrimes i := by
    intro i
    fin_cases i <;> norm_num [firstFiveOddPrimes]
  have hcop : Pairwise (Function.onFun Nat.Coprime firstFiveOddPrimes) := by
    change ∀ i j : Fin 5, i ≠ j → Nat.Coprime (firstFiveOddPrimes i) (firstFiveOddPrimes j)
    decide +kernel
  have hb := finite_exponent_cover_bound firstFiveOddPrimes ![E, 2, 1, 1, 1]
    hp hcop e he he0 heE a hc
  exact (not_lt_of_ge hb) (five_capacity_lt_one E)

/-- Arithmetic form of the obstruction: no finite strict cover has all its
moduli dividing `3^E * 25025`, where `25025 = 5^2 * 7 * 11 * 13`. -/
theorem not_cover_divisors {κ : Type*} [Fintype κ]
    (E : ℕ) (m : κ → ℕ) (a : κ → ℤ)
    (hm : ∀ k, 1 < m k) (hmi : Function.Injective m)
    (hd : ∀ k, m k ∣ 3^E * 25025) :
    ¬ (∀ x : ℤ, ∃ k, (m k : ℤ) ∣ x - a k) := by
  classical
  intro hc
  let p := firstFiveOddPrimes
  let caps : Fin 5 → ℕ := ![E, 2, 1, 1, 1]
  let P := Finset.univ.image p
  have hp : ∀ i, (p i).Prime := by
    intro i
    fin_cases i <;> norm_num [p, firstFiveOddPrimes]
  have hpi : Function.Injective p := by
    change ∀ i j : Fin 5, p i = p j → i = j
    decide +kernel
  have hN0 : 3^E * 25025 ≠ 0 := by positivity
  have hNprod : 3^E * 25025 = ∏ i, p i ^ caps i := by
    norm_num [p, firstFiveOddPrimes, caps, Fin.prod_univ_succ]
  have hsmall : (25025 : ℕ).primeFactors = {5, 7, 11, 13} := by decide +kernel
  have hPF (k : κ) : (m k).primeFactors ⊆ P := by
    intro q hq
    obtain ⟨hqprime, hqd, _⟩ := Nat.mem_primeFactors.mp hq
    have hqN := hqd.trans (hd k)
    rcases hqprime.dvd_mul.mp hqN with h3 | hrest
    · have hq3 := hqprime.dvd_of_dvd_pow h3
      have heq : q = 3 := by
        rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hq3 with h | h
        · exact (hqprime.ne_one h).elim
        · exact h
      subst q
      exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
    · have hmem := Nat.mem_primeFactors.mpr ⟨hqprime, hrest, by norm_num⟩
      rw [hsmall] at hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with rfl | rfl | rfl | rfl
      · exact Finset.mem_image.mpr ⟨1, Finset.mem_univ _, rfl⟩
      · exact Finset.mem_image.mpr ⟨2, Finset.mem_univ _, rfl⟩
      · exact Finset.mem_image.mpr ⟨3, Finset.mem_univ _, rfl⟩
      · exact Finset.mem_image.mpr ⟨4, Finset.mem_univ _, rfl⟩
  let e (k : κ) (i : Fin 5) := (m k).factorization (p i)
  have hm0 (k : κ) : m k ≠ 0 := by have := hm k; omega
  have hprod (k : κ) : m k = ∏ i, p i ^ e k i := by
    have hh := Erdos7Compression.factorization_product_over_superset (m k) (hm0 k) P (hPF k)
    rw [Finset.prod_coe_sort P (fun q => q ^ (m k).factorization q)] at hh
    rw [hh]
    exact Finset.prod_image (fun i _ j _ hij => hpi hij)
  have hei : Function.Injective e := by
    intro k l hkl
    apply hmi
    rw [hprod k, hprod l, hkl]
  have he0 (k : κ) : ∃ i, e k i ≠ 0 := by
    by_contra! hh
    have hk := hm k
    rw [hprod k] at hk
    simp only [hh, pow_zero, Finset.prod_const_one] at hk
    omega
  have heE (k : κ) (i : Fin 5) : e k i ≤ caps i := by
    have hle := (Nat.factorization_le_iff_dvd (hm0 k) hN0).mpr (hd k)
    have hv := hle (p i)
    rw [hNprod, Erdos7Compression.factorization_prime_power_product p hp hpi caps i] at hv
    exact hv
  apply not_cover E e hei he0 heE a
  change ∀ x : ℤ, ∃ k, ((∏ i, p i ^ e k i : ℕ) : ℤ) ∣ x - a k
  simpa only [← hprod] using hc

theorem not_all_moduli_dvd (C : StrictCoveringSystem ℤ) (E : ℕ) :
    ¬ (∀ i, (C.moduli i).absNorm ∣ 3^E * 25025) := by
  letI := C.fintypeIndex
  intro hd
  exact not_cover_divisors E (fun i => (C.moduli i).absNorm) C.residue
    (moduli_absNorm_gt_one C) (moduli_absNorm_injective C) hd (arithmetic_cover C)

#print axioms not_all_moduli_dvd
#print axioms not_cover_divisors

#print axioms not_cover
end Erdos7FivePrimeTail
