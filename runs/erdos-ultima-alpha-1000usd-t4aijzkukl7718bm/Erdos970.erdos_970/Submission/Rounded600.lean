import Submission.Rounded600Data

/-! Kernel-checked finite rounded certificate; this does not settle Erdos970. -/
namespace Erdos970.Rounded600
open Finset BlockSieve BlockSieve.SievePolynomial
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000

def integerMain (m : ℕ) : ℤ :=
  ∑ a : Fin 72, if 0 ≤ termCoeff a then
    termCoeff a * (m / (∏ p ∈ termPrimes a, p) : ℕ)
  else termCoeff a * (ceilQuotient m (∏ p ∈ termPrimes a, p) : ℕ)

lemma main_cast (m : ℕ) : (integerMain m : ℝ) = certificate.roundedMain m := by
  classical
  unfold integerMain roundedMain
  rw [Int.cast_sum]
  apply sum_congr rfl
  intro a ha
  change ((if 0 ≤ termCoeff a then
    termCoeff a * (m / (∏ p ∈ termPrimes a, p) : ℕ)
    else termCoeff a * (ceilQuotient m (∏ p ∈ termPrimes a, p) : ℕ) : ℤ) : ℝ) =
    if (0 : ℝ) ≤ termCoeff a then
      (termCoeff a : ℝ) * (m / (∏ p ∈ termPrimes a, p) : ℕ)
    else (termCoeff a : ℝ) * (ceilQuotient m (∏ p ∈ termPrimes a, p) : ℕ)
  by_cases h : 0 ≤ termCoeff a
  · have hR : (0 : ℝ) ≤ termCoeff a := by exact_mod_cast h
    simp only [if_pos h, if_pos hR, Int.cast_mul, Int.cast_natCast]
  · have hR : ¬(0 : ℝ) ≤ termCoeff a := by exact_mod_cast h
    simp only [if_neg h, if_neg hR, Int.cast_mul, Int.cast_natCast]

/-- Every floor or ceiling in this assertion is an exact integer calculation. -/
lemma rounded_main : certificate.roundedMain 600 = 22 := by
  have he : integerMain 600 = 22 := by decide +kernel
  rw [← main_cast, he]
  norm_num

noncomputable def hit (r : ℕ → ℕ) (i p : ℕ) : ℝ :=
  if i ≡ r p [MOD p] then 1 else 0

lemma hit_nonneg (r : ℕ → ℕ) (i p : ℕ) : 0 ≤ hit r i p := by
  unfold hit
  split_ifs <;> norm_num

lemma hit_le_one (r : ℕ → ℕ) (i p : ℕ) : hit r i p ≤ 1 := by
  unfold hit
  split_ifs <;> norm_num

lemma and_indicator (A B : Prop) [Decidable A] [Decidable B] :
    (if A ∧ B then (1 : ℝ) else 0) =
      (if A then 1 else 0) * (if B then 1 else 0) := by
  by_cases ha : A <;> by_cases hb : B <;> simp [ha, hb]

/-- The exact 72-term polynomial has a short nested first-hit factorization. -/
lemma value_factor (r : ℕ → ℕ) (i : ℕ) :
    certificate.value r i =
      (1-hit r i 2) * (1-hit r i 3) *
        ((1-hit r i 5) * (1-hit r i 7 -
          (hit r i 11 + hit r i 13 + hit r i 17 + hit r i 19)) -
          (hit r i 23 + hit r i 29 + hit r i 31 + hit r i 37 +
            hit r i 41 + hit r i 43)) := by
  classical
  simp only [value, certificate, Fin.sum_univ_succ, Fin.sum_univ_zero,
    termPrimes, termCoeff, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Finset.forall_mem_insert, Finset.mem_singleton, forall_eq,
    Finset.notMem_empty, IsEmpty.forall_iff, forall_const,
    and_indicator, hit, ite_true, Int.cast_neg, Int.cast_one]
  ring

lemma value_le_one (r : ℕ → ℕ) (i : ℕ) : certificate.value r i ≤ 1 := by
  let A := hit r i 11 + hit r i 13 + hit r i 17 + hit r i 19
  let B := hit r i 23 + hit r i 29 + hit r i 31 + hit r i 37 +
    hit r i 41 + hit r i 43
  have hA : 0 ≤ A := by
    have := hit_nonneg r i 11; have := hit_nonneg r i 13
    have := hit_nonneg r i 17; have := hit_nonneg r i 19
    dsimp [A]; linarith
  have hB : 0 ≤ B := by
    have := hit_nonneg r i 23; have := hit_nonneg r i 29
    have := hit_nonneg r i 31; have := hit_nonneg r i 37
    have := hit_nonneg r i 41; have := hit_nonneg r i 43
    dsimp [B]; linarith
  have hn (p : ℕ) : 0 ≤ 1 - hit r i p := sub_nonneg.mpr (hit_le_one r i p)
  have hu (p : ℕ) : 1 - hit r i p ≤ 1 := by have := hit_nonneg r i p; linarith
  have h23 : (1-hit r i 2) * (1-hit r i 3) ≤ 1 :=
    mul_le_one₀ (hu 2) (hn 3) (hu 3)
  have h57 : (1-hit r i 5) * (1-hit r i 7) ≤ 1 :=
    mul_le_one₀ (hu 5) (hn 7) (hu 7)
  have h5A := mul_nonneg (hn 5) hA
  have hy : (1-hit r i 5) * (1-hit r i 7-A)-B ≤ 1 := by nlinarith
  rw [value_factor]
  exact (mul_le_mul_of_nonneg_left hy (mul_nonneg (hn 2) (hn 3))).trans
    (by simpa only [mul_one] using h23)

lemma value_nonpos_of_hit (r : ℕ → ℕ) (i : ℕ)
    (hc : ∃ p ∈ primes, i ≡ r p [MOD p]) : certificate.value r i ≤ 0 := by
  have hn := hit_nonneg r i
  have hh (p : ℕ) (hp : i ≡ r p [MOD p]) : hit r i p = 1 := by simp [hit, hp]
  have hz (p : ℕ) (hp : ¬i ≡ r p [MOD p]) : hit r i p = 0 := by simp [hit, hp]
  rw [value_factor]
  by_cases h2 : i ≡ r 2 [MOD 2]
  · rw [hh 2 h2]; simp
  rw [hz 2 h2]
  by_cases h3 : i ≡ r 3 [MOD 3]
  · rw [hh 3 h3]; simp
  rw [hz 3 h3]
  norm_num only [sub_zero, one_mul]
  by_cases h5 : i ≡ r 5 [MOD 5]
  · rw [hh 5 h5]
    norm_num only [sub_self, zero_mul, zero_sub]
    have := hn 23; have := hn 29; have := hn 31
    have := hn 37; have := hn 41; have := hn 43
    linarith
  rw [hz 5 h5]
  norm_num only [sub_zero, one_mul]
  by_cases h7 : i ≡ r 7 [MOD 7]
  · rw [hh 7 h7]
    have := hn 11; have := hn 13; have := hn 17; have := hn 19
    have := hn 23; have := hn 29; have := hn 31
    have := hn 37; have := hn 41; have := hn 43
    linarith
  rw [hz 7 h7]
  obtain ⟨p, hp, hpi⟩ := hc
  have hh1 := hh p hpi
  have := hn 11; have := hn 13; have := hn 17; have := hn 19
  have := hn 23; have := hn 29; have := hn 31
  have := hn 37; have := hn 41; have := hn 43
  simp only [primes, mem_insert, mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | contradiction | linarith

lemma value_le_survivor (r : ℕ → ℕ) (i : ℕ) :
    certificate.value r i ≤ if ∀ p ∈ primes, ¬i ≡ r p [MOD p] then 1 else 0 := by
  classical
  by_cases h : ∀ p ∈ primes, ¬i ≡ r p [MOD p]
  · rw [if_pos h]
    exact value_le_one r i
  · rw [if_neg h]
    push_neg at h
    exact value_nonpos_of_hit r i h

/-- Uniform over all residue phases of this fixed fourteen-prime set. -/
theorem at_least_twenty_two (r : ℕ → ℕ) :
    22 ≤ ((range 600).filter (fun i => ∀ p ∈ primes, ¬i ≡ r p [MOD p])).card := by
  classical
  have h := certificate.roundedMain_le_interval term_primes_prime r 600
  rw [rounded_main] at h
  have hu := sum_le_sum (s := range 600) (fun i _ => value_le_survivor r i)
  have he : (∑ i ∈ range 600,
      if ∀ p ∈ primes, ¬i ≡ r p [MOD p] then (1 : ℝ) else 0) =
      (((range 600).filter (fun i => ∀ p ∈ primes, ¬i ≡ r p [MOD p])).card : ℝ) := by
    simp
  rw [he] at hu
  exact_mod_cast h.trans hu

#print axioms rounded_main
#print axioms value_factor
#print axioms at_least_twenty_two

end Erdos970.Rounded600
