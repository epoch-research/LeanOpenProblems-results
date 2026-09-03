import Submission.RoughMobiusHarmonic

/-! An elementary second-moment upper bound for integers avoiding a finite
set of primes. It will be used only to control discarded cofactor ranges. -/

namespace Erdos371

noncomputable def primeReciprocalSum (S : Finset ℕ) : ℝ := ∑ p ∈ S, (1 : ℝ) / p

noncomputable def primeDivCount (S : Finset ℕ) (n : ℕ) : ℝ :=
  ∑ p ∈ S, if p ∣ n then 1 else 0

def primeAvoidCount (S : Finset ℕ) (N : ℕ) : ℕ :=
  ((Finset.range N).filter fun n => ∀ p ∈ S, ¬p ∣ n + 1).card

lemma primeReciprocalSum_nonneg (S : Finset ℕ) : 0 ≤ primeReciprocalSum S :=
  Finset.sum_nonneg fun _ _ => by positivity

lemma primeDivCount_sum (S : Finset ℕ) (N : ℕ) :
    (∑ n ∈ Finset.range N, primeDivCount S (n + 1)) = ∑ p ∈ S, ((N / p : ℕ) : ℝ) := by
  unfold primeDivCount
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  simp [Nat.card_multiples]

lemma primeDivCount_sum_lower (S : Finset ℕ) (N : ℕ) (hS : ∀ p ∈ S, p.Prime) :
    (N : ℝ) * primeReciprocalSum S - S.card ≤
      ∑ n ∈ Finset.range N, primeDivCount S (n + 1) := by
  rw [primeDivCount_sum, primeReciprocalSum, Finset.mul_sum]
  have ht : ∀ p ∈ S, (N : ℝ) * (1 / p) - 1 ≤ ((N / p : ℕ) : ℝ) := by
    intro p hp
    have h := nat_div_rounding_error_norm_le_one N p (hS p hp).pos
    rw [Real.norm_eq_abs] at h
    have h' := (le_abs_self ((N : ℝ) / p - ((N / p : ℕ) : ℝ))).trans h
    simp only [mul_one_div]
    linarith
  have h := Finset.sum_le_sum ht
  simpa only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one] using h

lemma prime_divisor_pair_sum_le (p q N : ℕ) (hp : p.Prime) (hq : q.Prime) :
    (∑ n ∈ Finset.range N,
      (if p ∣ n + 1 then (1 : ℝ) else 0) * (if q ∣ n + 1 then (1 : ℝ) else 0)) ≤
      N * (1 / (p : ℝ)) * (1 / (q : ℝ)) + if p = q then (N : ℝ) / p else 0 := by
  by_cases he : p = q
  · subst q
    have heq (n : ℕ) :
        (if p ∣ n + 1 then (1 : ℝ) else 0) * (if p ∣ n + 1 then 1 else 0) =
          if p ∣ n + 1 then 1 else 0 := by split_ifs <;> norm_num
    simp only [heq, if_true]
    have hs : (∑ n ∈ Finset.range N, if p ∣ n + 1 then (1 : ℝ) else 0) = (N / p : ℕ) := by
      simp [Nat.card_multiples]
    rw [hs]
    exact (Nat.cast_div_le (m := N) (n := p) (α := ℝ)).trans (le_add_of_nonneg_left (by positivity))
  · have hc : p.Coprime q := (Nat.coprime_primes hp hq).mpr he
    have heq (n : ℕ) :
        (if p ∣ n + 1 then (1 : ℝ) else 0) * (if q ∣ n + 1 then 1 else 0) =
          if p * q ∣ n + 1 then 1 else 0 := by
      have hd : p * q ∣ n + 1 ↔ p ∣ n + 1 ∧ q ∣ n + 1 :=
        ⟨fun h => ⟨dvd_trans (Nat.dvd_mul_right p q) h, dvd_trans (Nat.dvd_mul_left q p) h⟩,
          fun h => hc.mul_dvd_of_dvd_of_dvd h.1 h.2⟩
      by_cases hpn : p ∣ n + 1 <;> by_cases hqn : q ∣ n + 1 <;> simp [hpn, hqn, hd]
    simp only [heq, if_neg he, add_zero]
    have hs : (∑ n ∈ Finset.range N, if p * q ∣ n + 1 then (1 : ℝ) else 0) = (N / (p * q) : ℕ) := by
      simp [Nat.card_multiples]
    rw [hs]
    convert Nat.cast_div_le (m := N) (n := p * q) (α := ℝ) using 1 <;> push_cast <;> ring

lemma primeDivCount_sum_sq_upper (S : Finset ℕ) (N : ℕ) (hS : ∀ p ∈ S, p.Prime) :
    (∑ n ∈ Finset.range N, (primeDivCount S (n + 1))^2) ≤
      N * (primeReciprocalSum S)^2 + N * primeReciprocalSum S := by
  calc
    _ = ∑ p ∈ S, ∑ q ∈ S, ∑ n ∈ Finset.range N,
        (if p ∣ n + 1 then (1 : ℝ) else 0) * (if q ∣ n + 1 then (1 : ℝ) else 0) := by
      simp only [primeDivCount, pow_two, Finset.sum_mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun p _ => Finset.sum_comm
    _ ≤ ∑ p ∈ S, ∑ q ∈ S,
        ((N : ℝ) * (1 / p) * (1 / q) + if p = q then (N : ℝ) / p else 0) := by
      exact Finset.sum_le_sum fun p hp => Finset.sum_le_sum fun q hq =>
        prime_divisor_pair_sum_le p q N (hS p hp) (hS q hq)
    _ = _ := by
      simp_rw [Finset.sum_add_distrib]
      congr 1
      · simp only [← Finset.mul_sum, ← Finset.sum_mul, primeReciprocalSum]
        ring
      · have he (p : ℕ) (hp : p ∈ S) :
            (∑ q ∈ S, if p = q then (N : ℝ) / p else 0) = N * (1 / p) := by
          simp [hp, div_eq_mul_inv]
        rw [Finset.sum_congr rfl he, ← Finset.mul_sum]
        rfl

lemma primeDivCount_variance_upper (S : Finset ℕ) (N : ℕ) (hS : ∀ p ∈ S, p.Prime) :
    (∑ n ∈ Finset.range N, (primeDivCount S (n + 1) - primeReciprocalSum S)^2) ≤
      N * primeReciprocalSum S + 2 * primeReciprocalSum S * S.card := by
  have h1 := primeDivCount_sum_lower S N hS
  have h2 := primeDivCount_sum_sq_upper S N hS
  have h0 := primeReciprocalSum_nonneg S
  have he : (∑ n ∈ Finset.range N, (primeDivCount S (n + 1) - primeReciprocalSum S)^2) =
      (∑ n ∈ Finset.range N, (primeDivCount S (n + 1))^2) -
        2 * primeReciprocalSum S * (∑ n ∈ Finset.range N, primeDivCount S (n + 1)) +
        N * (primeReciprocalSum S)^2 := by
    simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  rw [he]
  nlinarith [mul_le_mul_of_nonneg_left h1 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) h0)]

/-- A second-moment sieve. The error requires only the number of sieving
primes, since the second moment is bounded from above by dropping floor errors. -/
theorem primeAvoidCount_mul_reciprocal_le (S : Finset ℕ) (N : ℕ)
    (hS : ∀ p ∈ S, p.Prime) (hH : 0 < primeReciprocalSum S) :
    (primeAvoidCount S N : ℝ) * primeReciprocalSum S ≤ N + 2 * S.card := by
  have he : (primeAvoidCount S N : ℝ) * (primeReciprocalSum S)^2 ≤
      ∑ n ∈ Finset.range N, (primeDivCount S (n + 1) - primeReciprocalSum S)^2 := by
    calc
      _ = ∑ n ∈ Finset.range N, if ∀ p ∈ S, ¬p ∣ n + 1 then (primeReciprocalSum S)^2 else 0 := by
        simp [← Finset.sum_filter, primeAvoidCount]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro n hn
        split_ifs with h
        · have hz : primeDivCount S (n + 1) = 0 := by
            exact Finset.sum_eq_zero fun p hp => if_neg (h p hp)
          simp [hz]
        · exact sq_nonneg _
  have ht := he.trans (primeDivCount_variance_upper S N hS)
  apply (mul_le_mul_iff_right₀ hH).mp
  nlinarith

/-- A convenient normalized form when all the sieving primes are at most
the averaging endpoint. -/
theorem primeAvoidCount_ratio_le (S : Finset ℕ) (N : ℕ)
    (hS : ∀ p ∈ S, p.Prime) (hcard : S.card ≤ N + 1) (hN : 0 < N)
    (hH : 0 < primeReciprocalSum S) :
    (primeAvoidCount S N : ℝ) / N ≤ 5 / primeReciprocalSum S := by
  have h := primeAvoidCount_mul_reciprocal_le S N hS hH
  have hcardR : (S.card : ℝ) ≤ N + 1 := by exact_mod_cast hcard
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  apply (le_div_iff₀ hH).mpr
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (show (0 : ℝ) < N by exact_mod_cast hN)).mpr
  nlinarith

#print axioms primeDivCount_variance_upper
#print axioms primeAvoidCount_mul_reciprocal_le
#print axioms primeAvoidCount_ratio_le
end Erdos371
