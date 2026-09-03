import Submission.CarriedRationalPrimePattern

/-!
An averaged necessary condition for rationality of the original sum.
The non-summability needed to apply the resulting criterion is not proved.
This file does not settle the conjecture in Spec.lean.
-/

namespace CarriedPrimeAverage

open Erdos68Development CongruencePreservingCarry CarriedRationalPrimePattern

/-- The prime enumeration starting at five. -/
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n+2)

lemma prime_prime (n : ℕ) : (prime n).Prime := Nat.prime_nth_prime _

lemma prime_strictMono : StrictMono prime := by
  intro i j hij
  exact Nat.nth_strictMono Nat.infinite_setOf_prime (by omega)

lemma prime_ge_five (n : ℕ) : 5 ≤ prime n := by
  have he : prime 0 = 5 := by simp [prime, Nat.nth_prime_two_eq_five]
  rw [← he]
  exact prime_strictMono.monotone (Nat.zero_le n)

lemma prime_ge_index (n : ℕ) : n+4 ≤ prime n := by
  simpa only [prime, Nat.add_assoc] using Nat.add_two_le_nth_prime (n+2)

lemma prime_gap (n k : ℕ) (hlo : prime n < k) (hhi : k < prime (n+1)) :
    ¬k.Prime := by
  intro hk
  have he : k < Nat.nth Nat.Prime ((n+2)+1) := by
    simpa only [prime, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hhi
  have hh := Nat.le_nth_of_lt_nth_succ he hk
  change k ≤ prime n at hh
  omega

lemma prime_succ_lt_twice (n : ℕ) : prime (n+1) < 2*prime n := by
  have hp := prime_prime n
  have hp5 := prime_ge_five n
  obtain ⟨r, hr, hpr, hr2⟩ := Nat.exists_prime_lt_and_le_two_mul (prime n) hp.ne_zero
  have hrlt : r < 2*prime n := by
    by_contra h
    have he : r = 2*prime n := by omega
    rw [he] at hr
    have htwo := hr.eq_two_or_odd
    omega
  have hnext : prime (n+1) ≤ r := by
    by_contra h
    exact prime_gap n r hpr (by omega) hr
  omega

lemma actualTail_lt_square (n : ℕ) (hn : 3 ≤ n) :
    actualTail n < (n : ℝ)^2 := by
  obtain ⟨r, rfl⟩ : ∃ r, n = r+3 := ⟨n-3, by omega⟩
  rw [actualTail_add_three]
  exact_mod_cast tail_lt_square r

/-- Quadratic deficit at the n-th prime, weighted by the reciprocal prime. -/
noncomputable def deficit (n : ℕ) : ℝ :=
  ((prime n : ℝ)^2-actualTail (prime n))/(prime n : ℝ)^3

lemma deficit_pos (n : ℕ) : 0 < deficit n := by
  apply div_pos
  · exact sub_pos.mpr (actualTail_lt_square _ (by have := prime_ge_five n; omega))
  · have hp : (0 : ℝ) < prime n := by exact_mod_cast (prime_prime n).pos
    positivity

lemma rational_prime_tail (q : ℚ) (hq : (∑' k : ℕ, term k) = (q : ℝ))
    (n : ℕ) (hden : q.den ≤ prime n-1) :
    actualTail (prime (n+1)) =
      (prime (n+1) : ℝ)*(2*(prime n : ℝ)-prime (n+1))-1 := by
  have he := (rational_between_primes q hq (prime n) (prime (n+1))
    (prime_prime n) (prime_prime (n+1)) (prime_ge_five n) hden
    (prime_strictMono (by omega)) (prime_succ_lt_twice n)
    (prime_gap n)).2
  have hnext := prime_strictMono (show n < n+1 by omega)
  rw [← integerTail_cast q hq (prime (n+1)) (by omega)]
  exact_mod_cast he

lemma elementary_deficit_bound (p s : ℝ) (hp : 1 ≤ p) (hgap : p+1 ≤ s) :
    (s^2-(s*(2*p-s)-1))/s^3 ≤ 3*(1/p-1/s) := by
  have hp0 : 0 < p := by linarith
  have hs0 : 0 < s := by linarith
  have hdiff : 0 ≤ s-p := by linarith
  have he : (s-p)/(p*s) = 1/p-1/s := by field_simp
  have hg : (s-p)/s^2 ≤ 1/p-1/s := by
    rw [← he]
    apply div_le_div_of_nonneg_left hdiff (by positivity)
    nlinarith
  have hpow : s^2 ≤ s^3 := by
    have hh := mul_le_mul_of_nonneg_right (show 1 ≤ s by linarith) (sq_nonneg s)
    nlinarith
  have hsmall : 1/s^3 ≤ (s-p)/s^2 := by
    calc
      _ ≤ 1/s^2 := one_div_le_one_div_of_le (by positivity) hpow
      _ ≤ _ := div_le_div_of_nonneg_right (by linarith) (by positivity)
  have hid : (s^2-(s*(2*p-s)-1))/s^3 = 2*((s-p)/s^2)+1/s^3 := by
    field_simp
    ring
  rw [hid]
  linarith

lemma rational_deficit_succ_bound (q : ℚ)
    (hq : (∑' k : ℕ, term k) = (q : ℝ)) (n : ℕ)
    (hden : q.den ≤ prime n-1) :
    deficit (n+1) ≤ 3*(1/(prime n : ℝ)-1/(prime (n+1) : ℝ)) := by
  rw [deficit, rational_prime_tail q hq n hden]
  apply elementary_deficit_bound
  · exact_mod_cast (show 1 ≤ prime n by have := prime_ge_five n; omega)
  · exact_mod_cast (show prime n+1 ≤ prime (n+1) by
      have := prime_strictMono (show n < n+1 by omega)
      omega)

/-- Every finite block after a sufficiently late prime has this telescoping
bound under rationality. The original sum is the one in `hq`. -/
theorem rational_block_bound (q : ℚ)
    (hq : (∑' k : ℕ, term k) = (q : ℝ)) (N k : ℕ)
    (hden : q.den ≤ prime N-1) :
    (∑ i ∈ Finset.range k, deficit (N+1+i)) ≤
      3*(1/(prime N : ℝ)-1/(prime (N+k) : ℝ)) := by
  have hle : (∑ i ∈ Finset.range k, deficit (N+1+i)) ≤
      ∑ i ∈ Finset.range k,
        3*(1/(prime (N+i) : ℝ)-1/(prime (N+i+1) : ℝ)) := by
    apply Finset.sum_le_sum
    intro i _
    have hm := prime_strictMono.monotone (show N ≤ N+i by omega)
    have he := rational_deficit_succ_bound q hq (N+i) (by omega)
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using he
  refine hle.trans_eq ?_
  rw [← Finset.mul_sum]
  have he := Finset.sum_range_sub' (fun i => 1/(prime (N+i) : ℝ)) k
  simpa only [Nat.add_zero, Nat.add_assoc] using congrArg (fun x : ℝ => 3*x) he

lemma rational_block_bound_simple (q : ℚ)
    (hq : (∑' k : ℕ, term k) = (q : ℝ)) (N k : ℕ)
    (hden : q.den ≤ prime N-1) :
    (∑ i ∈ Finset.range k, deficit (N+1+i)) ≤ 3/(prime N : ℝ) := by
  apply (rational_block_bound q hq N k hden).trans
  have hp : (0 : ℝ) ≤ 1/(prime (N+k) : ℝ) := by positivity
  rw [show 3/(prime N : ℝ) = 3*(1/(prime N : ℝ)) by ring]
  linarith

/-- Rationality forces summability of the positive weighted deficits. -/
theorem rational_summable_deficit (q : ℚ)
    (hq : (∑' k : ℕ, term k) = (q : ℝ)) : Summable deficit := by
  apply (summable_nat_add_iff (q.den+1)).mp
  apply summable_of_sum_range_le (c := 3/(prime q.den : ℝ))
    (fun n => (deficit_pos _).le)
  intro k
  have he := rational_block_bound_simple q hq q.den k (by
    have := prime_ge_index q.den
    omega)
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using he

/-- The entire deficit tail has the same explicit bound. -/
theorem rational_tsum_bound (q : ℚ)
    (hq : (∑' k : ℕ, term k) = (q : ℝ)) (N : ℕ)
    (hden : q.den ≤ prime N-1) :
    (∑' i : ℕ, deficit (N+1+i)) ≤ 3/(prime N : ℝ) := by
  have hs : Summable (fun i => deficit (N+1+i)) := by
    simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      (summable_nat_add_iff (N+1)).mpr (rational_summable_deficit q hq)
  exact hs.tsum_le_of_sum_range_le (fun k => rational_block_bound_simple q hq N k hden)

/-- A sufficient condition only: non-summability for the actual deficits
has not been established. -/
theorem irrational_of_not_summable_deficit (h : ¬Summable deficit) :
    Irrational (∑' k : ℕ, term k) := by
  rintro ⟨q, hq⟩
  exact h (rational_summable_deficit q hq.symm)

/-- Arbitrarily late finite violations would suffice, without needing a
uniform pointwise prime-tail estimate. No such violations are proved. -/
theorem irrational_of_frequent_block_violations
    (h : ∀ M : ℕ, ∃ N ≥ M, ∃ k : ℕ,
      3/(prime N : ℝ) < ∑ i ∈ Finset.range k, deficit (N+1+i)) :
    Irrational (∑' k : ℕ, term k) := by
  rintro ⟨q, hq⟩
  obtain ⟨N, hN, k, hk⟩ := h q.den
  have hden : q.den ≤ prime N-1 := by have := prime_ge_index N; omega
  exact (not_lt_of_ge (rational_block_bound_simple q hq.symm N k hden)) hk

#print axioms rational_summable_deficit
#print axioms rational_tsum_bound
#print axioms irrational_of_not_summable_deficit
#print axioms irrational_of_frequent_block_violations

end CarriedPrimeAverage
