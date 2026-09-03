import Submission.Elementary

/-!
# A finite prime-square sieve

For every fixed natural number `A`, eventually in the interval length `H`,
uniformly in the starting point `x`, at most `13 * H / 16` members of `(x, x + H]`
are divisible by the square of a prime at most `A * H`.

The finite union bound is `3 * H / 4 + Nat.primeCounting B` for cutoff `B`.
Chebyshev's upper bound and logarithmic growth show that
`Nat.primeCounting (A * H) / H` tends to zero, including the case `A = 0`.

This is only a finite preliminary sieve: it does not control squares of primes
larger than `A * H`, and it does not prove a squarefree-gap conjecture.
-/

open Finset Filter
open scoped Topology

namespace PrimeSieve

/-- Members of `(x, x + H]` divisible by the square of a prime at most `B`. -/
noncomputable def primeSquareBad (x H B : ℕ) : Finset ℕ := by
  classical
  exact (Ioc x (x + H)).filter (fun n => ∃ p : ℕ, p.Prime ∧ p ≤ B ∧ p ^ 2 ∣ n)

@[simp]
theorem mem_primeSquareBad (x H B n : ℕ) :
    n ∈ primeSquareBad x H B ↔
      x < n ∧ n ≤ x + H ∧ ∃ p : ℕ, p.Prime ∧ p ≤ B ∧ p ^ 2 ∣ n := by
  classical
  simp only [primeSquareBad, mem_filter, mem_Ioc, and_assoc]

@[simp]
theorem primeSquareBad_zero_length (x B : ℕ) : primeSquareBad x 0 B = ∅ := by
  classical
  simp [primeSquareBad]

@[simp]
theorem primeSquareBad_zero_cutoff (x H : ℕ) : primeSquareBad x H 0 = ∅ := by
  classical
  simp [primeSquareBad]

/-- The union over the finitely many primes up to `B` is exactly the bad set. -/
theorem primeSquareBad_eq_biUnion (x H B : ℕ) :
    primeSquareBad x H B = (B + 1).primesBelow.biUnion
      (fun p => (Ioc x (x + H)).filter (fun n => p ^ 2 ∣ n)) := by
  classical
  ext n
  simp only [primeSquareBad, mem_filter, mem_biUnion, Nat.mem_primesBelow]
  constructor
  · rintro ⟨hn, p, hp, hpB, hpn⟩
    exact ⟨p, ⟨by omega, hp⟩, hn, hpn⟩
  · rintro ⟨p, ⟨hpB, hp⟩, hn, hpn⟩
    exact ⟨hn, p, hp, by omega, hpn⟩

/-- The prime sum is bounded by the elementary sum over all integers from `2` to `B`. -/
theorem sum_prime_reciprocal_sq_le (B : ℕ) :
    (∑ p ∈ (B + 1).primesBelow, (1 : ℚ) / (p : ℚ) ^ 2) ≤ 3 / 4 := by
  apply le_trans (sum_le_sum_of_subset_of_nonneg (t := Icc 2 B) ?_ ?_)
    (ElementarySquarefree.sum_reciprocal_sq_le B)
  · intro p hp
    obtain ⟨hpB, hp⟩ := Nat.mem_primesBelow.mp hp
    exact mem_Icc.mpr ⟨hp.two_le, by omega⟩
  · intro p _ _
    positivity

/-- The finite union bound, valid for every cutoff and including zero lengths. -/
theorem card_primeSquareBad_le (x H B : ℕ) :
    ((primeSquareBad x H B).card : ℚ) ≤
      (3 / 4 : ℚ) * (H : ℚ) + Nat.primeCounting B := by
  have h_each (p : ℕ) :
      (((Ioc x (x + H)).filter (fun n => p ^ 2 ∣ n)).card : ℚ) ≤
        (H : ℚ) * (1 / (p : ℚ) ^ 2) + 1 := by
    have hc := ElementarySquarefree.card_multiples_Ioc_le x H (p ^ 2)
    have hcQ :
        (((Ioc x (x + H)).filter (fun n => p ^ 2 ∣ n)).card : ℚ) ≤
          ((H / p ^ 2 : ℕ) : ℚ) + 1 := by exact_mod_cast hc
    have hd : ((H / p ^ 2 : ℕ) : ℚ) ≤ (H : ℚ) / (p : ℚ) ^ 2 := by
      simpa only [Nat.cast_pow] using
        (Nat.cast_div_le (α := ℚ) (m := H) (n := p ^ 2))
    calc
      _ ≤ ((H / p ^ 2 : ℕ) : ℚ) + 1 := hcQ
      _ ≤ (H : ℚ) / (p : ℚ) ^ 2 + 1 := by linarith
      _ = _ := by ring
  have hcard : ((primeSquareBad x H B).card : ℚ) ≤
      ∑ p ∈ (B + 1).primesBelow,
        (((Ioc x (x + H)).filter (fun n => p ^ 2 ∣ n)).card : ℚ) := by
    rw [primeSquareBad_eq_biUnion]
    exact_mod_cast (card_biUnion_le (s := (B + 1).primesBelow)
      (t := fun p => (Ioc x (x + H)).filter (fun n => p ^ 2 ∣ n)))
  have hsum := sum_le_sum (s := (B + 1).primesBelow) (fun p _ => h_each p)
  have hsum_eq :
      (∑ p ∈ (B + 1).primesBelow, ((H : ℚ) * (1 / (p : ℚ) ^ 2) + 1)) =
        (H : ℚ) * (∑ p ∈ (B + 1).primesBelow, (1 : ℚ) / (p : ℚ) ^ 2) +
          (Nat.primeCounting B : ℚ) := by
    rw [sum_add_distrib, ← mul_sum]
    simp [Nat.primesBelow_card_eq_primeCounting', Nat.primeCounting]
  rw [hsum_eq] at hsum
  have hs := mul_le_mul_of_nonneg_left (sum_prime_reciprocal_sq_le B)
    (show (0 : ℚ) ≤ H by positivity)
  linarith

/-- For each fixed natural `A`, the number of primes up to `A * H` is `o(H)`. -/
theorem tendsto_primeCounting_mul_div (A : ℕ) :
    Tendsto (fun H : ℕ => (Nat.primeCounting (A * H) : ℝ) / (H : ℝ))
      atTop (𝓝 0) := by
  by_cases hA : A = 0
  · subst A
    simp
  have hApos : (0 : ℝ) < A := by exact_mod_cast Nat.pos_of_ne_zero hA
  have ht : Tendsto (fun H : ℕ => ((A * H : ℕ) : ℝ)) atTop atTop := by
    simp only [Nat.cast_mul]
    exact Tendsto.const_mul_atTop hApos tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun H : ℕ => Real.log ((A * H : ℕ) : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp ht
  have hlim : Tendsto
      (fun H : ℕ => (Real.log 4 + 1) * (A : ℝ) / Real.log ((A * H : ℕ) : ℝ))
      atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      hlog.inv_tendsto_atTop.const_mul ((Real.log 4 + 1) * (A : ℝ))
  apply squeeze_zero' (Eventually.of_forall fun H => by positivity) ?_ hlim
  filter_upwards [ht.eventually (Chebyshev.eventually_primeCounting_le (ε := 1) (by norm_num)),
    eventually_gt_atTop (0 : ℕ)] with H hπ hH
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  simp only [Nat.floor_natCast] at hπ
  calc
    _ ≤ ((Real.log 4 + 1) * ((A * H : ℕ) : ℝ) /
        Real.log ((A * H : ℕ) : ℝ)) / (H : ℝ) :=
      div_le_div_of_nonneg_right hπ (le_of_lt hHR)
    _ = _ := by
      simp only [Nat.cast_mul]
      rw [← mul_assoc, div_right_comm, mul_div_cancel_right₀ _ (ne_of_gt hHR)]

/-- An eventual linear prime-counting bound with any positive real coefficient. -/
theorem eventually_primeCounting_mul_le (A : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ H : ℕ in atTop, (Nat.primeCounting (A * H) : ℝ) ≤ ε * (H : ℝ) := by
  filter_upwards [(tendsto_primeCounting_mul_div A).eventually_le_const hε,
    eventually_gt_atTop (0 : ℕ)] with H hπ hH
  exact (div_le_iff₀ (by exact_mod_cast hH : (0 : ℝ) < H)).mp hπ

/-- The prime-counting error is eventually at most one sixteenth of the length. -/
theorem eventually_sixteen_mul_primeCounting_le (A : ℕ) :
    ∀ᶠ H : ℕ in atTop, 16 * Nat.primeCounting (A * H) ≤ H := by
  filter_upwards [eventually_primeCounting_mul_le A (ε := 1 / 16) (by norm_num)] with H hH
  have h : (16 : ℝ) * Nat.primeCounting (A * H) ≤ H := by linarith
  exact_mod_cast h

/-- For fixed `A`, the sieve bound holds eventually in `H`, uniformly for every `x`.
The statement also covers `A = 0`. -/
theorem eventually_card_primeSquareBad_le (A : ℕ) :
    ∀ᶠ H : ℕ in atTop, ∀ x : ℕ,
      16 * (primeSquareBad x H (A * H)).card ≤ 13 * H := by
  filter_upwards [eventually_sixteen_mul_primeCounting_le A] with H hH
  intro x
  have hπ : (16 : ℚ) * Nat.primeCounting (A * H) ≤ H := by exact_mod_cast hH
  have hc := card_primeSquareBad_le x H (A * H)
  have hb : (16 : ℚ) * (primeSquareBad x H (A * H)).card ≤ 13 * (H : ℚ) := by
    linarith
  exact_mod_cast hb

/-- The rational-valued version of the eventual, uniform sieve estimate. -/
theorem eventually_card_primeSquareBad_le_rat (A : ℕ) :
    ∀ᶠ H : ℕ in atTop, ∀ x : ℕ,
      ((primeSquareBad x H (A * H)).card : ℚ) ≤ (13 / 16 : ℚ) * (H : ℚ) := by
  filter_upwards [eventually_card_primeSquareBad_le A] with H hH
  intro x
  have h : (16 : ℚ) * (primeSquareBad x H (A * H)).card ≤ 13 * (H : ℚ) := by
    exact_mod_cast hH x
  linarith

/-- An explicit quantifier formulation: the threshold depends on `A`, not on `x`. -/
theorem exists_uniform_threshold (A : ℕ) :
    ∃ H₀ : ℕ, ∀ H ≥ H₀, ∀ x : ℕ,
      16 * (primeSquareBad x H (A * H)).card ≤ 13 * H :=
  eventually_atTop.mp (eventually_card_primeSquareBad_le A)

open scoped Classical in
/-- The finite preliminary sieve, with the filtered set written out explicitly. -/
theorem eventually_card_prime_square_divisors_le (A : ℕ) :
    ∀ᶠ H : ℕ in atTop, ∀ x : ℕ,
      16 * ((Ioc x (x + H)).filter
        (fun n => ∃ p : ℕ, p.Prime ∧ p ≤ A * H ∧ p ^ 2 ∣ n)).card ≤ 13 * H := by
  simpa only [primeSquareBad] using eventually_card_primeSquareBad_le A

end PrimeSieve
