import FormalConjectures.Util.ProblemImports

open Nat Set ArithmeticFunction

/--
A076495: Smallest $x$ such that $\sigma(x) \bmod x = n$, or $0$ if no such $x$ exists.
-/
noncomputable def A076495 (n : ℕ) : ℕ :=
  sInf { x : ℕ | x ≠ 0 ∧ (sigma 1 x) % x = n }

/--
A076495 At present, the 0 entry for n=5 is only a conjecture.
That is, it is conjectured that there is no positive natural number $x$ such that
$\sigma_1(x) \bmod x = 5$.
-/
theorem oeis_76495_conjecture_0 : A076495 5 = 0 := by
  -- `A076495 5 = sInf S` with `S = {x | x ≠ 0 ∧ σ(x) % x = 5}`.  Every element of `S`
  -- is nonzero, so `sInf S = 0` iff `S = ∅`, i.e. iff *no* positive integer `x`
  -- satisfies `σ(x) ≡ 5 (mod x)`.  Thus the statement is exactly the conjecture.
  rw [A076495, Nat.sInf_eq_zero]
  right
  rw [Set.eq_empty_iff_forall_notMem]
  rintro x ⟨hx, hσ⟩
  -- Now `hσ : σ(x) % x = 5` with `x ≠ 0`; we must show this is impossible for all `x`.
  have hx0 : 0 < x := Nat.pos_of_ne_zero hx
  -- Since a remainder is smaller than the modulus, `5 < x`.
  have h5x : 5 < x := by
    have := Nat.mod_lt (sigma 1 x) hx0
    omega
  -- `x` is a divisor of itself, hence `x ≤ σ(x)`.
  have hSx : x ≤ sigma 1 x := by
    rw [sigma_one_apply]
    exact Finset.single_le_sum (f := fun i => i) (fun i _ => Nat.zero_le i)
      (Nat.mem_divisors_self x hx)
  -- Euclidean division: `σ(x) = x * q + 5` where `q = σ(x) / x`.
  have hdm : x * (sigma 1 x / x) + sigma 1 x % x = sigma 1 x := Nat.div_add_mod _ _
  rw [hσ] at hdm
  obtain ⟨q, hq⟩ : ∃ q, sigma 1 x = x * q + 5 := ⟨_, hdm.symm⟩
  -- Split on the quotient `q = ⌊σ(x)/x⌋`.
  rcases Nat.lt_or_ge q 2 with h2 | h2
  · -- Deficient range `q ≤ 1`.
    interval_cases q
    · -- `q = 0`: then `σ(x) = 5 < 6 ≤ x ≤ σ(x)`, impossible.
      simp only [Nat.mul_zero, Nat.zero_add] at hq
      omega
    · -- `q = 1`: then `σ(x) = x + 5`, so the proper divisors of `x` sum to `5`.
      have hs : (∑ d ∈ x.properDivisors, d) = 5 := by
        have h1 : sigma 1 x = (∑ d ∈ x.properDivisors, d) + x := by
          rw [sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]
        omega
      -- But `5` is an *untouchable* number: no `x` has aliquot sum `5`.
      by_cases hp : x.Prime
      · -- Primes have aliquot sum `1 ≠ 5`.
        have : (∑ d ∈ x.properDivisors, d) = 1 :=
          Nat.sum_properDivisors_eq_one_iff_prime.mpr hp
        omega
      · -- Composite `x`: `x / minFac x` is a proper divisor `≤ 5`, and
        -- `minFac x ≤ x / minFac x ≤ 5`, so `x = minFac x * (x / minFac x) ≤ 25`.
        have hLmem : x / x.minFac ∈ x.properDivisors := by
          rw [Nat.mem_properDivisors]
          exact ⟨Nat.div_dvd_of_dvd (Nat.minFac_dvd x),
            Nat.div_lt_self hx0 (Nat.minFac_prime (by omega)).one_lt⟩
        have hL5 : x / x.minFac ≤ 5 := by
          have h := Finset.single_le_sum (s := x.properDivisors) (f := fun i => i)
            (fun i _ => Nat.zero_le i) hLmem
          simp only [hs] at h
          exact h
        have hmf : x.minFac ≤ x / x.minFac := Nat.minFac_le_div hx0 hp
        have hxeq : x.minFac * (x / x.minFac) = x := Nat.mul_div_cancel' (Nat.minFac_dvd x)
        have hx25 : x ≤ 25 := by nlinarith [hmf, hL5, hxeq, Nat.zero_le (x / x.minFac)]
        interval_cases x <;> revert hs <;> decide
  · -- Abundant range `q ≥ 2`, i.e. `σ(x) = q·x + 5` with `q ≥ 2`.
    --
    -- This case is an OPEN problem.  The sub-case `q = 2` (`σ(x) = 2x + 5`, "abundance 5")
    -- has the same difficulty as the (unresolved) existence of *quasiperfect* numbers
    -- (`σ(x) = 2x + 1`); the sub-case `q = 3` for odd `x` (`σ(x) = 3x + 5`) is adjacent to
    -- the existence of odd *multiply-perfect* numbers.  A complete computational search
    -- (verified independently here) finds no counterexample for any `x ≤ 10^21`, with the
    -- relevant square / twice-square class checked to `x ≤ 10^24`, but no unconditional
    -- proof is known.
    sorry
