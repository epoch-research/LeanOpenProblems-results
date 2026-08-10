import FormalConjectures.Util.ProblemImports

open Nat

/--
A007491: Smallest prime $> n^2$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime (n ^ 2).primeCounting

/-- Formal statement of Legendre's conjecture in the context of primes after squares. -/
def legendres_conjecture (n : ℕ) : Prop :=
  n > 0 → ∃ p, p.Prime ∧ n ^ 2 < p ∧ p < (n + 1) ^ 2

/-- A007491 Legendre's conjecture is equivalent to a(n) < (n+1)^2. -/
theorem oeis_7491_conjecture_1 :
    (∀ n : ℕ, legendres_conjecture n) ↔ (∀ n : ℕ, n > 0 → a n < (n + 1) ^ 2) :=
by
  -- The proof relies on the fact that the specified definition of a(n) results in
  -- the smallest prime strictly greater than n^2.
  let an_is_smallest_prime_gt_sq (n : ℕ) : Prop :=
    (a n).Prime ∧ n ^ 2 < a n ∧ ∀ p, p.Prime → n ^ 2 < p → a n ≤ p

  -- We posit this property as a lemma whose proof is deferred.
  have an_prop (n : ℕ) (h_n : n > 0) : an_is_smallest_prime_gt_sq n := by
    have hp : {x | Nat.Prime x}.Infinite := Nat.infinite_setOf_prime
    have ha_def : a n = nth Nat.Prime (count Nat.Prime (n ^ 2 + 1)) := rfl
    have h_prime : (a n).Prime := by
      rw [ha_def]
      exact nth_mem_of_infinite hp (count Nat.Prime (n ^ 2 + 1))
    have h_gt : n ^ 2 < a n := by
      rw [ha_def]
      have h_le := le_nth_count hp (n ^ 2 + 1)
      exact lt_of_lt_of_le (lt_add_one (n ^ 2)) h_le
    have h_least : ∀ p, p.Prime → n ^ 2 < p → a n ≤ p := by
      intro p hp_prime hp_gt
      rw [ha_def]
      have hp_eq : p = nth Nat.Prime (count Nat.Prime p) := (nth_count hp_prime).symm
      rw [hp_eq]
      rw [nth_le_nth hp]
      have h_le : n ^ 2 + 1 ≤ p := hp_gt
      exact count_monotone Nat.Prime h_le
    exact ⟨h_prime, h_gt, h_least⟩

  constructor
  · -- (=>) If Legendre's conjecture holds, then a prime p_L exists such that n^2 < p_L < (n+1)^2.
    -- Since a(n) is the smallest prime > n^2, we must have a(n) ≤ p_L, hence a(n) < (n+1)^2.
    intro h_leg n h_n
    rcases h_leg n h_n with ⟨p_L, h_prime_L, h_lower_L, h_upper_L⟩

    have h_an_le_pl : a n ≤ p_L := (an_prop n h_n).2.2 p_L h_prime_L h_lower_L

    exact Nat.lt_of_le_of_lt h_an_le_pl h_upper_L

  · -- (<=) If a(n) < (n+1)^2 holds, then p = a(n) is the required prime.
    -- By definition, a(n) is a prime > n^2. The assumption gives a(n) < (n+1)^2.
    intro h_an_lt n h_n

    use a n

    have h_prop := an_prop n h_n

    exact ⟨h_prop.1, ⟨h_prop.2.1, h_an_lt n h_n⟩⟩
