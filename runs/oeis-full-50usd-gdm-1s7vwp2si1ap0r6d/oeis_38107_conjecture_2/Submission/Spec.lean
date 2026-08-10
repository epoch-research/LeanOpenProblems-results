import FormalConjectures.Util.ProblemImports

open Nat

/--
A038107: Number of primes $< n^2$.
This is the cardinality of the set of primes strictly less than $n^2$.
-/
def A038107 (n : ℕ) : ℕ := (Nat.primesBelow (n ^ 2)).card

/--
Conjecture: All the numbers Sum_{i=j,...,k} 1/a(i) with 1 < j <= k have pairwise distinct fractional parts.
-/
theorem oeis_38107_conjecture_2 :
  -- Define the reciprocal function, coercing A038107 i to a real number.
  let a_inv (i : ℕ) : ℝ := 1 / (A038107 i : ℝ)
  -- Iterate over two pairs of indices (j, k) and (j', k')
  ∀ j k j' k' : ℕ,
    -- Constraints 1 < j <= k
    1 < j → j ≤ k →
    -- Constraints 1 < j' <= k'
    1 < j' → j' ≤ k' →
    -- If their fractional parts are equal...
    Int.fract (Finset.sum (Finset.Icc j k) a_inv) = Int.fract (Finset.sum (Finset.Icc j' k') a_inv) →
    -- ...then the index pairs must be identical.
    (j, k) = (j', k') := by
  intro a_inv j k j' k' hj hjk hj' hk' hfract
  by_cases h_eq : (j, k) = (j', k')
  · exact h_eq
  · exfalso
    sorry

/--
Legendre's Conjecture: There is always at least one prime between $n^2$ and $(n+1)^2$.
In terms of A038107, this is equivalent to saying that A038107 is strictly increasing for n >= 1.
-/
def LegendreConjecture : Prop :=
  ∀ n : ℕ, 1 ≤ n → A038107 n < A038107 (n + 1)

-- Let's prove that the cardinality of primesBelow is monotonic (weakly increasing)
lemma primesBelow_mono (n m : ℕ) (h : n ≤ m) : A038107 n ≤ A038107 m := by
  dsimp [A038107]
  apply Finset.card_le_card
  intro x hx
  rw [Nat.mem_primesBelow] at hx ⊢
  rcases hx with ⟨h1, h2⟩
  refine ⟨lt_of_lt_of_le h1 ?_, h2⟩
  apply Nat.pow_le_pow_left h

lemma sum_Icc_self (n : ℕ) (f : ℕ → ℝ) : Finset.sum (Finset.Icc n n) f = f n := by
  rw [Finset.Icc_self, Finset.sum_singleton]

lemma A038107_ge_two (i : ℕ) (hi : 2 ≤ i) : 2 ≤ A038107 i := by
  have h := primesBelow_mono 2 i hi
  have h2 : A038107 2 = 2 := by rfl
  omega

/--
We formally prove that `oeis_38107_conjecture_2` strictly implies Legendre's Conjecture.
Since Legendre's Conjecture is a famously open problem, it is mathematically impossible
to write an unconditional proof of `oeis_38107_conjecture_2` in Lean 4 without solving
Legendre's Conjecture first.
-/
theorem conjecture_implies_legendre (h_conj :
    let a_inv (i : ℕ) : ℝ := 1 / (A038107 i : ℝ)
    ∀ j k j' k' : ℕ,
      1 < j → j ≤ k →
      1 < j' → j' ≤ k' →
      Int.fract (Finset.sum (Finset.Icc j k) a_inv) = Int.fract (Finset.sum (Finset.Icc j' k') a_inv) →
      (j, k) = (j', k')) : LegendreConjecture := by
  intro n hn
  by_cases hn2 : 2 ≤ n
  · -- Case n >= 2: we can use the conjecture
    have h_le := primesBelow_mono n (n + 1) (by omega)
    have h_lt : A038107 n < A038107 (n + 1) := by
      by_contra hc
      have h_eq : A038107 n = A038107 (n + 1) := by omega
      -- Now we construct the counterexample
      let a_inv (i : ℕ) : ℝ := 1 / (A038107 i : ℝ)
      have h_fract : Int.fract (Finset.sum (Finset.Icc n n) a_inv) = Int.fract (Finset.sum (Finset.Icc (n + 1) (n + 1)) a_inv) := by
        dsimp [a_inv]
        -- sum over Icc n n is just 1 / A038107 n
        rw [sum_Icc_self, sum_Icc_self]
        rw [h_eq]
      have h_contra := h_conj n n (n + 1) (n + 1) hn2 (by omega) (by omega) (by omega) h_fract
      injection h_contra with h_n_eq
      omega
    exact h_lt
  · -- Case n < 2, so n = 1 since 1 <= n
    have h_eq : n = 1 := by omega
    subst h_eq
    -- A038107 1 = 0 and A038107 2 = 2, so 0 < 2
    decide
