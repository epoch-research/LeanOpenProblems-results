import FormalConjectures.Util.ProblemImports

set_option linter.unusedVariables false

open Nat

/--
A214497: Smallest $k \ge 0$ such that $(3^n-k)2^n-1$ and $(3^n-k)2^n+1$ are a twin prime pair.
-/
noncomputable def A214497 (n : ℕ) : ℕ :=
  -- Nat.sInf is the rigorous definition of the minimum element of a set of natural numbers,
  -- which translates "smallest k" directly.
  sInf {k : ℕ | Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1)}

lemma A214497_zero (n : ℕ) (k : ℕ) (hk : k ≥ 3 ^ n) :
    ¬ (Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1)) := by
  intro h
  have h1 : 3 ^ n - k = 0 := Nat.sub_eq_zero_of_le hk
  have h2 : (3 ^ n - k) * (2 ^ n) - 1 = 0 := by
    rw [h1]
    simp
  have h_prime := h.left
  rw [h2] at h_prime
  have h0 : ¬ Nat.Prime 0 := Nat.not_prime_zero
  exact h0 h_prime

lemma k_lt_three_n (n : ℕ) (k : ℕ) (h : Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1)) :
    k < 3 ^ n := by
  by_contra hc
  push_neg at hc
  have h_not := A214497_zero n k hc
  contradiction

/--
We prove that the OEIS A214497 conjecture is logically equivalent to a bounded existential.
Since the prime condition is decidable, the bounded existential `∃ k < 3 ^ n, ...` is decidable
for each n, making the conjecture's witness search space finite.
-/
theorem oeis_214497_conjecture_equivalence (n : ℕ) :
    (∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1)) ↔
    (∃ k < 3 ^ n, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1)) := by
  constructor
  · rintro ⟨k, hk⟩
    have h_lt := k_lt_three_n n k hk
    exact ⟨k, h_lt, hk⟩
  · rintro ⟨k, _, hk⟩
    exact ⟨k, hk⟩

lemma A214497_lt_three_n (n : ℕ) (hn : n > 0) : A214497 n < 3 ^ n := by
  have h_cases : (∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1)) ∨
                 ¬(∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1)) := Classical.em _
  rcases h_cases with h_exists | h_not_exists
  · have h_nonempty : {k : ℕ | Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1)}.Nonempty := by
      rcases h_exists with ⟨k, hk_left, hk_right⟩
      exact ⟨k, hk_left, hk_right⟩
    have h_mem := Nat.sInf_mem h_nonempty
    exact k_lt_three_n n (A214497 n) h_mem
  · have h_empty : {k : ℕ | Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1)} = ∅ := by
      ext k
      constructor
      · intro hk
        exact (h_not_exists ⟨k, hk⟩).elim
      · intro h
        contradiction
    unfold A214497
    rw [h_empty]
    have h_sInf_empty : sInf ∅ = 0 := Nat.sInf_empty
    rw [h_sInf_empty]
    have h_three_n_pos : 3 ^ n > 0 := Nat.pow_pos (by decide)
    exact h_three_n_pos

/--
OEIS A214497 Conjecture: there is always one such k for each n>0.
That is, for every $n>0$, there exists a $k \ge 0$ such that
$(3^n-k)2^n-1$ and $(3^n-k)2^n+1$ are a twin prime pair.
-/
theorem oeis_214497_conjecture_0 (n : ℕ) (hn : n > 0) :
    ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1) := by
  rw [oeis_214497_conjecture_equivalence n]
  sorry




