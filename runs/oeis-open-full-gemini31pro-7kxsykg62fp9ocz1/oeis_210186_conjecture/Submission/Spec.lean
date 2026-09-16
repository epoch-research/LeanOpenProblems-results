import FormalConjectures.Util.ProblemImports

open Nat Finset Set BigOperators

noncomputable def prod_first_k_primes (k : ℕ) : ℕ :=
  (range k).prod (fun i => Nat.nth Nat.Prime i)

noncomputable def A210186 (n : ℕ) : ℕ :=
  sInf { m : ℕ |
    1 < m ∧
    ∀ i j : ℕ,
      (1 ≤ i ∧ i < j ∧ j ≤ n) →
      ¬ (m ∣ (prod_first_k_primes i + prod_first_k_primes j)) }

theorem A_0 : A210186 0 = 2 := by
  have H : { m : ℕ | 1 < m ∧ ∀ i j : ℕ, (1 ≤ i ∧ i < j ∧ j ≤ 0) → ¬ (m ∣ (prod_first_k_primes i + prod_first_k_primes j)) } = { m : ℕ | 1 < m } := by
    ext m
    simp only [mem_setOf_eq]
    constructor
    · rintro ⟨h1, h2⟩
      exact h1
    · rintro h1
      refine ⟨h1, ?_⟩
      intro i j hij
      omega
  unfold A210186
  rw [H]
  have h3 : 2 ∈ { m : ℕ | 1 < m } := by
    simp only [mem_setOf_eq]
    decide
  have h4 : ∀ x ∈ { m : ℕ | 1 < m }, 2 ≤ x := by
    intro x hx
    simp only [mem_setOf_eq] at hx
    omega
  apply le_antisymm
  · exact csInf_le (OrderBot.bddBelow _) h3
  · exact le_csInf (by use 2) h4

theorem a210186_conjecture_disproof : ¬ ((∀ n : ℕ, Nat.Prime (A210186 n)) ∧ (∀ n : ℕ, 1 < n → A210186 n < n^2)) := by
  intro h
  rcases h with ⟨h_prime, _⟩
  have hp0 := h_prime 0
  rw [A_0] at hp0
  have h_contra : ¬Nat.Prime 2 := by decide
  contradiction

theorem oeis_210186_conjecture :
  (∀ n : ℕ, Nat.Prime (A210186 n)) ∧ (∀ n : ℕ, 1 < n → A210186 n < n^2) := by
  sorry

theorem oeis_210186_conjecture.disproof : ¬ (type_of% @oeis_210186_conjecture) := by
  exact a210186_conjecture_disproof
