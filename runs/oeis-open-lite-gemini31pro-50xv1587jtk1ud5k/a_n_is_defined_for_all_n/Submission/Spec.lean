import FormalConjectures.Util.ProblemImports

open Polynomial Int Set

/--
A117545: Least $k$ such that $\Phi(k,n)$, the $k$-th cyclotomic polynomial evaluated at $n$, is prime.
$$a(n) = \min \{k \in \mathbb{N} \mid \text{Prime}(\Phi_k(n)) \}$$
-/
noncomputable def a (n : ℕ) : ℕ :=
  sInf { k : ℕ | 0 < k ∧ (Polynomial.eval (n : ℤ) (Polynomial.cyclotomic k ℤ)).natAbs.Prime }

/--
OEIS A117545 Conjecture 0:
Is $a(n)$ defined for all $n$?
That is, for every $n \in \mathbb{N}$, does there exist a $k \in \mathbb{N}$ such that $0 < k$ and $\Phi_k(n)$ is prime?
-/
theorem a_n_is_defined_for_all_n :
  ∀ n : ℕ, ∃ k : ℕ, 0 < k ∧ (Polynomial.eval (n : ℤ) (Polynomial.cyclotomic k ℤ)).natAbs.Prime := by sorry

theorem a_n_is_defined_for_all_n.disproof : ¬ (type_of% @a_n_is_defined_for_all_n) := by
  intro h
  rcases h 0 with ⟨k, _, hprime⟩
  have h_eval : (Polynomial.eval ((0:ℕ) : ℤ) (Polynomial.cyclotomic k ℤ)).natAbs = 1 := by
    have h_coeff := coeff_zero_eq_eval_zero (Polynomial.cyclotomic k ℤ)
    have hz : ((0:ℕ) : ℤ) = 0 := by simp
    rw [hz, ← h_coeff]
    rcases lt_trichotomy 1 k with h1 | rfl | h2
    · rw [cyclotomic_coeff_zero _ h1, natAbs_one]
    · simp [cyclotomic_one]
    · have : k = 0 := by omega
      simp [this, cyclotomic_zero]
  rw [h_eval] at hprime
  exact Nat.not_prime_one hprime

