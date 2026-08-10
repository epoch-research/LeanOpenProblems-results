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
-- The conjecture is FALSE: for n = 0, the cyclotomic polynomial evaluated at 0
-- is always ±1 (since the constant term of Φ_k is 1 for k ≥ 2 and -1 for k = 1),
-- hence never prime. We prove the negation.
theorem a_n_is_defined_for_all_n.disproof :
  ¬ (∀ n : ℕ, ∃ k : ℕ, 0 < k ∧ (Polynomial.eval (n : ℤ) (Polynomial.cyclotomic k ℤ)).natAbs.Prime) := by
  intro h
  obtain ⟨k, hk, hprime⟩ := h 0
  rw [Nat.cast_zero] at hprime
  have key : (Polynomial.eval (0 : ℤ) (Polynomial.cyclotomic k ℤ)).natAbs = 1 := by
    rw [← Polynomial.coeff_zero_eq_eval_zero]
    rcases Nat.lt_or_ge k 2 with h1 | h1
    · -- 0 < k < 2 so k = 1
      interval_cases k
      rw [Polynomial.cyclotomic_one]
      simp
    · rw [Polynomial.cyclotomic_coeff_zero ℤ h1]; rfl
  rw [key] at hprime
  exact Nat.not_prime_one hprime

-- Also provide the disproof under the generic `foo.disproof` name.
theorem foo.disproof :
  ¬ (∀ n : ℕ, ∃ k : ℕ, 0 < k ∧ (Polynomial.eval (n : ℤ) (Polynomial.cyclotomic k ℤ)).natAbs.Prime) :=
  a_n_is_defined_for_all_n.disproof
