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
  obtain ⟨k, hk, hp⟩ := h 0
  have hval : (Polynomial.eval ((0 : ℕ) : ℤ) (Polynomial.cyclotomic k ℤ)).natAbs = 1 := by
    rcases Nat.lt_or_ge 1 k with h1 | h1
    · rw [Nat.cast_zero, ← Polynomial.coeff_zero_eq_eval_zero, Polynomial.cyclotomic_coeff_zero ℤ h1]
      rfl
    · have : k = 1 := by omega
      subst this
      rw [Polynomial.cyclotomic_one]
      simp
  rw [hval] at hp
  exact Nat.not_prime_one hp
