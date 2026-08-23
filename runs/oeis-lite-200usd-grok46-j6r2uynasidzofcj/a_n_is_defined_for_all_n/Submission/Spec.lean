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
theorem a_n_is_defined_for_all_n.disproof :
    ¬∀ n : ℕ, ∃ k : ℕ, 0 < k ∧ (Polynomial.eval (n : ℤ) (Polynomial.cyclotomic k ℤ)).natAbs.Prime := by
  intro h
  obtain ⟨k, hk_pos, hk_prime⟩ := h 0
  simp only [Nat.cast_zero] at hk_prime
  have heq : (eval (0 : ℤ) (cyclotomic k ℤ)).natAbs = 1 := by
    match k with
    | 0 => exact absurd hk_pos (lt_irrefl _)
    | 1 =>
      rw [cyclotomic_one, eval_sub, eval_X, eval_one, zero_sub, natAbs_neg, natAbs_one]
    | k + 2 =>
      have hn : 1 < k + 2 := by omega
      rw [← coeff_zero_eq_eval_zero, cyclotomic_coeff_zero ℤ hn, natAbs_one]
  rw [heq] at hk_prime
  exact Nat.not_prime_one hk_prime
