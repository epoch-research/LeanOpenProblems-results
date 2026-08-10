import FormalConjectures.Util.ProblemImports

open Polynomial Int Set

/--
A117545: Least $k$ such that $\Phi(k,n)$, the $k$-th cyclotomic polynomial evaluated at $n$, is prime.
$$a(n) = \min \{k \in \mathbb{N} \mid \text{Prime}(\Phi_k(n)) \}$$
-/
noncomputable def a (n : ℕ) : ℕ :=
  sInf { k : ℕ | 0 < k ∧ (Polynomial.eval (n : ℤ) (Polynomial.cyclotomic k ℤ)).natAbs.Prime }

/--
OEIS A117545 Conjecture 0 (disproof):
The statement fails at $n = 0$: we have $\Phi_1(0) = -1$ and $\Phi_k(0) = 1$ for all $k \geq 2$,
so $|\Phi_k(0)| = 1$ is never prime.
-/
theorem a_n_is_defined_for_all_n.disproof :
  ¬ ∀ n : ℕ, ∃ k : ℕ, 0 < k ∧ (Polynomial.eval (n : ℤ) (Polynomial.cyclotomic k ℤ)).natAbs.Prime := by
  intro h
  obtain ⟨k, hk, hp⟩ := h 0
  rw [Nat.cast_zero, ← Polynomial.coeff_zero_eq_eval_zero] at hp
  rcases Nat.lt_or_ge k 2 with h2 | h2
  · interval_cases k
    rw [Polynomial.cyclotomic_one] at hp
    simp only [Polynomial.coeff_sub, Polynomial.coeff_X_zero, Polynomial.coeff_one_zero,
      zero_sub] at hp
    norm_num at hp
  · rw [Polynomial.cyclotomic_coeff_zero ℤ h2] at hp
    norm_num at hp
