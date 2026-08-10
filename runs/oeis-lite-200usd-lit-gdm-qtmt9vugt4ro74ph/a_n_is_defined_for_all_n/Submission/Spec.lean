import FormalConjectures.Util.ProblemImports

open Polynomial Int Set

/--
A117545: Least $k$ such that $\Phi(k,n)$, the $k$-th cyclotomic polynomial evaluated at $n$, is prime.
$$a(n) = \min \{k \in \mathbb{N} \mid \text{Prime}(\Phi_k(n)) \}$$
-/
noncomputable def a (n : ℕ) : ℕ :=
  sInf { k : ℕ | 0 < k ∧ (Polynomial.eval (n : ℤ) (Polynomial.cyclotomic k ℤ)).natAbs.Prime }

theorem eval_zero_eq_coeff_zero (p : ℤ[X]) : eval 0 p = coeff p 0 := by
  exact (coeff_zero_eq_eval_zero p).symm

theorem test_eval_zero_k (k : ℕ) (hk : 0 < k) :
  (Polynomial.eval (0 : ℤ) (Polynomial.cyclotomic k ℤ)).natAbs = 1 := by
  rcases eq_or_ne k 1 with rfl | hk_ne
  · -- k = 1
    simp [cyclotomic_one]
  · -- k > 1
    have hk_gt1 : 1 < k := by
      omega
    have hcoeff := cyclotomic_coeff_zero ℤ hk_gt1
    rw [coeff_zero_eq_eval_zero] at hcoeff
    rw [hcoeff]
    simp

/--
OEIS A117545 Conjecture 0:
Is $a(n)$ defined for all $n$?
That is, for every $n \in \mathbb{N}$, does there exist a $k \in \mathbb{N}$ such that $0 < k$ and $\Phi_k(n)$ is prime?
-/
theorem a_n_is_defined_for_all_n.disproof :
  ¬ (∀ n : ℕ, ∃ k : ℕ, 0 < k ∧ (Polynomial.eval (n : ℤ) (Polynomial.cyclotomic k ℤ)).natAbs.Prime) := by
  intro h
  obtain ⟨k, hk_pos, hk_prime⟩ := h 0
  rw [Nat.cast_zero] at hk_prime
  have h_val := test_eval_zero_k k hk_pos
  rw [h_val] at hk_prime
  exact Nat.not_prime_one hk_prime
