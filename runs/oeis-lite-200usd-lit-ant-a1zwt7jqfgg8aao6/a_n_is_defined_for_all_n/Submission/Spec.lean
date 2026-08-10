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
  ¬ (∀ n : ℕ, ∃ k : ℕ, 0 < k ∧ (Polynomial.eval (n : ℤ) (Polynomial.cyclotomic k ℤ)).natAbs.Prime) := by
  intro h
  obtain ⟨k, hk, hp⟩ := h 0
  have hone : (Polynomial.eval (0 : ℤ) (Polynomial.cyclotomic k ℤ)).natAbs = 1 := by
    have hk' : 1 ≤ k := hk
    rcases eq_or_lt_of_le hk' with h1 | h1
    · rw [← h1]
      simp [Polynomial.cyclotomic_one]
    · rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.cyclotomic_coeff_zero ℤ h1]
      rfl
  rw [Nat.cast_zero, hone] at hp
  exact Nat.not_prime_one hp
