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
  by_cases h_one : k = 1
  · subst k
    norm_num [Polynomial.cyclotomic_one] at hp
  · have hk' : 1 < k := by omega
    rw [Nat.cast_zero, ← Polynomial.coeff_zero_eq_eval_zero,
      Polynomial.cyclotomic_coeff_zero ℤ hk'] at hp
    norm_num at hp
