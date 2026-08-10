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
  obtain ⟨k, hk_pos, hk_prime⟩ := h 0
  change Nat.Prime (Polynomial.eval (0 : ℤ) (Polynomial.cyclotomic k ℤ)).natAbs at hk_prime
  have hk_eval : (Polynomial.eval (0 : ℤ) (Polynomial.cyclotomic k ℤ)).natAbs = 1 := by
    have h_k : k = 1 ∨ 1 < k := by omega
    rcases h_k with rfl | hk_gt_1
    · rw [cyclotomic_one]
      simp
    · have hcoeff : (Polynomial.cyclotomic k ℤ).coeff 0 = 1 := cyclotomic_coeff_zero ℤ hk_gt_1
      rw [← coeff_zero_eq_eval_zero]
      rw [hcoeff]
      rfl
  rw [hk_eval] at hk_prime
  exact Nat.not_prime_one hk_prime



