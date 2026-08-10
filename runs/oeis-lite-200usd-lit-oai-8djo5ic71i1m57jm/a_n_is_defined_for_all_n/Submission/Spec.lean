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
  rcases h 0 with ⟨k, hkpos, hkprime⟩
  have hval : (Polynomial.eval (0 : ℤ) (Polynomial.cyclotomic k ℤ)).natAbs = 1 := by
    cases k with
    | zero => omega
    | succ k' =>
        cases k' with
        | zero =>
            simp [Polynomial.cyclotomic_one]
        | succ k'' =>
            have hkgt : 1 < Nat.succ (Nat.succ k'') := by omega
            rw [← Polynomial.coeff_zero_eq_eval_zero]
            rw [Polynomial.cyclotomic_coeff_zero ℤ hkgt]
            simp
  exact Nat.not_prime_one (by simpa [hval] using hkprime)
