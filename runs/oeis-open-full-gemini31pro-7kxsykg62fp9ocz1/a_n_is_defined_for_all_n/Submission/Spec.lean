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
  have h0 := h 0
  rcases h0 with ⟨k, hk0, hkp⟩
  have h_zero : (0 : ℤ) = ↑(0 : ℕ) := rfl
  rw [← h_zero] at hkp
  rcases eq_or_lt_of_le (Nat.succ_le_of_lt hk0) with rfl | hk1
  · have h_eval : eval (0 : ℤ) (cyclotomic 1 ℤ) = -1 := by
      rw [cyclotomic_one, eval_sub, eval_X, eval_one, zero_sub]
    have h_one : (1 : ℕ) = Nat.succ 0 := rfl
    rw [← h_one] at hkp
    rw [h_eval] at hkp
    have h_abs : (-1 : ℤ).natAbs = 1 := rfl
    rw [h_abs] at hkp
    exact Nat.not_prime_one hkp
  · have h_eval : eval (0 : ℤ) (cyclotomic k ℤ) = 1 := by
      rw [← coeff_zero_eq_eval_zero, cyclotomic_coeff_zero _ hk1]
    rw [h_eval] at hkp
    have h_abs : (1 : ℤ).natAbs = 1 := rfl
    rw [h_abs] at hkp
    exact Nat.not_prime_one hkp
