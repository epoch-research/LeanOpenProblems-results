import FormalConjectures.Util.ProblemImports

open Nat Set
#check Nat.exists_infinite_primes


def A234642_condition_test (n x : ℕ) : Prop :=
  x.totient > 0 ∧ x % x.totient = n

theorem test_exists_zero : ∃ x, A234642_condition_test 0 x := by
  use 1
  unfold A234642_condition_test
  decide

theorem test_exists_one : ∃ x, A234642_condition_test 1 x := by
  use 3
  unfold A234642_condition_test
  decide



lemma totient_prime_sq_local {p : ℕ} (hp : p.Prime) : (p^2).totient = p * (p - 1) := by
  have h_sq : p^2 = p^(1 + 1) := rfl
  rw [h_sq, Nat.totient_prime_pow_succ hp 1]
  simp

theorem test_exists_prime (n : ℕ) (hp : n.Prime) (hn : n ≥ 3) : ∃ x, A234642_condition_test n x := by
  use n^2
  unfold A234642_condition_test
  constructor
  · have h2 : n > 0 := Nat.Prime.pos hp
    rw [totient_prime_sq_local hp]
    apply Nat.mul_pos h2
    omega
  · rw [totient_prime_sq_local hp]
    -- we want to prove n^2 % (n * (n - 1)) = n
    -- n^2 = n * (n - 1) + n
    have hq : n * (n - 1) > n := by
      have : n - 1 ≥ 2 := by omega
      calc
        n * (n - 1) ≥ n * 2 := Nat.mul_le_mul_left n this
        _ = 2 * n := by ring
        _ > n := by omega
    have h_eq : n^2 = (n * (n - 1)) + n := by
      calc
        n^2 = n * n := by ring
        _ = n * (n - 1 + 1) := by congr; omega
        _ = n * (n - 1) + n := by ring
    rw [h_eq]
    rw [add_comm]
    rw [Nat.add_mod_right]
    apply Nat.mod_eq_of_lt hq
