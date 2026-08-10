import FormalConjectures.Util.ProblemImports

open Nat Set

lemma totient_prime_sq_local {p : ℕ} (hp : p.Prime) : (p^2).totient = p * (p - 1) := by
  have h_sq : p^2 = p^(1 + 1) := rfl
  rw [h_sq, Nat.totient_prime_pow_succ hp 1]
  simp

def A234642_condition (n x : ℕ) : Prop :=
  x.totient > 0 ∧ x % x.totient = n

theorem test_first_branch (n : ℕ) (hp : (n + 3).Prime) : ∃ x, A234642_condition (n + 3) x := by
  use (n + 3)^2
  unfold A234642_condition
  constructor
  · have h2 : n + 3 > 0 := Nat.Prime.pos hp
    rw [totient_prime_sq_local hp]
    apply Nat.mul_pos h2
    omega
  · rw [totient_prime_sq_local hp]
    have h_sub : n + 3 - 1 = n + 2 := by omega
    rw [h_sub]
    have hq : (n + 3) * (n + 2) > n + 3 := by
      have : n + 2 ≥ 2 := by omega
      calc
        (n + 3) * (n + 2) ≥ (n + 3) * 2 := Nat.mul_le_mul_left (n + 3) this
        _ = 2 * (n + 3) := by ring
        _ > n + 3 := by omega
    have h_eq : (n + 3)^2 = (n + 3) * (n + 2) + (n + 3) := by ring
    rw [h_eq]
    rw [add_comm]
    rw [Nat.add_mod_right]
    rw [Nat.mod_eq_of_lt hq]
