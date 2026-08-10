import Mathlib

open Nat Set

noncomputable def A268597 (n : ℕ) : ℕ :=
  sInf { x : ℕ | x > 0 ∧ (x - 1) % Nat.totient x = n }

theorem totient_prime_sq (p : ℕ) (hp : p.Prime) : Nat.totient (p^2) = p * (p - 1) := by
  have h1 : 0 < 2 := by decide
  have h2 := Nat.totient_prime_pow hp h1
  have h3 : p ^ (2 - 1) = p := by
    have : 2 - 1 = 1 := by decide
    rw [this, pow_one]
  rwa [h3] at h2

theorem solve_prime (n : ℕ) (hp : (n+1).Prime) : (n+1)^2 ∈ { x : ℕ | x > 0 ∧ (x - 1) % Nat.totient x = n } := by
  simp only [mem_setOf_eq]
  have h_pos : (n+1)^2 > 0 := sq_pos_of_pos (Nat.succ_pos n)
  refine ⟨h_pos, ?_⟩
  rw [totient_prime_sq (n+1) hp]
  have h_tot_eq : (n+1) * ((n+1) - 1) = (n+1) * n := by
    rw [Nat.add_sub_cancel]
  have h_eq : (n+1)^2 - 1 = (n+1) * n + n := by
    have : (n+1)^2 = (n+1)*n + n + 1 := by ring
    rw [this]
    exact Nat.add_sub_cancel ((n+1)*n + n) 1
  rw [h_tot_eq, h_eq]
  have h_n_pos : n > 0 := by
    by_contra h_zero
    have : n = 0 := by omega
    subst this
    exact Nat.not_prime_one hp
  have h_lt : n < (n+1) * n := by
    have : 1 < n + 1 := by omega
    have h1 : 1 * n < (n+1) * n := Nat.mul_lt_mul_of_pos_right this h_n_pos
    rwa [one_mul] at h1
  have h_mod : (n + (n+1)*n) % ((n+1)*n) = n % ((n+1)*n) := by
    have h_rew : n + (n+1)*n = n + ((n+1)*n) * 1 := by ring
    rw [h_rew]
    exact Nat.add_mul_mod_self_left n ((n+1)*n) 1
  rw [Nat.add_comm ((n+1)*n) n]
  rw [h_mod]
  exact Nat.mod_eq_of_lt h_lt

theorem solve_pow2 (k : ℕ) (hk : 0 < k) : 2^(k+1) ∈ { x : ℕ | x > 0 ∧ (x - 1) % Nat.totient x = 2^k - 1 } := by
  simp only [mem_setOf_eq]
  have h_pos : 2^(k+1) > 0 := pos_of_gt (by positivity)
  refine ⟨h_pos, ?_⟩
  have h_tot : Nat.totient (2^(k+1)) = 2^k := by
    have h_prime : Nat.Prime 2 := Nat.prime_two
    have h_k1_pos : 0 < k + 1 := by omega
    have h_tot2 := Nat.totient_prime_pow h_prime h_k1_pos
    rw [h_tot2]
    have h_sub : k + 1 - 1 = k := by omega
    rw [h_sub]
    ring
  rw [h_tot]
  have h_div : 2^(k+1) - 1 = 1 * 2^k + (2^k - 1) := by
    have h_pow : 2^(k+1) = 2^k + 2^k := by ring
    rw [h_pow]
    omega
  have h_rew : 1 * 2^k + (2^k - 1) = (2^k - 1) + 2^k * 1 := by omega
  rw [h_div, h_rew]
  rw [Nat.add_mul_mod_self_left (2^k - 1) (2^k) 1]
  have h_lt : 2^k - 1 < 2^k := by omega
  exact Nat.mod_eq_of_lt h_lt
