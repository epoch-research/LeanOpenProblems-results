import FormalConjectures.Util.ProblemImports

open Nat Finset

theorem step1 (N k' : ℕ) (hk' : k' ≤ 2 * N) (hN : 1 ≤ N) :
  Nat.choose (3 * N - k' - 1) (2 * N - k') * (3 * N - k') = Nat.choose (3 * N - k') (2 * N - k') * N := by
  have h1 : 3 * N - k' - 1 + 1 = 3 * N - k' := by
    have h : 1 ≤ 3 * N - k' := by omega
    omega
  have := Nat.choose_mul_succ_eq (3 * N - k' - 1) (2 * N - k')
  rw [h1] at this
  have h2 : 3 * N - k' - (2 * N - k') = N := by omega
  rw [h2] at this
  exact this

theorem step2 (N k' : ℕ) :
  Nat.choose (N + k' - 1) k' * (N + k') = Nat.choose (N + k') k' * N := by
  by_cases hNk : N + k' = 0
  · have hN : N = 0 := by omega
    have hk' : k' = 0 := by omega
    rw [hN, hk']
  · have h1 : N + k' - 1 + 1 = N + k' := by omega
    have := Nat.choose_mul_succ_eq (N + k' - 1) k'
    rw [h1] at this
    have h2 : N + k' - k' = N := by omega
    rw [h2] at this
    exact this


theorem step3 (N k' : ℕ) (hk' : k' ≤ 2 * N) :
  Nat.choose (3 * N) k' * Nat.choose (3 * N - k') (2 * N - k') = Nat.choose (3 * N) (2 * N) * Nat.choose (2 * N) k' := by
  have := Nat.choose_mul (n := 3 * N) hk'
  exact this.symm

theorem step4 (N k' : ℕ) (hk' : k' ≤ 2 * N) :
  Nat.choose (3 * N) (2 * N - k') = Nat.choose (3 * N) (N + k') := by
  have h1 : 2 * N - k' ≤ 3 * N := by omega
  have := Nat.choose_symm h1
  have h2 : 3 * N - (2 * N - k') = N + k' := by omega
  rw [h2] at this
  exact this.symm

theorem step5 (N k' : ℕ) :
  Nat.choose (3 * N) (N + k') * Nat.choose (N + k') k' = Nat.choose (3 * N) k' * Nat.choose (3 * N - k') N := by
  have hk_sub : k' ≤ N + k' := by omega
  have := Nat.choose_mul (n := 3 * N) hk_sub
  have h2 : N + k' - k' = N := by omega
  rw [h2] at this
  exact this

theorem step6 (N k' : ℕ) (hk' : k' ≤ 2 * N) :
  Nat.choose (3 * N - k') N = Nat.choose (3 * N - k') (2 * N - k') := by
  have h1 : N ≤ 3 * N - k' := by omega
  have := Nat.choose_symm h1
  have h2 : 3 * N - k' - N = 2 * N - k' := by omega
  rw [h2] at this
  exact this.symm

theorem T_identity (N k' : ℕ) (hk' : k' ≤ 2 * N) (hN : 1 ≤ N) :
  (3 * N - k') * (Nat.choose (3 * N) k' * Nat.choose (3 * N - k' - 1) (2 * N - k')) =
  (N + k') * (Nat.choose (3 * N) (2 * N - k') * Nat.choose (N + k' - 1) k') := by
  have L1 := step1 N k' hk' hN
  have L2 := step2 N k'
  have L3 := step3 N k' hk'
  have L4 := step4 N k' hk'
  have L5 := step5 N k'
  have L6 := step6 N k' hk'
  have h_LHS : (3 * N - k') * (Nat.choose (3 * N) k' * Nat.choose (3 * N - k' - 1) (2 * N - k')) = Nat.choose (3 * N) (2 * N) * (Nat.choose (2 * N) k' * N) := by
    calc
      (3 * N - k') * (Nat.choose (3 * N) k' * Nat.choose (3 * N - k' - 1) (2 * N - k')) =
        Nat.choose (3 * N) k' * (Nat.choose (3 * N - k' - 1) (2 * N - k') * (3 * N - k')) := by ring
      _ = Nat.choose (3 * N) k' * (Nat.choose (3 * N - k') (2 * N - k') * N) := by rw [L1]
      _ = (Nat.choose (3 * N) k' * Nat.choose (3 * N - k') (2 * N - k')) * N := by ring
      _ = (Nat.choose (3 * N) (2 * N) * Nat.choose (2 * N) k') * N := by rw [L3]
      _ = Nat.choose (3 * N) (2 * N) * (Nat.choose (2 * N) k' * N) := by ring
  have h_RHS : (N + k') * (Nat.choose (3 * N) (2 * N - k') * Nat.choose (N + k' - 1) k') = Nat.choose (3 * N) (2 * N) * (Nat.choose (2 * N) k' * N) := by
    calc
      (N + k') * (Nat.choose (3 * N) (2 * N - k') * Nat.choose (N + k' - 1) k') =
        Nat.choose (3 * N) (2 * N - k') * (Nat.choose (N + k' - 1) k' * (N + k')) := by ring
      _ = Nat.choose (3 * N) (2 * N - k') * (Nat.choose (N + k') k' * N) := by rw [L2]
      _ = Nat.choose (3 * N) (N + k') * (Nat.choose (N + k') k' * N) := by rw [L4]
      _ = (Nat.choose (3 * N) (N + k') * Nat.choose (N + k') k') * N := by ring
      _ = (Nat.choose (3 * N) k' * Nat.choose (3 * N - k') N) * N := by rw [L5]
      _ = (Nat.choose (3 * N) k' * Nat.choose (3 * N - k') (2 * N - k')) * N := by rw [L6]
      _ = (Nat.choose (3 * N) (2 * N) * Nat.choose (2 * N) k') * N := by rw [L3]
      _ = Nat.choose (3 * N) (2 * N) * (Nat.choose (2 * N) k' * N) := by ring
  rw [h_LHS, h_RHS]
