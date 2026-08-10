import FormalConjectures.Util.ProblemImports
import Mathlib.Data.Nat.Prime.Nth

open BigOperators Nat Int

def fermat_quotient_int (k p : ℕ) : ℤ := (((k : ℤ) ^ (p - 1) - 1) / (p : ℤ))

def wilson_quotient_int (p : ℕ) : ℤ := ((p - 1).factorial + 1) / (p : ℤ)

noncomputable def a (n : ℕ) : ℕ :=
  if 1 < n then
    let p_n : ℕ := Nat.nth Nat.Prime (n - 1)
    let p_z : ℤ := p_n
    let sum_q : ℤ := Finset.sum (Finset.range (p_n - 1)) (fun k : ℕ => fermat_quotient_int (k + 1) p_n)
    let L_p : ℤ := sum_q - wilson_quotient_int p_n
    (L_p / p_z).natAbs
  else
    0

theorem nth_prime_one_eq_three_local : Nat.nth Nat.Prime 1 = 3 := by
  have h : Nat.nth Nat.Prime (Nat.count Nat.Prime 3) = 3 := Nat.nth_count (by decide : (3 : ℕ).Prime)
  have hc : Nat.count Nat.Prime 3 = 1 := by rfl
  rw [hc] at h
  exact h

theorem nth_prime_two_eq_five_local : Nat.nth Nat.Prime 2 = 5 := by
  have h : Nat.nth Nat.Prime (Nat.count Nat.Prime 5) = 5 := Nat.nth_count (by decide : (5 : ℕ).Prime)
  have hc : Nat.count Nat.Prime 5 = 2 := by rfl
  rw [hc] at h
  exact h

theorem nth_prime_three_eq_seven_local : Nat.nth Nat.Prime 3 = 7 := by
  have h : Nat.nth Nat.Prime (Nat.count Nat.Prime 7) = 7 := Nat.nth_count (by decide : (7 : ℕ).Prime)
  have hc : Nat.count Nat.Prime 7 = 3 := by rfl
  rw [hc] at h
  exact h

theorem a_two_eq_zero : a 2 = 0 := by
  unfold a
  dsimp
  rw [nth_prime_one_eq_three_local]
  decide

theorem a_three_eq_thirteen : a 3 = 13 := by
  unfold a
  dsimp
  rw [nth_prime_two_eq_five_local]
  decide

theorem a_four_eq_1356 : a 4 = 1356 := by
  unfold a
  dsimp
  rw [nth_prime_three_eq_seven_local]
  decide

theorem proof_cases (n : ℕ) (hn : 1 < n) (hp : Nat.Prime (a n)) : a n = 13 := by
  rcases n with _ | _ | _ | _ | _ | n_gt
  · omega
  · omega
  · -- n = 2
    have ha2 : a 2 = 0 := a_two_eq_zero
    rw [ha2] at hp
    exfalso
    exact Nat.not_prime_zero hp
  · -- n = 3
    exact a_three_eq_thirteen
  · -- n = 4
    have ha4 : a 4 = 1356 := a_four_eq_1356
    rw [ha4] at hp
    exfalso
    have h_div : 2 ∣ 1356 := by decide
    have h_le : 2 ≤ 2 := by decide
    have h_lt2 : 2 < 1356 := by decide
    exact Nat.not_prime_of_dvd_of_lt h_div h_le h_lt2 hp
  · sorry
