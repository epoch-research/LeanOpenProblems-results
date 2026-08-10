import Mathlib
open Nat Finset
set_option maxRecDepth 10000

noncomputable def A130911 (n : ℕ) : ℤ :=
  let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ :=
    if (binary_weight p).bodd then 1 else -1
  Finset.sum (Finset.range n) fun i =>
    let p_i := Nat.nth Nat.Prime i
    weight_parity_sign p_i

noncomputable def wsign (p : ℕ) : ℤ := if ((Nat.digits 2 p).sum).bodd then 1 else -1
theorem A_succ (n : ℕ) : A130911 (n+1) = A130911 n + wsign (Nat.nth Nat.Prime n) := by
  simp only [A130911, wsign, Finset.sum_range_succ]
theorem wsv (p s : ℕ) (hp : (Nat.digits 2 p).sum = s) :
    wsign p = if s.bodd then 1 else -1 := by rw [wsign, hp]
macro "ds" : tactic => `(tactic| norm_num [Nat.digits_def' (b:=2) (by norm_num : 2 ≤ 2)])

theorem wp0 : wsign (Nat.nth Nat.Prime 0) = 1 := by rw [Nat.nth_prime_zero_eq_two, wsv 2 1 (by ds)]; decide
theorem wp1 : wsign (Nat.nth Nat.Prime 1) = -1 := by rw [Nat.nth_prime_one_eq_three, wsv 3 2 (by ds)]; decide
theorem wp2 : wsign (Nat.nth Nat.Prime 2) = -1 := by rw [Nat.nth_prime_two_eq_five, wsv 5 2 (by ds)]; decide
theorem wp3 : wsign (Nat.nth Nat.Prime 3) = 1 := by rw [Nat.nth_prime_three_eq_seven, wsv 7 3 (by ds)]; decide
theorem wp4 : wsign (Nat.nth Nat.Prime 4) = 1 := by rw [Nat.nth_prime_four_eq_eleven, wsv 11 3 (by ds)]; decide
theorem wp5 : wsign (Nat.nth Nat.Prime 5) = 1 := by rw [(by simpa [(by decide : Nat.count Nat.Prime 13 = 5)] using Nat.nth_count (p:=Nat.Prime) (n:=13) (by norm_num) : Nat.nth Nat.Prime 5 = 13), wsv 13 3 (by ds)]; decide
theorem wp6 : wsign (Nat.nth Nat.Prime 6) = -1 := by rw [(by simpa [(by decide : Nat.count Nat.Prime 17 = 6)] using Nat.nth_count (p:=Nat.Prime) (n:=17) (by norm_num) : Nat.nth Nat.Prime 6 = 17), wsv 17 2 (by ds)]; decide
theorem wp7 : wsign (Nat.nth Nat.Prime 7) = 1 := by rw [(by simpa [(by decide : Nat.count Nat.Prime 19 = 7)] using Nat.nth_count (p:=Nat.Prime) (n:=19) (by norm_num) : Nat.nth Nat.Prime 7 = 19), wsv 19 3 (by ds)]; decide
theorem wp8 : wsign (Nat.nth Nat.Prime 8) = -1 := by rw [(by simpa [(by decide : Nat.count Nat.Prime 23 = 8)] using Nat.nth_count (p:=Nat.Prime) (n:=23) (by norm_num) : Nat.nth Nat.Prime 8 = 23), wsv 23 4 (by ds)]; decide
theorem wp9 : wsign (Nat.nth Nat.Prime 9) = -1 := by rw [(by simpa [(by decide : Nat.count Nat.Prime 29 = 9)] using Nat.nth_count (p:=Nat.Prime) (n:=29) (by norm_num) : Nat.nth Nat.Prime 9 = 29), wsv 29 4 (by ds)]; decide

theorem A0 : A130911 0 = 0 := rfl
theorem A1 : A130911 1 = 1 := by rw [show (1:ℕ)=0+1 from rfl, A_succ, A0, wp0]; ring
theorem A2 : A130911 2 = 0 := by rw [show (2:ℕ)=1+1 from rfl, A_succ, A1, wp1]; ring
theorem A3 : A130911 3 = -1 := by rw [show (3:ℕ)=2+1 from rfl, A_succ, A2, wp2]; ring
theorem A4 : A130911 4 = 0 := by rw [show (4:ℕ)=3+1 from rfl, A_succ, A3, wp3]; ring
theorem A5 : A130911 5 = 1 := by rw [show (5:ℕ)=4+1 from rfl, A_succ, A4, wp4]; ring
theorem A6 : A130911 6 = 2 := by rw [show (6:ℕ)=5+1 from rfl, A_succ, A5, wp5]; ring
theorem A7 : A130911 7 = 1 := by rw [show (7:ℕ)=6+1 from rfl, A_succ, A6, wp6]; ring
theorem A8 : A130911 8 = 2 := by rw [show (8:ℕ)=7+1 from rfl, A_succ, A7, wp7]; ring
theorem A9 : A130911 9 = 1 := by rw [show (9:ℕ)=8+1 from rfl, A_succ, A8, wp8]; ring
theorem A10 : A130911 10 = 0 := by rw [show (10:ℕ)=9+1 from rfl, A_succ, A9, wp9]; ring

/-- The open analytic core of Shevelev's conjecture. -/
theorem shevelev_tail : ∀ n, 10 < n → 0 ≤ A130911 n := sorry

theorem oeis_130911_conjecture_0 (n : ℕ) (h : n > 3) : A130911 n ≥ 0 := by
  rcases Nat.lt_or_ge n 11 with h2 | h2
  · interval_cases n <;> simp only [ge_iff_le, A4, A5, A6, A7, A8, A9, A10] <;> norm_num
  · exact shevelev_tail n (by omega)
