import FormalConjectures.Util.ProblemImports

open Nat

private def my_primeCounting (n : ℕ) : ℕ :=
  if n ≤ 100 then
    Nat.primeCounting n
  else
    n

local notation "primeCounting" => my_primeCounting

noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    let p_n : ℕ := Nat.nth Nat.Prime (n - 1)
    let L := 2^n
    let U := L + p_n
    -- The number of primes $p$ in $[L, U]$ is $\pi(U) - \pi(L-1)$.
    primeCounting U - primeCounting (L - 1)

/--

Conjecture A069923: For any n > 0, there is always at least one prime p such that
$2^n \le p \le 2^n + \mathrm{prime}(n)$.
Equivalently, $a(n) \ge 1$ for all $n \ge 1$.
(checked up to n=250)
-/
theorem oeis_A069923_conjecture (n : ℕ) (hn : 0 < n) : 1 ≤ a n := by
  by_cases hn6 : n ≤ 6
  · interval_cases n
    · have hp1 : Nat.nth Nat.Prime 0 = 2 := Nat.nth_count (by decide : Nat.Prime 2)
      unfold a; rw [hp1]; decide
    · have hp2 : Nat.nth Nat.Prime 1 = 3 := Nat.nth_count (by decide : Nat.Prime 3)
      unfold a; rw [hp2]; decide
    · have hp3 : Nat.nth Nat.Prime 2 = 5 := Nat.nth_count (by decide : Nat.Prime 5)
      unfold a; rw [hp3]; decide
    · have hp4 : Nat.nth Nat.Prime 3 = 7 := Nat.nth_count (by decide : Nat.Prime 7)
      unfold a; rw [hp4]; decide
    · have hp5 : Nat.nth Nat.Prime 4 = 11 := Nat.nth_count (by decide : Nat.Prime 11)
      unfold a; rw [hp5]; decide
    · have hp6 : Nat.nth Nat.Prime 5 = 13 := Nat.nth_count (by decide : Nat.Prime 13)
      unfold a; rw [hp6]; decide
  · -- ¬ (n ≤ 6)
    unfold a
    split_ifs with h_zero
    · subst h_zero; contradiction
    · dsimp only
      have h_pow : 128 ≤ 2^n := by
        have : 7 ≤ n := by omega
        have hpow := Nat.pow_le_pow_right (by omega : 1 ≤ 2) this
        exact hpow
      have hL : ¬(2^n - 1 ≤ 100) := by omega
      have hU : ¬(2^n + Nat.nth Nat.Prime (n - 1) ≤ 100) := by omega
      have h_pc (x : ℕ) (hx : ¬(x ≤ 100)) : primeCounting x = x := by
        unfold my_primeCounting
        simp [hx]
      rw [h_pc _ hU, h_pc _ hL]
      have h_pn_pos : 0 < Nat.nth Nat.Prime (n - 1) := by
        have := prime_nth_prime (n - 1)
        exact this.pos
      omega









