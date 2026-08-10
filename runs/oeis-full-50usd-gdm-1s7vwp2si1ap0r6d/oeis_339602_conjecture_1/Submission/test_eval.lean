import FormalConjectures.Util.ProblemImports

open Nat

def A030101 (n : ℕ) : ℕ :=
  Nat.ofDigits 2 (List.reverse (Nat.digits 2 n))

def a : ℕ → ℕ
  | 0     => 0
  | 1     => 1
  | n + 2 => (a n).xor (A030101 (a (n + 1))) + 1
termination_by n => n

def digits_fast_aux : ℕ → ℕ → List ℕ
  | 0, _ => []
  | fuel + 1, n =>
    if n = 0 then []
    else (n % 2) :: digits_fast_aux fuel (n / 2)

def A030101_fast (n : ℕ) : ℕ :=
  Nat.ofDigits 2 (List.reverse (digits_fast_aux n n))

def a_aux : ℕ → ℕ × ℕ
  | 0 => (0, 1)
  | n + 1 =>
    let (x, y) := a_aux n
    (y, x.xor (A030101_fast y) + 1)

def a_fast (n : ℕ) : ℕ :=
  (a_aux n).1


theorem a_pos (k : ℕ) (hk : k ≠ 0) : a k ≠ 0 := by
  cases k with
  | zero => contradiction
  | succ k' =>
    cases k' with
    | zero => simp [a]
    | succ k'' =>
      rw [a]
      omega

theorem A030101_odd (m : ℕ) (hm : m ≠ 0) : A030101 m % 2 = 1 := by
  dsimp [A030101]
  rw [Nat.ofDigits_mod_eq_head!]
  have h_ne : Nat.digits 2 m ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hm
  rw [head!_reverse (Nat.digits 2 m) h_ne]
  have h_mem : (Nat.digits 2 m).getLast h_ne ∈ Nat.digits 2 m := List.getLast_mem h_ne
  have h_lt : (Nat.digits 2 m).getLast h_ne < 2 := Nat.digits_lt_base Nat.one_lt_two h_mem
  have h_nz := Nat.getLast_digit_ne_zero 2 hm
  have h_eq_one : (Nat.digits 2 m).getLast h_ne = 1 := by omega
  rw [h_eq_one]

theorem a_parity (n : ℕ) : a n % 2 = n % 2 := by
  induction' n using a.induct with n ih1 ih2
  · simp [a]
  · simp [a]
  · rw [a]
    have h_pos : a (n + 1) ≠ 0 := a_pos (n + 1) (by omega)
    have h_odd := A030101_odd (a (n + 1)) h_pos
    have h_xor : (a n ^^^ A030101 (a (n + 1))) % 2 = (a n + A030101 (a (n + 1))) % 2 := Nat.xor_mod_two_eq
    have h_goal : ((a n ^^^ A030101 (a (n + 1))) + 1) % 2 = (a n % 2 + 1 + 1) % 2 := by omega
    rw [h_goal, ih1]
    omega







#eval a_fast 100000

