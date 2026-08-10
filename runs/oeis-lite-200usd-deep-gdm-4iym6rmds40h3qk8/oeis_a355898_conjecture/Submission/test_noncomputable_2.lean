import Mathlib

def A355898 : ℕ → ℕ
| 0 => 0
| 1 => 1
| 2 => 1
| n + 3 =>
  let an_minus_1 := A355898 (n + 2)
  let an_minus_2 := A355898 (n + 1)
  let g := Nat.gcd an_minus_1 an_minus_2
  g + (an_minus_1 + an_minus_2) / g

def c_seq : ℕ → ℤ
| 0 => 0
| m + 1 => c_seq m -- dummy for now

def d_seq : ℕ → ℤ
| 0 => 0
| m + 1 => d_seq m -- dummy for now

def G_prop (n : ℕ) (m : ℕ) : Prop :=
  if n - m = 3774 then True else Nat.gcd (Int.natAbs (c_seq m + A355898 (n - m))) (Int.natAbs (d_seq m + A355898 (n - 1 - m))) = 1

lemma G_prop_base_eq (n : ℕ) (m' : ℕ) (h_eq : n - (m' + 1) = 3774) : G_prop (n - 1) m' = G_prop n (m' + 1) := by
  have h1 : (n - 1) - m' = 3774 := by omega
  have h2 : n - (m' + 1) = 3774 := h_eq
  unfold G_prop
  rw [if_pos h1, if_pos h2]
