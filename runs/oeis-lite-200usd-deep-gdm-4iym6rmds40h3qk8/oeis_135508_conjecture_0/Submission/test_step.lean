import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 10000000

open Nat

/--
The auxiliary sequence $x(n)$, where $x(1)=1$ and $x(n) = 2 \cdot x(n-1) + \mathrm{lcm}(x(n-1), n)$ for $n > 1$.
`x_seq n` corresponds to the OEIS term $x(n)$.
This definition is set up for `n : ℕ` where $n=0$ and $n=1$ are base cases for $x(0)$ and $x(1)$.
Note: Mathlib's `lcm` is `Nat.lcm`.
-/
def x_seq : ℕ → ℕ
| 0 => 0
| 1 => 1
| n + 1 => 2 * (x_seq n) + Nat.lcm (x_seq n) (n + 1)

/--
A135508: $a(n) = x(n+1)/x(n) - 2$ where $x(1)=1$ and $x(n) = 2*x(n-1) + \operatorname{lcm}(x(n-1),n)$.
-/
def A135508 (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    let x_n_plus_1 := x_seq (n + 1)
    let x_n := x_seq n
    (x_n_plus_1 / x_n) - 2

lemma x_seq_pos (n : ℕ) (h : n > 0) : x_seq n > 0 := by
  induction n with
  | zero => contradiction
  | succ n ih =>
    cases n with
    | zero =>
      decide
    | succ n =>
      simp [x_seq]
      have : n + 1 > 0 := Nat.succ_pos n
      have ih' := ih this
      omega

lemma lcm_div_self_eq (a b : ℕ) (ha : a > 0) :
    Nat.lcm a b / a = b / Nat.gcd a b := by
  have h_dvd : Nat.gcd a b ∣ b := Nat.gcd_dvd_right a b
  have h_cancel : b = Nat.gcd a b * (b / Nat.gcd a b) := (Nat.mul_div_cancel' h_dvd).symm
  have h_lcm : Nat.lcm a b = a * (b / Nat.gcd a b) := by
    have h_gcd : Nat.gcd a b > 0 := by
      exact Nat.gcd_pos_of_pos_left b ha
    have h_prod : a * b = a * (Nat.gcd a b * (b / Nat.gcd a b)) := by rw [← h_cancel]
    have h_mul_lcm : Nat.lcm a b * Nat.gcd a b = a * b := by
      rw [Nat.mul_comm]
      exact Nat.gcd_mul_lcm a b
    have h_eq : Nat.lcm a b * Nat.gcd a b = a * (b / Nat.gcd a b) * Nat.gcd a b := by
      rw [h_mul_lcm]
      rw [h_prod]
      ring
    exact Nat.eq_of_mul_eq_mul_right h_gcd h_eq
  rw [h_lcm]
  rw [Nat.mul_div_cancel_left _ ha]

lemma x_seq_p_eq (p : ℕ) (hp : Nat.Prime p) :
    x_seq (p + 1) = 2 * (x_seq p) + Nat.lcm (x_seq p) (p + 1) := by
  rfl

lemma A135508_eq (p : ℕ) (hp : Nat.Prime p) :
    A135508 (p - 1) = (x_seq p / x_seq (p - 1)) - 2 := by
  unfold A135508
  split_ifs with h
  · have hp_ge_2 : p ≥ 2 := Nat.Prime.two_le hp
    omega
  · rfl

lemma A135508_p_eq (p : ℕ) (hp : Nat.Prime p) :
    A135508 (p - 1) = Nat.lcm (x_seq (p - 1)) p / x_seq (p - 1) := by
  have hp_ge_2 : p ≥ 2 := Nat.Prime.two_le hp
  have h_div_p : p - 1 + 1 = p := by omega
  have h_step : x_seq p = 2 * x_seq (p - 1) + Nat.lcm (x_seq (p - 1)) p := by
    have h_step_raw := x_seq_p_eq (p - 1) hp
    -- wait, x_seq_p_eq requires Nat.Prime (p-1) which is not always true!
    sorry

#print axioms A135508_p_eq
