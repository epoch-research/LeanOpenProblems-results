import FormalConjectures.Util.ProblemImports

open Nat

/--
The auxiliary sequence $b(k)$ for A323359, where $b(1)=2$ and $b(k) = b(k-1) + \operatorname{lcm}(\lfloor\sqrt{k^3}\rfloor, b(k-1))$ for $k \ge 2$.
-/
def b : ℕ → ℕ
| 0 => 0
| 1 => 2
| k_plus_1 + 1 =>
  let k := k_plus_1 + 1
  let b_prev := b k_plus_1
  b_prev + Nat.lcm (Nat.sqrt (k ^ 3)) b_prev

/--
A323359: $a(n) = b(n+1)/b(n) - 1$, where $n>0$ and $b$ is the auxiliary sequence.
-/
def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    (b (n + 1) / b n) - 1

lemma b_step (k : ℕ) (hk : 0 < k) : b (k + 1) = b k + Nat.lcm (Nat.sqrt ((k + 1) ^ 3)) (b k) := by
  cases k with
  | zero =>
    contradiction
  | succ k_prev =>
    rfl

lemma b_ge_two (n : ℕ) (hn : 0 < n) : 2 <= b n := by
  induction n with
  | zero => contradiction
  | succ n ih =>
    cases n with
    | zero =>
      show 2 <= b 1
      decide
    | succ n_prev =>
      have h_step := b_step (n_prev + 1) (Nat.succ_pos n_prev)
      rw [h_step]
      have ih_prev : 2 <= b (n_prev + 1) := ih (Nat.succ_pos n_prev)
      omega

lemma b_pos (n : ℕ) (hn : 0 < n) : 0 < b n := by
  have h := b_ge_two n hn
  omega

lemma a_eq (n : ℕ) (hn : 0 < n) : a n = (b (n + 1) / b n) - 1 := by
  unfold a
  split_ifs with h
  · subst h; contradiction
  · rfl

lemma add_div_self_left_var (x y : ℕ) (hx : 0 < x) : (x + y) / x = 1 + y / x := by
  rw [Nat.add_comm x y]
  rw [Nat.add_div_right y hx]
  rw [Nat.add_comm]

lemma lcm_div_self_right (x y : ℕ) (hy : 0 < y) : Nat.lcm x y / y = x / Nat.gcd x y := by
  have h_gcd_pos : 0 < Nat.gcd x y := Nat.gcd_pos_of_pos_right x hy
  have h_lcm_gcd : Nat.lcm x y * Nat.gcd x y = x * y := Nat.lcm_mul_gcd x y
  have h_lcm_div : Nat.lcm x y = (Nat.lcm x y / y) * y := by
    rw [Nat.div_mul_cancel (Nat.dvd_lcm_right x y)]
  have h3 : (Nat.lcm x y / y) * Nat.gcd x y * y = x * y := by
    calc
      (Nat.lcm x y / y) * Nat.gcd x y * y = ((Nat.lcm x y / y) * y) * Nat.gcd x y := by ac_rfl
      _ = Nat.lcm x y * Nat.gcd x y := by rw [← h_lcm_div]
      _ = x * y := h_lcm_gcd
  have h4 : ((Nat.lcm x y / y) * Nat.gcd x y * y) / y = (x * y) / y := by rw [h3]
  rw [Nat.mul_div_cancel ((Nat.lcm x y / y) * Nat.gcd x y) hy] at h4
  rw [Nat.mul_div_cancel x hy] at h4
  have h5 : ((Nat.lcm x y / y) * Nat.gcd x y) / Nat.gcd x y = x / Nat.gcd x y := by rw [h4]
  rw [Nat.mul_div_cancel (Nat.lcm x y / y) h_gcd_pos] at h5
  exact h5

lemma a_eq_formula (n : ℕ) (hn : 0 < n) : a n = Nat.sqrt ((n + 1) ^ 3) / Nat.gcd (Nat.sqrt ((n + 1) ^ 3)) (b n) := by
  have h_b_step := b_step n hn
  have h_b_pos := b_pos n hn
  have h_a_eq := a_eq n hn
  rw [h_b_step] at h_a_eq
  rw [add_div_self_left_var (b n) (Nat.lcm (Nat.sqrt ((n + 1) ^ 3)) (b n)) h_b_pos] at h_a_eq
  have h_add_sub : 1 + Nat.lcm (Nat.sqrt ((n + 1) ^ 3)) (b n) / b n - 1 = Nat.lcm (Nat.sqrt ((n + 1) ^ 3)) (b n) / b n := by
    rw [Nat.add_comm]
    rfl
  rw [h_add_sub] at h_a_eq
  rw [lcm_div_self_right (Nat.sqrt ((n + 1) ^ 3)) (b n) h_b_pos] at h_a_eq
  exact h_a_eq

lemma a_dvd_term (n : ℕ) (hn : 0 < n) : a n ∣ Nat.sqrt ((n + 1) ^ 3) := by
  rw [a_eq_formula n hn]
  have h_gcd := Nat.gcd_dvd_left (Nat.sqrt ((n + 1) ^ 3)) (b n)
  exact Nat.div_dvd_of_dvd h_gcd

lemma a_ge_one (n : ℕ) (hn : 0 < n) : 1 ≤ a n := by
  have h_a_eq := a_eq_formula n hn
  rw [h_a_eq]
  -- We want to show that term / gcd >= 1.
  -- Since gcd ∣ term, term / gcd is at least 1 as long as term > 0.
  have h_term_pos : 0 < Nat.sqrt ((n + 1) ^ 3) := by
    have h_n1 : 1 < n + 1 := by omega
    have h_pow : 1 < (n + 1) ^ 3 := by
      have h : 2 ≤ n + 1 := by omega
      have h2 : 2^3 ≤ (n+1)^3 := Nat.pow_le_pow_left h 3
      omega
    have h_sqrt : 0 < Nat.sqrt ((n + 1) ^ 3) := by
      rw [Nat.sqrt_pos]
      omega
    exact h_sqrt
  have h_gcd_dvd : Nat.gcd (Nat.sqrt ((n + 1) ^ 3)) (b n) ∣ Nat.sqrt ((n + 1) ^ 3) := Nat.gcd_dvd_left _ _
  have h_gcd_pos : 0 < Nat.gcd (Nat.sqrt ((n + 1) ^ 3)) (b n) := Nat.gcd_pos_of_pos_right _ (b_pos n hn)
  have h_le : Nat.gcd (Nat.sqrt ((n + 1) ^ 3)) (b n) ≤ Nat.sqrt ((n + 1) ^ 3) := Nat.le_of_dvd h_term_pos h_gcd_dvd
  exact Nat.div_pos h_le h_gcd_pos

lemma a_ge_two (n : ℕ) (hn : 0 < n) (ha1 : a n ≠ 1) : 2 ≤ a n := by
  have h := a_ge_one n hn
  omega

/--
Conjecture 1 from OEIS A323359: This sequence consists only of 1's and primes.
-/
theorem oeis_323359_conjecture_1 :
  ∀ (n : ℕ), 0 < n → (a n = 1 ∨ Nat.Prime (a n)) := by
  sorry
