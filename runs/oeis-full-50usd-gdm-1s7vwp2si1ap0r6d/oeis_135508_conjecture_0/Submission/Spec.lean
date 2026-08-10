import FormalConjectures.Util.ProblemImports

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
    -- We rely on the fact that x_seq n divides x_seq (n+1), which is a known property of the sequence.
    -- Since n : ℕ, the division is integer division.
    let x_n_plus_1 := x_seq (n + 1)
    let x_n := x_seq n

    -- The fact that x_seq n divides x_seq (n+1) means that the division is exact.
    -- The final result is always a natural number.
    (x_n_plus_1 / x_n) - 2

theorem x_seq_pos (n : ℕ) (h : n > 0) : x_seq n > 0 := by
  induction n with
  | zero => contradiction
  | succ n ih =>
    cases n with
    | zero => decide
    | succ n =>
      have ih_val : x_seq (n + 1) > 0 := ih (Nat.succ_pos n)
      have h_eq : x_seq (n + 1 + 1) = 2 * x_seq (n + 1) + Nat.lcm (x_seq (n + 1)) (n + 2) := rfl
      omega

theorem x_seq_step (n : ℕ) : x_seq (n + 2) = x_seq (n + 1) * (2 + (n + 2) / Nat.gcd (x_seq (n + 1)) (n + 2)) := by
  have h_eq : x_seq (n + 2) = 2 * x_seq (n + 1) + (x_seq (n + 1) * (n + 2)) / Nat.gcd (x_seq (n + 1)) (n + 2) := rfl
  rw [h_eq]
  let A := x_seq (n + 1)
  let B := n + 2
  let G := Nat.gcd A B
  have hG : G ∣ B := Nat.gcd_dvd_right A B
  rw [Nat.mul_div_assoc A hG]
  ring

theorem x_seq_dvd_succ (n : ℕ) (h : n > 0) : x_seq n ∣ x_seq (n + 1) := by
  cases n with
  | zero => contradiction
  | succ n =>
    have h_eq : x_seq (n + 1 + 1) = 2 * x_seq (n + 1) + Nat.lcm (x_seq (n + 1)) (n + 2) := rfl
    rw [h_eq]
    apply dvd_add
    · exact dvd_mul_left (x_seq (n + 1)) 2
    · exact Nat.dvd_lcm_left (x_seq (n + 1)) (n + 2)

theorem x_seq_dvd_of_le (a b : ℕ) (ha : a > 0) (h : a ≤ b) : x_seq a ∣ x_seq b := by
  induction b, h using Nat.le_induction with
  | base => exact dvd_rfl
  | succ b h_le ih =>
    have hb_pos : b > 0 := by omega
    exact dvd_trans ih (x_seq_dvd_succ b hb_pos)

theorem x_seq_step_succ (n : ℕ) (hn : n > 0) : x_seq (n + 1) = x_seq n * (2 + (n + 1) / Nat.gcd (x_seq n) (n + 1)) := by
  cases n with
  | zero => contradiction
  | succ n =>
    have h_eq : x_seq (n + 2) = 2 * x_seq (n + 1) + (x_seq (n + 1) * (n + 2)) / Nat.gcd (x_seq (n + 1)) (n + 2) := rfl
    rw [h_eq]
    let A := x_seq (n + 1)
    let B := n + 2
    let G := Nat.gcd A B
    have hG : G ∣ B := Nat.gcd_dvd_right A B
    rw [Nat.mul_div_assoc A hG]
    ring

theorem A135508_eq (p : ℕ) (hp : Nat.Prime p) : A135508 (p - 1) = p / Nat.gcd (x_seq (p - 1)) p := by
  have hp2 : p ≥ 2 := hp.two_le
  have hn0 : p - 1 ≠ 0 := by omega
  simp [A135508, hn0]
  have h_p_eq2 : p - 1 + 1 = p := Nat.sub_add_cancel (by omega)
  rw [h_p_eq2]
  let m := p - 2
  have h_p_eq : p = m + 2 := by omega
  have h_pm1 : p - 1 = m + 1 := by omega
  have h_step := x_seq_step m
  rw [← h_p_eq] at h_step
  rw [← h_pm1] at h_step
  rw [h_step]
  have h_pos : x_seq (p - 1) > 0 := by
    apply x_seq_pos
    omega
  rw [Nat.mul_div_cancel_left _ h_pos]
  rw [Nat.add_comm]
  exact Nat.add_sub_cancel _ _

theorem x_seq_not_dvd (p : ℕ) (hp : Nat.Prime p) (n : ℕ) (hn : n < p - 2) (h_pos : n > 0) : ¬ (p ∣ x_seq n) := by
  induction n with
  | zero => contradiction
  | succ n ih =>
    cases n with
    | zero =>
      -- n = 1
      intro h_dvd
      have h_x1 : x_seq 1 = 1 := rfl
      rw [h_x1] at h_dvd
      have hp1 : p > 1 := hp.one_lt
      have h_dvd_one := Nat.dvd_one.mp h_dvd
      omega
    | succ n =>
      -- n = succ n + 1 = n + 2
      -- We want to prove ¬ (p ∣ x_seq (n + 2))
      -- hn : n + 2 < p - 2
      intro h_dvd
      have hp2 : p ≥ 2 := hp.two_le
      have ih_val : ¬ (p ∣ x_seq (n + 1)) := by
        apply ih
        · omega
        · omega
      -- We use x_seq_step n
      have h_step := x_seq_step n
      rw [h_step] at h_dvd
      -- p is prime, so p | A * B => p | A or p | B
      have h_dvd_or := hp.dvd_mul.mp h_dvd
      cases h_dvd_or with
      | inl h1 => exact ih_val h1
      | inr h2 =>
        -- p | 2 + (n + 2) / Nat.gcd (x_seq (n + 1)) (n + 2)
        have h_div_le : (n + 2) / Nat.gcd (x_seq (n + 1)) (n + 2) ≤ n + 2 := Nat.div_le_self (n + 2) (Nat.gcd (x_seq (n + 1)) (n + 2))
        have hX_pos : (n + 2) / Nat.gcd (x_seq (n + 1)) (n + 2) ≥ 0 := Nat.zero_le _
        have h_val_lt : 2 + (n + 2) / Nat.gcd (x_seq (n + 1)) (n + 2) < p := by omega
        have h_val_pos : 2 + (n + 2) / Nat.gcd (x_seq (n + 1)) (n + 2) > 0 := by omega
        -- p divides something strictly less than p and positive, contradiction!
        have h_dvd_lt := Nat.le_of_dvd h_val_pos h2
        omega

theorem p_not_dvd_pm1_of_pm2 (p : ℕ) (hp : Nat.Prime p) (hp5 : p ≥ 5) (h_prev : ¬ (p ∣ x_seq (p - 2))) : ¬ (p ∣ x_seq (p - 1)) := by
  have hp2 : p ≥ 2 := hp.two_le
  let m := p - 3
  have h_p_eq : p - 1 = m + 2 := by omega
  have h_pm2 : p - 2 = m + 1 := by omega
  have h_step := x_seq_step m
  rw [← h_p_eq] at h_step
  rw [← h_pm2] at h_step
  -- h_step : x_seq (p - 1) = x_seq (p - 2) * (2 + (p - 1) / Nat.gcd (x_seq (p - 2)) (p - 1))
  intro h_dvd
  rw [h_step] at h_dvd
  have h_or := hp.dvd_mul.mp h_dvd
  cases h_or with
  | inl h1 => exact (h_prev h1).elim
  | inr h2 =>
    generalize hG : Nat.gcd (x_seq (p - 2)) (p - 1) = G
    rw [hG] at h2
    have hG_pos : G > 0 := by
      rw [← hG]
      exact Nat.gcd_pos_of_pos_right _ (by omega)
    have h_div_le : (p - 1) / G ≤ p - 1 := by
      rw [← hG]
      exact Nat.div_le_self (p - 1) (Nat.gcd (x_seq (p - 2)) (p - 1))
    have h_div_pos : (p - 1) / G ≥ 1 := by
      apply Nat.div_pos
      · rw [← hG]
        exact Nat.gcd_le_right _ (by omega)
      · omega
    have h_sum_pos : 2 + (p - 1) / G > 0 := by omega
    have h_sum_le : 2 + (p - 1) / G ≤ p + 1 := by omega
    have h_eq_p : 2 + (p - 1) / G = p := by
      have h_cases : 2 + (p - 1) / G < p ∨ 2 + (p - 1) / G = p ∨ 2 + (p - 1) / G = p + 1 := by omega
      rcases h_cases with h_lt | h_eq | h_eq_p1
      · have h_dvd_lt := Nat.le_of_dvd h_sum_pos h2
        omega
      · exact h_eq
      · -- if 2 + (p-1)/G = p+1, then (p-1)/G = p-1. So G = 1.
        have h_G1 : G = 1 := by
          have h_div : (p - 1) / G = p - 1 := by omega
          have h_mul : p - 1 = G * (p - 1) := by
            have h_temp := Nat.mul_div_cancel' (Nat.gcd_dvd_right (x_seq (p - 2)) (p - 1))
            rw [hG] at h_temp
            rw [h_div] at h_temp
            exact h_temp.symm
          have h_mul_one : 1 * (p - 1) = G * (p - 1) := by omega
          exact Nat.eq_of_mul_eq_mul_right (by omega) h_mul_one.symm
        rw [h_G1] at h2
        rw [Nat.div_one] at h2
        have h_add_eq : 2 + (p - 1) = p + 1 := by omega
        rw [h_add_eq] at h2
        -- p | p + 1 => p | 1
        have h_dvd_one : p ∣ 1 := (Nat.dvd_add_right (dvd_refl p)).mp h2
        have hp1 : p > 1 := hp.one_lt
        have := Nat.le_of_dvd (by omega) h_dvd_one
        omega
    have h_div_eq : (p - 1) / G = p - 2 := by omega
    have h_mul : p - 1 = G * (p - 2) := by
      have h_temp := Nat.mul_div_cancel' (Nat.gcd_dvd_right (x_seq (p - 2)) (p - 1))
      rw [hG] at h_temp
      rw [h_div_eq] at h_temp
      exact h_temp.symm
    have h_G_cases : G = 0 ∨ G = 1 ∨ G ≥ 2 := by omega
    rcases h_G_cases with hG0 | hG1 | hG2
    · omega
    · rw [hG1] at h_mul
      omega
    · have h_le : 2 * (p - 2) ≤ G * (p - 2) := Nat.mul_le_mul_right (p - 2) hG2
      rw [← h_mul] at h_le
      omega

theorem p_dvd_x_pm2_iff (p : ℕ) (hp : Nat.Prime p) (hp5 : p ≥ 5) : (p ∣ x_seq (p - 2)) ↔ Nat.gcd (x_seq (p - 3)) (p - 2) = 1 := by
  have hp2 : p ≥ 2 := hp.two_le
  let m := p - 4
  have h_p_eq : p - 2 = m + 2 := by omega
  have h_pm3 : p - 3 = m + 1 := by omega
  have h_step := x_seq_step m
  rw [← h_p_eq] at h_step
  rw [← h_pm3] at h_step
  -- h_step : x_seq (p - 2) = x_seq (p - 3) * (2 + (p - 2) / Nat.gcd (x_seq (p - 3)) (p - 2))
  constructor
  · intro h_dvd
    have h_not_dvd_pm3 : ¬ (p ∣ x_seq (p - 3)) := by
      apply x_seq_not_dvd p hp (p - 3)
      · omega
      · omega
    rw [h_step] at h_dvd
    have h_or := hp.dvd_mul.mp h_dvd
    cases h_or with
    | inl h1 => exact (h_not_dvd_pm3 h1).elim
    | inr h2 =>
      let G := Nat.gcd (x_seq (p - 3)) (p - 2)
      have hG_pos : G > 0 := Nat.gcd_pos_of_pos_right _ (by omega)
      have h_div_le : (p - 2) / G ≤ p - 2 := Nat.div_le_self (p - 2) G
      have h_div_pos : (p - 2) / G ≥ 1 := by
        -- Since G divides p - 2, and p - 2 > 0, (p - 2) / G >= 1
        apply Nat.div_pos
        · exact Nat.gcd_le_right _ (by omega)
        · omega
      have h_sum_pos : 2 + (p - 2) / G > 0 := by omega
      have h_sum_le : 2 + (p - 2) / G ≤ p := by omega
      have h_eq_p : 2 + (p - 2) / G = p := by
        have h_le_p : 2 + (p - 2) / G < p ∨ 2 + (p - 2) / G = p := by omega
        cases h_le_p with
        | inl h_lt =>
          have h_dvd_lt := Nat.le_of_dvd h_sum_pos h2
          omega
        | inr h_eq => exact h_eq
      have h_div_eq : (p - 2) / G = p - 2 := by omega
      -- G must be 1
      have h_mul : p - 2 = G * (p - 2) := by
        have h_temp := Nat.mul_div_cancel' (Nat.gcd_dvd_right (x_seq (p - 3)) (p - 2))
        rw [h_div_eq] at h_temp
        exact h_temp.symm
      have h_mul_one : 1 * (p - 2) = G * (p - 2) := by omega
      have h_pm2_pos : p - 2 > 0 := by omega
      exact Nat.eq_of_mul_eq_mul_right h_pm2_pos h_mul_one.symm
  · intro hG1
    rw [h_step]
    rw [hG1]
    simp
    -- x_seq (p - 2) = x_seq (p - 3) * p
    apply dvd_mul_of_dvd_right
    have : 2 + (p - 2) = p := by omega
    rw [this]

def g_seq (q : ℕ) : ℕ → ℕ
| 0 => 1
| i + 1 => Nat.gcd (x_seq (g_seq q i * (q - 2) - 1)) (g_seq q i * (q - 2))

theorem g_seq_pos (q : ℕ) (hq3 : q ≥ 3) (i : ℕ) : g_seq q i > 0 := by
  induction i with
  | zero =>
    unfold g_seq
    decide
  | succ i ih =>
    unfold g_seq
    apply Nat.gcd_pos_of_pos_right
    have hq2 : q - 2 > 0 := by omega
    exact Nat.mul_pos ih hq2

theorem g_seq_dvd_succ (q : ℕ) (i : ℕ) (hih : g_seq q i ∣ x_seq (g_seq q i * (q - 2) - 1)) : g_seq q i ∣ g_seq q (i + 1) := by
  rw [g_seq]
  apply Nat.dvd_gcd
  · exact hih
  · exact dvd_mul_right (g_seq q i) (q - 2)

theorem g_seq_prop1 (q : ℕ) (i : ℕ) : g_seq q i ∣ (q - 2)^i := by
  induction i with
  | zero =>
    simp [g_seq]
  | succ i ih =>
    simp [g_seq]
    have h_dvd : g_seq q i * (q - 2) ∣ (q - 2) ^ i * (q - 2) := Nat.mul_dvd_mul_right ih (q - 2)
    have h_pow_eq : (q - 2) ^ (i + 1) = (q - 2) ^ i * (q - 2) := by
      rw [pow_succ]
    rw [← h_pow_eq] at h_dvd
    exact dvd_trans (Nat.gcd_dvd_right _ _) h_dvd

theorem g_seq_prop2 (q : ℕ) (hq5 : q ≥ 5) (i : ℕ) : g_seq q i ∣ x_seq (g_seq q i * (q - 2) - 1) := by
  induction i with
  | zero =>
    rw [g_seq]
    exact one_dvd _
  | succ i ih =>
    have h_dvd_succ : g_seq q i ∣ g_seq q (i + 1) := g_seq_dvd_succ q i ih
    have hq3 : q ≥ 3 := by omega
    have h_pos_i1 : g_seq q (i + 1) > 0 := g_seq_pos q hq3 (i + 1)
    have h_le_g : g_seq q i ≤ g_seq q (i + 1) := Nat.le_of_dvd h_pos_i1 h_dvd_succ
    have h_pos_i0 : g_seq q i > 0 := g_seq_pos q hq3 i
    have h_idx_pos : g_seq q i * (q - 2) - 1 > 0 := by
      have h1 : 1 ≤ g_seq q i := h_pos_i0
      have h2 : 3 ≤ q - 2 := by omega
      have h_mul_ge : 3 ≤ g_seq q i * (q - 2) := Nat.mul_le_mul h1 h2
      omega
    have h_idx_le : g_seq q i * (q - 2) - 1 ≤ g_seq q (i + 1) * (q - 2) - 1 := by
      have h_mul_le : g_seq q i * (q - 2) ≤ g_seq q (i + 1) * (q - 2) := Nat.mul_le_mul_right (q - 2) h_le_g
      omega
    have h_x_dvd := x_seq_dvd_of_le (g_seq q i * (q - 2) - 1) (g_seq q (i + 1) * (q - 2) - 1) h_idx_pos h_idx_le
    have h_g_dvd_prev : g_seq q (i + 1) ∣ x_seq (g_seq q i * (q - 2) - 1) := by
      rw [g_seq]
      exact Nat.gcd_dvd_left _ _
    exact dvd_trans h_g_dvd_prev h_x_dvd

theorem g_seq_strict_mono (q : ℕ) (hq : Nat.Prime q) (hq5 : q ≥ 5) (h_not : ¬ (q ∣ x_seq (q^2 - 1))) (i : ℕ) (hi : g_seq q i < q - 2) : g_seq q (i + 1) > g_seq q i := by
  have _ := hq
  have h_dvd_succ : g_seq q i ∣ g_seq q (i + 1) := by
    have h_ih : g_seq q i ∣ x_seq (g_seq q i * (q - 2) - 1) := g_seq_prop2 q hq5 i
    exact g_seq_dvd_succ q i h_ih
  have hq3 : q ≥ 3 := by omega
  have h_pos_i1 : g_seq q (i + 1) > 0 := g_seq_pos q hq3 (i + 1)
  have h_pos_i0 : g_seq q i > 0 := g_seq_pos q hq3 i
  by_contra h_not_gt
  have h_eq : g_seq q (i + 1) = g_seq q i := by
    have : g_seq q i ≤ g_seq q (i + 1) := Nat.le_of_dvd h_pos_i1 h_dvd_succ
    omega
  let k := g_seq q i * (q - 2) - 1
  have h_idx_pos : g_seq q i * (q - 2) - 1 > 0 := by
    have h1 : 1 ≤ g_seq q i := h_pos_i0
    have h2 : 3 ≤ q - 2 := by omega
    have h_mul_ge : 3 ≤ g_seq q i * (q - 2) := Nat.mul_le_mul h1 h2
    omega
  have h_k_plus_1 : k + 1 = g_seq q i * (q - 2) := Nat.sub_add_cancel (by omega)
  have h_step := x_seq_step_succ k h_idx_pos
  have h_gcd_eq : Nat.gcd (x_seq k) (k + 1) = g_seq q i := by
    have h_g_eq : g_seq q (i + 1) = Nat.gcd (x_seq k) (g_seq q i * (q - 2)) := by rw [g_seq]
    rw [← h_k_plus_1] at h_g_eq
    rw [← h_g_eq]
    exact h_eq
  rw [h_gcd_eq] at h_step
  rw [h_k_plus_1] at h_step
  have h_div_eq : g_seq q i * (q - 2) / g_seq q i = q - 2 := Nat.mul_div_cancel_left _ h_pos_i0
  rw [h_div_eq] at h_step
  have h_step_simp : x_seq (g_seq q i * (q - 2)) = x_seq k * q := by
    rw [h_step]
    have : 2 + (q - 2) = q := by omega
    rw [this]
  have hq_dvd_k1 : q ∣ x_seq (g_seq q i * (q - 2)) := by
    rw [h_step_simp]
    exact dvd_mul_left q (x_seq k)
  have h_le_sq : g_seq q i * (q - 2) ≤ q^2 - 1 := by
    have h_le_qm3 : g_seq q i ≤ q - 3 := by omega
    have h_mul_le : g_seq q i * (q - 2) ≤ (q - 3) * (q - 2) := Nat.mul_le_mul_right (q - 2) h_le_qm3
    have h_qm3_le : (q - 3) * (q - 2) ≤ q^2 - 1 := by
      have h1 : (q - 3) * (q - 2) ≤ (q - 3) * q := Nat.mul_le_mul_left (q - 3) (by omega)
      have h2 : (q - 3) * q = q * q - 3 * q := Nat.sub_mul q 3 q
      rw [h2] at h1
      have h3 : 3 * q ≥ 15 := by omega
      have h_pow2 : q^2 = q * q := by ring
      omega
    exact le_trans h_mul_le h_qm3_le
  have h_x_dvd : x_seq (g_seq q i * (q - 2)) ∣ x_seq (q^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · exact h_le_sq
  have hq_dvd_final : q ∣ x_seq (q^2 - 1) := dvd_trans hq_dvd_k1 h_x_dvd
  exact h_not hq_dvd_final

theorem pow_two_ge_self (m : ℕ) : 2^m ≥ m := by
  induction m with
  | zero => omega
  | succ m ih =>
    have h_pow : 2^(m + 1) = 2^m * 2 := pow_succ 2 m
    have h_pos : 2^m ≥ 1 := by
      induction m with
      | zero => omega
      | succ m ih2 =>
        have : 2^(m + 1) = 2^m * 2 := pow_succ 2 m
        omega
    omega

theorem g_seq_growth (q : ℕ) (hq : Nat.Prime q) (hq5 : q ≥ 5) (h_not : ¬ (q ∣ x_seq (q^2 - 1))) (i : ℕ) (hi : ∀ k ≤ i, g_seq q k < q - 2) : g_seq q i ≥ 2^i := by
  induction i with
  | zero =>
    rw [g_seq]
    omega
  | succ i ih =>
    have hi_i : ∀ k ≤ i, g_seq q k < q - 2 := fun k hk => hi k (by omega)
    have ih_val := ih hi_i
    have h_lt : g_seq q i < q - 2 := hi i (by omega)
    have h_gt := g_seq_strict_mono q hq hq5 h_not i h_lt
    have h_ih_dvd : g_seq q i ∣ x_seq (g_seq q i * (q - 2) - 1) := g_seq_prop2 q hq5 i
    have h_dvd : g_seq q i ∣ g_seq q (i + 1) := g_seq_dvd_succ q i h_ih_dvd
    have hq3 : q ≥ 3 := by omega
    have h_pos : g_seq q i > 0 := g_seq_pos q hq3 i
    have h_factor : g_seq q (i + 1) ≥ 2 * g_seq q i := by
      rcases h_dvd with ⟨c, hc⟩
      have hc2 : c ≥ 2 := by
        by_cases hc0 : c = 0
        · subst hc0; omega
        · by_cases hc1 : c = 1
          · subst hc1; omega
          · omega
      rw [hc]
      rw [Nat.mul_comm]
      exact Nat.mul_le_mul_right (g_seq q i) hc2
    have h_pow_eq : 2^(i + 1) = 2^i * 2 := pow_succ 2 i
    rw [h_pow_eq]
    omega

lemma find_smallest_ge (y : ℕ → ℕ) (M : ℕ) (k : ℕ) (hk : y k ≥ M) : ∃ j ≤ k, y j ≥ M ∧ ∀ i < j, y i < M := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases h_ex : ∃ j' < k, y j' ≥ M
    · rcases h_ex with ⟨j', hj'_lt, hj'_ge⟩
      rcases ih j' hj'_lt hj'_ge with ⟨j, hj_le, hj_ge, hj_min⟩
      use j
      refine ⟨by omega, hj_ge, hj_min⟩
    · use k
      refine ⟨by omega, hk, ?_⟩
      intro i hi
      by_contra h_ge
      push_neg at h_ge
      exact h_ex ⟨i, hi, h_ge⟩

theorem g_seq_has_large (q : ℕ) (hq : Nat.Prime q) (hq5 : q ≥ 5) (h_not : ¬ (q ∣ x_seq (q^2 - 1))) : ∃ k ≤ q - 2, g_seq q k ≥ q - 2 := by
  by_contra h_all_lt
  push_neg at h_all_lt
  have h_growth := g_seq_growth q hq hq5 h_not (q - 2) h_all_lt
  have h_bound := h_all_lt (q - 2) (by omega)
  have h_ge := pow_two_ge_self (q - 2)
  omega

mutual
theorem prime_dvd_x_seq_sq_sub_one (q : ℕ) (hq : Nat.Prime q) : q ∣ x_seq (q^2 - 1) := by
  have hq2 : q ≥ 2 := hq.two_le
  have h_cases : q = 2 ∨ q = 3 ∨ q ≥ 5 := by
    rcases hq.eq_two_or_odd with rfl | hq_odd
    · left; rfl
    · right
      have : q % 2 = 1 := hq_odd
      omega
  rcases h_cases with rfl | rfl | hq5
  · decide
  · decide
  · by_contra h_not
    have h_large := g_seq_has_large q hq hq5 h_not
    rcases h_large with ⟨k, hk_le, hk_ge⟩
    rcases find_smallest_ge (g_seq q) (q - 2) k hk_ge with ⟨j, hj_le, hj_ge, hj_min⟩
    have hj_pos : j > 0 := by
      by_contra hj0
      have : j = 0 := by omega
      subst this
      have h_g0 : g_seq q 0 = 1 := rfl
      omega
    have h_prev_lt : g_seq q (j - 1) < q - 2 := hj_min (j - 1) (by omega)
    have h_strict := g_seq_strict_mono q hq hq5 h_not (j - 1) h_prev_lt
    have h_eq : j - 1 + 1 = j := Nat.sub_add_cancel hj_pos
    rw [h_eq] at h_strict
    have h_ge_j : g_seq q j ≥ q - 2 := hj_ge
    have h_dvd : g_seq q (j - 1) ∣ g_seq q j := by
      have h_ih : g_seq q (j - 1) ∣ x_seq (g_seq q (j - 1) * (q - 2) - 1) := g_seq_prop2 q hq5 (j - 1)
      have h_dvd_succ := g_seq_dvd_succ q (j - 1) h_ih
      have h_eq : j - 1 + 1 = j := Nat.sub_add_cancel hj_pos
      rw [h_eq] at h_dvd_succ
      exact h_dvd_succ
    have h_dvd_right : g_seq q j ∣ g_seq q (j - 1) * (q - 2) := by
      have h_eq_j : j = j - 1 + 1 := (Nat.sub_add_cancel hj_pos).symm
      have h_g_eq : g_seq q j = Nat.gcd (x_seq (g_seq q (j - 1) * (q - 2) - 1)) (g_seq q (j - 1) * (q - 2)) := by
        conv_lhs => rw [h_eq_j]
        rfl
      rw [h_g_eq]
      exact Nat.gcd_dvd_right _ _
    have h_le_sq : g_seq q (j - 1) * (q - 2) ≤ q^2 - 1 := by
      have h_le_qm3 : g_seq q (j - 1) ≤ q - 3 := by omega
      have h_mul_le : g_seq q (j - 1) * (q - 2) ≤ (q - 3) * (q - 2) := Nat.mul_le_mul_right (q - 2) h_le_qm3
      have h_qm3_le : (q - 3) * (q - 2) ≤ q^2 - 1 := by
        have h1 : (q - 3) * (q - 2) ≤ (q - 3) * q := Nat.mul_le_mul_left (q - 3) (by omega)
        have h2 : (q - 3) * q = q * q - 3 * q := Nat.sub_mul q 3 q
        rw [h2] at h1
        have h3 : 3 * q ≥ 15 := by omega
        have h_pow2 : q^2 = q * q := by ring
        omega
      exact le_trans h_mul_le h_qm3_le
    have h_g_dvd_prev : g_seq q j ∣ x_seq (g_seq q (j - 1) * (q - 2) - 1) := by
      have h_eq_j : j = j - 1 + 1 := (Nat.sub_add_cancel hj_pos).symm
      have h_g_eq : g_seq q j = Nat.gcd (x_seq (g_seq q (j - 1) * (q - 2) - 1)) (g_seq q (j - 1) * (q - 2)) := by
        conv_lhs => rw [h_eq_j]
        rfl
      rw [h_g_eq]
      exact Nat.gcd_dvd_left _ _
    have h_idx_pos : g_seq q (j - 1) * (q - 2) - 1 > 0 := by
      have h1 : 1 ≤ g_seq q (j - 1) := g_seq_pos q (by omega) (j - 1)
      have h2 : 3 ≤ q - 2 := by omega
      have h_mul_ge : 3 ≤ g_seq q (j - 1) * (q - 2) := Nat.mul_le_mul h1 h2
      omega
    have h_le_sq_sub_one : g_seq q (j - 1) * (q - 2) - 1 ≤ q^2 - 1 := by omega
    have h_x_dvd : x_seq (g_seq q (j - 1) * (q - 2) - 1) ∣ x_seq (q^2 - 1) := x_seq_dvd_of_le (g_seq q (j - 1) * (q - 2) - 1) (q^2 - 1) h_idx_pos h_le_sq_sub_one
    have h_g_dvd_final : g_seq q j ∣ x_seq (q^2 - 1) := dvd_trans h_g_dvd_prev h_x_dvd
    by_cases hq_pm2 : Nat.Prime (q - 2)
    · -- Case 1: q - 2 is prime
      have h_g1_cases : g_seq q 1 = 1 ∨ g_seq q 1 = q - 2 := by
        have h_g1_dvd : g_seq q 1 ∣ q - 2 := by
          have := g_seq_prop1 q 1
          simp at this
          exact this
        rcases (Nat.dvd_prime hq_pm2).mp h_g1_dvd with h_g1_1 | h_g1_q
        · left; exact h_g1_1
        · right; exact h_g1_q
      have h_g1_not1 : g_seq q 1 ≠ 1 := by
        have h_mono := g_seq_strict_mono q hq hq5 h_not 0 (by
          have : g_seq q 0 = 1 := rfl
          omega)
        have h_0_1 : 0 + 1 = 1 := rfl
        rw [h_0_1] at h_mono
        have : g_seq q 0 = 1 := rfl
        omega
      have h_g1_eq : g_seq q 1 = q - 2 := by
        rcases h_g1_cases with h_g1_1 | h_g1_q
        · exact (h_g1_not1 h_g1_1).elim
        · exact h_g1_q
      have hj1 : j = 1 := by
        by_contra hj_gt1
        have : 1 < j := by omega
        have h_lt := hj_min 1 this
        omega
      have h_pm2_dvd : q - 2 ∣ x_seq (q - 3) := by
        subst hj1
        have h_g0 : g_seq q 0 = 1 := rfl
        have h_g1 : g_seq q 1 = q - 2 := h_g1_eq
        rw [h_g0, h_g1] at h_g_dvd_prev
        have : 1 * (q - 2) - 1 = q - 3 := by omega
        rw [this] at h_g_dvd_prev
        exact h_g_dvd_prev
      have hq_not5 : q ≠ 5 := by
        intro hq5_eq
        subst hq5_eq
        have h_dvd : 5 ∣ x_seq (5^2 - 1) := by
          have : 5^2 - 1 = 24 := rfl
          rw [this]
          decide
        exact h_not h_dvd
      have hq_not7 : q ≠ 7 := by
        intro hq7_eq
        subst hq7_eq
        have h_dvd : 7 ∣ x_seq (7^2 - 1) := by
          have : 7^2 - 1 = 48 := rfl
          rw [this]
          decide
        exact h_not h_dvd
      have hq_not9 : q ≠ 9 := by
        intro hq9_eq
        subst hq9_eq
        have : ¬ Nat.Prime 9 := by decide
        exact this hq
      have hq11 : q ≥ 11 := by
        rcases hq.eq_two_or_odd with rfl | hq_odd
        · omega
        · have hq_odd' : q % 2 = 1 := hq_odd
          omega
      have h_mod3 : q % 3 = 0 ∨ q % 3 = 1 ∨ q % 3 = 2 := by omega
      rcases h_mod3 with h0 | h1 | h2
      · have : 3 ∣ q := Nat.dvd_of_mod_eq_zero h0
        rcases (Nat.dvd_prime hq).mp this with h_3_1 | h_3_q
        · contradiction
        · omega
      · have h_pm4_mod : (q - 4) % 3 = 0 := by omega
        have h3_dvd : 3 ∣ q - 4 := Nat.dvd_of_mod_eq_zero h_pm4_mod
        have h_pm4_ge : q - 4 ≥ 6 := by omega
        have h_not_prime : ¬ Nat.Prime (q - 4) := by
          intro hp_pm4
          rcases (Nat.dvd_prime hp_pm4).mp h3_dvd with h_3_1 | h_3_eq
          · contradiction
          · omega
        let p := q - 2
        have hp_prime : Nat.Prime p := hq_pm2
        have hp5 : p ≥ 5 := by omega
        have hc : ¬ Nat.Prime (p - 2) := h_not_prime
        have h_dvd_p := min_fac_dvd_x_seq_pm3 p hp_prime hp5 hc
        have h_iff := p_dvd_x_pm2_iff p hp_prime hp5
        have h_not_dvd_pm2 : ¬ (p ∣ x_seq (p - 2)) := by
          rw [h_iff]
          intro h_gcd
          let r := Nat.minFac (p - 2)
          have hr_prime : Nat.Prime r := Nat.minFac_prime (by omega)
          have hr_dvd_pm2 : r ∣ p - 2 := Nat.minFac_dvd (p - 2)
          have hr_dvd_pm3 : r ∣ x_seq (p - 3) := h_dvd_p
          have hr_gcd : r ∣ Nat.gcd (x_seq (p - 3)) (p - 2) := Nat.dvd_gcd hr_dvd_pm3 hr_dvd_pm2
          rw [h_gcd] at hr_gcd
          have : r ∣ 1 := hr_gcd
          have : r ≤ 1 := Nat.le_of_dvd (by decide) this
          have : r ≥ 2 := hr_prime.two_le
          omega
        have h_not_dvd_pm1 := p_not_dvd_pm1_of_pm2 p hp_prime hp5 h_not_dvd_pm2
        exact h_not_dvd_pm1 h_pm2_dvd
      · have h_pm2_mod : (q - 2) % 3 = 0 := by omega
        have h3_dvd : 3 ∣ q - 2 := Nat.dvd_of_mod_eq_zero h_pm2_mod
        rcases (Nat.dvd_prime hq_pm2).mp h3_dvd with h_3_1 | h_3_eq
        · contradiction
        · omega
    · -- Case 2: q - 2 is composite
      let p' := Nat.minFac (q - 2)
      have hp'_prime : Nat.Prime p' := Nat.minFac_prime (by omega)
      have hp'_dvd_pm2 : p' ∣ q - 2 := Nat.minFac_dvd (q - 2)
      have hp'_dvd_pm3 := min_fac_dvd_x_seq_pm3 q hq hq5 hq_pm2
      have h_dvd_g : ∀ i ≥ 1, p' ∣ g_seq q i := by
        intro i hi
        induction i with
        | zero => contradiction
        | succ i ih =>
          by_cases hi0 : i = 0
          · subst hi0
            have h_g1 : g_seq q 1 = Nat.gcd (x_seq (q - 3)) (q - 2) := by
              have : g_seq q 1 = Nat.gcd (x_seq (g_seq q 0 * (q - 2) - 1)) (g_seq q 0 * (q - 2)) := rfl
              rw [this]
              have h_g0 : g_seq q 0 = 1 := rfl
              rw [h_g0]
              simp
              have : q - 2 - 1 = q - 3 := by omega
              rw [this]
            rw [h_g1]
            exact Nat.dvd_gcd hp'_dvd_pm3 hp'_dvd_pm2
          · have hi_ge1 : i ≥ 1 := by omega
            have ih_val : p' ∣ g_seq q i := ih hi_ge1
            have h_g_eq : g_seq q (i + 1) = Nat.gcd (x_seq (g_seq q i * (q - 2) - 1)) (g_seq q i * (q - 2)) := rfl
            rw [h_g_eq]
            apply Nat.dvd_gcd
            · let K := g_seq q i * (q - 2) - 1
              have h_q2_pos : q - 2 > 0 := by omega
              have hp'_ge2 : p' ≥ 2 := hp'_prime.two_le
              have h_g_pos : g_seq q i > 0 := g_seq_pos q (by omega) i
              have hp'_pos : p' > 0 := by omega
              have h_mul_ge : g_seq q i * (q - 2) ≥ p' * p' := by
                rcases ih_val with ⟨c1, hc1⟩
                rcases hp'_dvd_pm2 with ⟨c2, hc2⟩
                have hc1_pos : c1 > 0 := by
                  by_contra hc0
                  have : c1 = 0 := by omega
                  subst this; omega
                have hc2_pos : c2 > 0 := by
                  by_contra hc0
                  have : c2 = 0 := by omega
                  subst this; omega
                rw [hc1, hc2]
                have h_ring : (p' * c1) * (p' * c2) = (p' * p') * (c1 * c2) := by ring
                rw [h_ring]
                have h_c12 : c1 * c2 ≥ 1 := Nat.mul_le_mul hc1_pos hc2_pos
                have h_ge : (p' * p') * 1 ≤ (p' * p') * (c1 * c2) := Nat.mul_le_mul_left (p' * p') h_c12
                rw [Nat.mul_one] at h_ge
                exact h_ge
              have h_K_ge : K ≥ p'^2 - 1 := by
                have : p'^2 = p' * p' := by ring
                omega
              have h_p'_sq_pos : p'^2 - 1 > 0 := by
                have : p' * p' ≥ 4 := Nat.mul_le_mul hp'_ge2 hp'_ge2
                have : p'^2 = p' * p' := by ring
                omega
              have h_dvd_x := x_seq_dvd_of_le (p'^2 - 1) K h_p'_sq_pos h_K_ge
              have hp'_dvd_sq : p' ∣ x_seq (p'^2 - 1) := prime_dvd_x_seq_sq_sub_one p' hp'_prime
              exact dvd_trans hp'_dvd_sq h_dvd_x
            · exact dvd_mul_of_dvd_right hp'_dvd_pm2 (g_seq q i)
      have hq_dvd_g_j : p' ∣ g_seq q j := h_dvd_g j (by omega)
      have h_g_dvd_final_p : p' ∣ x_seq (q^2 - 1) := dvd_trans hq_dvd_g_j h_g_dvd_final
      have h_gcd_1 : Nat.gcd (x_seq (q^2 - 1)) q = 1 := by
        have h_prime_dvd : ∀ d, d ∣ q → d = 1 ∨ d = q := by
          intro d hd
          rcases (Nat.dvd_prime hq).mp hd with h1 | h2
          · left; exact h1
          · right; exact h2
        have h_dvd_q : Nat.gcd (x_seq (q^2 - 1)) q ∣ q := Nat.gcd_dvd_right _ _
        rcases h_prime_dvd _ h_dvd_q with h1 | h2
        · exact h1
        · have h_dvd : Nat.gcd (x_seq (q^2 - 1)) q ∣ x_seq (q^2 - 1) := Nat.gcd_dvd_left _ _
          rw [h2] at h_dvd
          exact (h_not h_dvd).elim
      have hq_not_dvd_pm2 : ¬ (q ∣ x_seq (q - 2)) := by
        have h_iff := p_dvd_x_pm2_iff q hq hq5
        rw [h_iff]
        intro h_gcd
        have hp'_dvd_g1 : p' ∣ g_seq q 1 := h_dvd_g 1 (by omega)
        have h_g1 : g_seq q 1 = Nat.gcd (x_seq (q - 3)) (q - 2) := by
          have h_g0 : g_seq q 0 = 1 := rfl
          have : g_seq q 1 = Nat.gcd (x_seq (g_seq q 0 * (q - 2) - 1)) (g_seq q 0 * (q - 2)) := rfl
          rw [this, h_g0]
          simp
          have : q - 2 - 1 = q - 3 := by omega
          rw [this]
        rw [h_g1] at hp'_dvd_g1
        rw [h_gcd] at hp'_dvd_g1
        have : p' ∣ 1 := hp'_dvd_g1
        have : p' ≤ 1 := Nat.le_of_dvd (by decide) this
        have : p' ≥ 2 := hp'_prime.two_le
        omega
      have hq_not_dvd_pm1 : ¬ (q ∣ x_seq (q - 1)) := p_not_dvd_pm1_of_pm2 q hq hq5 hq_not_dvd_pm2
      exact hq_not_dvd_pm1
termination_by 2 * q + 1
decreasing_by
  · omega
  · omega
  · have h_le : (q - 2).minFac ≤ q - 2 := Nat.minFac_le (by omega)
    omega

theorem min_fac_dvd_x_seq_pm3 (p : ℕ) (hp : Nat.Prime p) (hp5 : p ≥ 5) (hc : ¬ Nat.Prime (p - 2)) : Nat.minFac (p - 2) ∣ x_seq (p - 3) := by
  have _ := hp
  let q := Nat.minFac (p - 2)
  have hq_prime : Nat.Prime q := Nat.minFac_prime (by omega)
  have h_comp : ¬ Nat.Prime (p - 2) := hc
  have h_pm2_ge2 : p - 2 ≥ 2 := by omega
  have h_le_pm3 : q^2 - 1 ≤ p - 3 := by
    have h_pow : q^2 = q * q := by ring
    rw [h_pow]
    have hq_dvd : q ∣ p - 2 := Nat.minFac_dvd (p - 2)
    rcases hq_dvd with ⟨k, hk⟩
    have hk_pos : k > 1 := by
      by_contra hk1
      have : k = 0 ∨ k = 1 := by omega
      rcases this with rfl | rfl
      · omega
      · rw [mul_one] at hk
        have : p - 2 = q := hk
        rw [this] at h_comp
        exact h_comp hq_prime
    have hk_ge : k ≥ q := by
      by_contra hk_lt
      have h_prime_k : ∃ r, Nat.Prime r ∧ r ∣ k := by
        use Nat.minFac k
        exact ⟨Nat.minFac_prime (by omega), Nat.minFac_dvd k⟩
      rcases h_prime_k with ⟨r, hr_prime, hr_dvd⟩
      have hr_dvd_pm2 : r ∣ p - 2 := by
        rw [hk]
        exact dvd_mul_of_dvd_right hr_dvd q
      have hr_ge_q : r ≥ q := Nat.minFac_le_of_dvd hr_prime.two_le hr_dvd_pm2
      have hr_le_k : r ≤ k := Nat.le_of_dvd (by omega) hr_dvd
      omega
    have hq_sq_le : q * q ≤ p - 2 := by
      rw [hk]
      exact Nat.mul_le_mul_left q hk_ge
    have h_q_ge2 : q ≥ 2 := hq_prime.two_le
    have h_sq_ge1 : q * q ≥ 1 := by
      have : q * q ≥ 4 := Nat.mul_le_mul h_q_ge2 h_q_ge2
      omega
    omega
  have hq_dvd_sq : q ∣ x_seq (q^2 - 1) := prime_dvd_x_seq_sq_sub_one q hq_prime
  have h_idx_pos : q^2 - 1 > 0 := by
    have h_prime_ge2 : q ≥ 2 := hq_prime.two_le
    have h_sq_ge4 : q^2 ≥ 4 := by
      have h_pow : q^2 = q * q := by ring
      rw [h_pow]
      have : q * q ≥ 4 := Nat.mul_le_mul h_prime_ge2 h_prime_ge2
      omega
    omega
  have h_x_dvd : x_seq (q^2 - 1) ∣ x_seq (p - 3) := x_seq_dvd_of_le (q^2 - 1) (p - 3) h_idx_pos h_le_pm3
  exact dvd_trans hq_dvd_sq h_x_dvd
termination_by 2 * p
decreasing_by
  have hq_le : q ≤ p - 2 := Nat.minFac_le (by omega)
  omega
end


/--
Conjecture: For prime p such that p-2 is not a prime, a(p-1) = p.
p-2 in natural numbers is $\max(0, p-2)$.
A prime $p$ such that $p-2$ is not a prime means $p$ is not the larger element of a twin prime pair, except for $p=3$ where $p-2=1$ (not prime) and $p=2$ where $p-2=0$ (not prime).
-/
theorem oeis_135508_conjecture_0 :
  ∀ p : ℕ, Nat.Prime p → ¬ (Nat.Prime (p - 2)) → A135508 (p - 1) = p := by
  intro p hp hc
  have h_cases : p = 2 ∨ p = 3 ∨ p ≥ 5 := by
    rcases hp.eq_two_or_odd with rfl | hp_odd
    · left; rfl
    · right
      have hp2 : p ≥ 2 := hp.two_le
      omega
  rcases h_cases with rfl | rfl | hp5
  · decide
  · decide
  · -- p >= 5
    have h_eq := A135508_eq p hp
    rw [h_eq]
    have h_gcd_eq : Nat.gcd (x_seq (p - 1)) p = 1 := by
      have h_prime_dvd : ∀ d, d ∣ p → d = 1 ∨ d = p := by
        intro d hd
        rcases (Nat.dvd_prime hp).mp hd with h1 | h2
        · left; exact h1
        · right; exact h2
      have h_dvd_p : Nat.gcd (x_seq (p - 1)) p ∣ p := Nat.gcd_dvd_right _ _
      rcases h_prime_dvd _ h_dvd_p with h1 | h2
      · exact h1
      · -- if gcd = p, then p ∣ x_seq (p - 1)
        have hp_dvd_pm1 : p ∣ x_seq (p - 1) := by
          have h_dvd : Nat.gcd (x_seq (p - 1)) p ∣ x_seq (p - 1) := Nat.gcd_dvd_left _ _
          rw [h2] at h_dvd
          exact h_dvd
        have h_not_dvd_pm2 : ¬ (p ∣ x_seq (p - 2)) := by
          have h_iff := p_dvd_x_pm2_iff p hp hp5
          rw [h_iff]
          intro h_gcd
          let q := Nat.minFac (p - 2)
          have hq_prime : Nat.Prime q := Nat.minFac_prime (by omega)
          have h_comp : ¬ Nat.Prime (p - 2) := hc
          have hq_dvd_pm2 : q ∣ p - 2 := Nat.minFac_dvd (p - 2)
          have hq_dvd_pm3 : q ∣ x_seq (p - 3) := min_fac_dvd_x_seq_pm3 p hp hp5 hc
          have hq_gcd : q ∣ Nat.gcd (x_seq (p - 3)) (p - 2) := Nat.dvd_gcd hq_dvd_pm3 hq_dvd_pm2
          have hq_one : q ∣ 1 := by
            rw [h_gcd] at hq_gcd
            exact hq_gcd
          have hq_le_one : q ≤ 1 := Nat.le_of_dvd (by decide) hq_one
          have h_ge2 : q ≥ 2 := hq_prime.two_le
          omega
        have h_not_dvd_pm1 : ¬ (p ∣ x_seq (p - 1)) := p_not_dvd_pm1_of_pm2 p hp hp5 h_not_dvd_pm2
        contradiction
    rw [h_gcd_eq]
    exact Nat.div_one p
