import FormalConjectures.Util.ProblemImports

open Nat

def x_seq : ℕ → ℕ
| 0 => 0
| 1 => 1
| n + 1 => 2 * (x_seq n) + Nat.lcm (x_seq n) (n + 1)

def A135508 (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    let x_n_plus_1 := x_seq (n + 1)
    let x_n := x_seq n
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
    sorry

theorem test_5 : 5 ∣ x_seq 24 := by decide
theorem test_7 : 7 ∣ x_seq 48 := by decide
