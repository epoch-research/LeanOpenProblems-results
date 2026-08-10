import FormalConjectures.Util.ProblemImports

open Nat Int

set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

/-- The rule function for Rule 167. Inputs must be 0 or 1. -/
def ca_rule_167 (c_L c_C c_R : ℕ) : ℕ :=
  let R : ℕ := 167
  let index : ℕ := 4 * c_L + 2 * c_C + c_R
  -- Rule 167 is determined by the index-th bit of R.
  (R / (2 ^ index)) % 2

/--
The state of the Rule 167 elementary cellular automaton at time $t$ and position $x$.
The initial condition is a single ON cell at $x=0$.
$C(t, x)$ is structurally recursive on $t$.
-/
def ca_state (t : ℕ) (x : ℤ) : ℕ :=
  match t with
  | 0 => if x = 0 then 1 else 0
  | t' + 1 =>
    let C_t' (y : ℤ) := ca_state t' y
    ca_rule_167 (C_t' (x - 1)) (C_t' x) (C_t' (x + 1))

/-- The sequence of bits forming the middle column of the CA pattern, $C_{t, 0}$. -/
def middle_column_bit (t : ℕ) : ℕ := ca_state t 0

/--
A267581: Decimal representation of the middle column of the "Rule 167" elementary cellular automaton
starting with a single ON (black) cell.
The term $a(n)$ is the decimal value of the binary number $C_{0, 0} C_{1, 0} \dots C_{n, 0}$,
where $C_{i, 0}$ is the state of the center cell at time $i$.
$$a(n) = \sum_{k=0}^n C_{k, 0} \cdot 2^{n-k}$$
-/
noncomputable def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n + 1)) fun k => (middle_column_bit k) * (2^ (n - k))

/-- The floor term in the conjectured recurrence relation for A267581.
This term, $\lfloor (1/2)^{(2^{n+1} \bmod n)} \rfloor$, simplifies to 1 if $(2^{n+1} \bmod n) = 0$
(i.e., $n \mid 2^{n+1}$), and 0 otherwise.
Since the recurrence is only stated for $n \ge 2$, the $n=0$ case is irrelevant to the conjecture. -/
def oeis_floor_term (n : ℕ) : ℕ :=
  if n = 0 then 0
  else if (2 ^ (n + 1)) % n = 0 then 1 else 0

lemma ca_rule_167_eq_zero_iff (L C R : ℕ) (hL : L < 2) (hC : C < 2) (hR : R < 2) :
  ca_rule_167 L C R = 0 ↔ (L = 0 ∧ C = 1 ∧ R = 1) ∨ (L = 1 ∧ C = 0 ∧ R = 0) ∨ (L = 1 ∧ C = 1 ∧ R = 0) := by
  interval_cases L <;> interval_cases C <;> interval_cases R <;> (unfold ca_rule_167; decide)

def z_pred (t : ℕ) (x : ℤ) : Prop :=
  if (x + t) % 2 = 0 then
    let j := (x + t - 2) / 2
    if 0 ≤ j ∧ j < t then
      (Nat.choose (t - 1) j.toNat) % 2 = 1
    else False
  else False

lemma ca_state_one_eq_zero_iff (x : ℤ) : ca_state 1 x = 0 ↔ z_pred 1 x := by
  constructor
  · intro h
    unfold ca_state ca_rule_167 at h
    have h_state (y : ℤ) : ca_state 0 y = if y = 0 then 1 else 0 := rfl
    simp only [h_state] at h
    unfold z_pred
    split_ifs with h_odd
    · by_cases hx : x = 1
      · subst hx
        simp
      · exfalso
        by_cases hx1 : x = -1
        · subst hx1
          revert h; decide
        · have h_L : (if x - 1 = 0 then 1 else 0) = 0 := by split_ifs <;> omega
          have h_C : (if x = 0 then 1 else 0) = 0 := by split_ifs <;> omega
          have h_R : (if x + 1 = 0 then 1 else 0) = 0 := by split_ifs <;> omega
          rw [h_L, h_C, h_R] at h
          revert h; decide
    · by_cases hx0 : x = 0
      · subst hx0
        revert h; decide
      · have h_L : (if x - 1 = 0 then 1 else 0) = 0 := by split_ifs <;> omega
        have h_C : (if x = 0 then 1 else 0) = 0 := by split_ifs <;> omega
        have h_R : (if x + 1 = 0 then 1 else 0) = 0 := by split_ifs <;> omega
        rw [h_L, h_C, h_R] at h
        revert h; decide
  · intro h
    unfold z_pred at h
    dsimp only at h
    split_ifs at h with h1 h2
    · have hx : x = 1 := by omega
      subst hx
      rfl

lemma ca_state_lt_two (t : ℕ) (x : ℤ) : ca_state t x < 2 := by
  induction t generalizing x with
  | zero =>
    unfold ca_state
    split <;> decide
  | succ t' ih =>
    unfold ca_state
    unfold ca_rule_167
    exact Nat.mod_lt _ (by decide)

lemma choose_step_logic (t : ℕ) (j : ℤ) (ht : t ≥ 1) :
  (((0 ≤ j ∧ j ≤ t) ∧ t.choose j.toNat % 2 = 1) ↔
    (((0 ≤ j - 1 ∧ j - 1 < t) ∧ (t - 1).choose (j - 1).toNat % 2 = 1) ∧ (0 ≤ j → j < t → (t - 1).choose j.toNat % 2 = 0)) ∨
    (((0 ≤ j - 1 → j - 1 < t → (t - 1).choose (j - 1).toNat % 2 = 0)) ∧ (0 ≤ j ∧ j < t) ∧ (t - 1).choose j.toNat % 2 = 1)) := by
  by_cases hj0 : j < 0
  · have hj_L : ¬ (0 ≤ j - 1) := by omega
    have hj_R : ¬ (0 ≤ j) := by omega
    simp [hj_L, hj_R, hj0]
    intro h_mid; exfalso; omega
  · push_neg at hj0
    by_cases hjt : j > t
    · have hj_L : ¬ (j - 1 < t) := by omega
      have hj_R : ¬ (j < t) := by omega
      have h_L2 : ¬ (j ≤ t) := by omega
      simp [hj_L, hj_R, h_L2]
    · push_neg at hjt
      by_cases hj_eq0 : j = 0
      · have h_t : 0 < t := by omega
        simp [hj_eq0, h_t]
      · by_cases hj_eqt : j = t
        · have h_t : 1 ≤ t := by omega
          simp [hj_eqt, h_t]
        · have hj_mid : 1 ≤ j ∧ j < t := by omega
          have hj_L : 0 ≤ j - 1 ∧ j - 1 < t := by omega
          have hj_R : 0 ≤ j ∧ j < t := by omega
          simp only [hj_mid.2, hj_L.1, hj_L.2, hj_R.1, true_and,
                     and_true, hjt, hj0, true_implies]
          have h_eq : t.choose j.toNat = (t - 1).choose (j - 1).toNat + (t - 1).choose j.toNat := by
            have h_t : t = (t - 1) + 1 := by omega
            have h_j : j.toNat = (j - 1).toNat + 1 := by omega
            rw [h_t, h_j, Nat.choose_succ_succ']
            rfl
          rw [h_eq]
          have h_mod (A B : ℕ) : (A + B) % 2 = 1 ↔ (A % 2 = 1 ∧ B % 2 = 0) ∨ (A % 2 = 0 ∧ B % 2 = 1) := by
            omega
          exact h_mod ((t - 1).choose (j - 1).toNat) ((t - 1).choose j.toNat)

lemma choose_recurrence_one (A B : ℕ) :
  (2 * A + 1).choose (2 * B + 1) % 2 = A.choose B % 2 := by
  have h_lucas := @Choose.choose_modEq_choose_mod_mul_choose_div_nat (2 * A + 1) (2 * B + 1) 2 ⟨Nat.prime_two⟩
  rw [Nat.ModEq] at h_lucas
  have h_div1 : (2 * A + 1) / 2 = A := by omega
  have h_mod1 : (2 * A + 1) % 2 = 1 := by omega
  have h_div2 : (2 * B + 1) / 2 = B := by omega
  have h_mod2 : (2 * B + 1) % 2 = 1 := by omega
  rw [h_div1, h_mod1, h_div2, h_mod2] at h_lucas
  have h_c1 : Nat.choose 1 1 = 1 := rfl
  rw [h_c1, one_mul] at h_lucas
  exact h_lucas

lemma choose_recurrence_zero (A B : ℕ) :
  (2 * A + 1).choose (2 * B) % 2 = A.choose B % 2 := by
  have h_lucas := @Choose.choose_modEq_choose_mod_mul_choose_div_nat (2 * A + 1) (2 * B) 2 ⟨Nat.prime_two⟩
  rw [Nat.ModEq] at h_lucas
  have h_div1 : (2 * A + 1) / 2 = A := by omega
  have h_mod1 : (2 * A + 1) % 2 = 1 := by omega
  have h_div2 : (2 * B) / 2 = B := by omega
  have h_mod2 : (2 * B) % 2 = 0 := by omega
  rw [h_div1, h_mod1, h_div2, h_mod2] at h_lucas
  have h_c1 : Nat.choose 1 0 = 1 := rfl
  rw [h_c1, one_mul] at h_lucas
  exact h_lucas

lemma z_pred_rec (t : ℕ) (x : ℤ) (ht : t ≥ 1) :
  z_pred (t+1) x ↔
  (z_pred t (x-1) ∧ ¬ z_pred t x ∧ ¬ z_pred t (x+1)) ∨
  (¬ z_pred t (x-1) ∧ z_pred t x ∧ z_pred t (x+1)) ∨
  (¬ z_pred t (x-1) ∧ ¬ z_pred t x ∧ z_pred t (x+1)) := by
  unfold z_pred
  by_cases h_odd : (x + (t+1)) % 2 = 0
  · have h_odd' : (x + t) % 2 ≠ 0 := by omega
    have h_L : (x - 1 + t) % 2 = 0 := by omega
    have h_R : (x + 1 + t) % 2 = 0 := by omega
    simp [h_odd, h_odd', h_L, h_R]
    have h_div1 : (x + (t + 1) - 2) / 2 = (x + t - 1) / 2 := by omega
    have h_div2 : (x - 1 + t - 2) / 2 = (x + t - 1) / 2 - 1 := by omega
    have h_div3 : (x + 1 + t - 2) / 2 = (x + t - 1) / 2 := by omega
    rw [h_div1, h_div2, h_div3]
    exact choose_step_logic t ((x + t - 1) / 2) ht
  · have h_odd' : (x + t) % 2 = 0 := by omega
    have h_L : (x - 1 + t) % 2 ≠ 0 := by omega
    have h_R : (x + 1 + t) % 2 ≠ 0 := by omega
    simp [h_odd, h_odd', h_L, h_R]

lemma ca_state_eq_zero_iff (t : ℕ) (x : ℤ) (ht : t ≥ 1) :
  ca_state t x = 0 ↔ z_pred t x := by
  induction t generalizing x with
  | zero => omega
  | succ t' ih =>
    by_cases ht' : t' = 0
    · subst ht'
      exact ca_state_one_eq_zero_iff x
    · have ht'_pos : t' ≥ 1 := by omega
      have h_rule := ca_rule_167_eq_zero_iff (ca_state t' (x-1)) (ca_state t' x) (ca_state t' (x+1))
                     (ca_state_lt_two t' (x-1)) (ca_state_lt_two t' x) (ca_state_lt_two t' (x+1))
      unfold ca_state
      rw [h_rule]
      rw [z_pred_rec t' x ht'_pos]
      have h_eq (y : ℤ) : ca_state t' y = 0 ↔ z_pred t' y := ih y ht'_pos
      have h_eq1 (y : ℤ) : ca_state t' y = 1 ↔ ¬ z_pred t' y := by
        have h_lt := ca_state_lt_two t' y
        rw [← h_eq y]
        omega
      rw [h_eq (x-1), h_eq x, h_eq (x+1)]
      rw [h_eq1 (x-1), h_eq1 x, h_eq1 (x+1)]

lemma choose_two_mul (m : ℕ) (hm : m ≥ 1) :
  (Nat.choose (2 * m) m) % 2 = 0 := by
  have h_succ : Nat.succ (2 * m - 1) * Nat.choose (2 * m - 1) (m - 1) =
                Nat.choose (Nat.succ (2 * m - 1)) (Nat.succ (m - 1)) * Nat.succ (m - 1) := by
    exact Nat.add_one_mul_choose_eq (2 * m - 1) (m - 1)
  have h_2m : Nat.succ (2 * m - 1) = 2 * m := by omega
  have h_m : Nat.succ (m - 1) = m := by omega
  rw [h_2m, h_m] at h_succ
  have h_eq : 2 * Nat.choose (2 * m - 1) (m - 1) = Nat.choose (2 * m) m := by
    have h_mul : 2 * Nat.choose (2 * m - 1) (m - 1) * m = Nat.choose (2 * m) m * m := by
      calc 2 * Nat.choose (2 * m - 1) (m - 1) * m = 2 * m * Nat.choose (2 * m - 1) (m - 1) := by ring
      _ = Nat.choose (2 * m) m * m := h_succ
    exact Nat.mul_right_cancel hm h_mul
  rw [← h_eq]
  simp

lemma choose_odd_iff_pow_two (m : ℕ) (hm : m ≥ 1) :
  (2 * m - 1).choose (m - 1) % 2 = 1 ↔ ∃ k, m = 2 ^ k := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases hm1 : m = 1
    · subst hm1
      simp
      exact ⟨0, rfl⟩
    · have hm_gt1 : m > 1 := by omega
      by_cases h_even : m % 2 = 0
      · have h_q : ∃ q, m = 2 * q ∧ 1 ≤ q ∧ q < m := by
          refine ⟨m / 2, ?_⟩
          have : m = 2 * (m / 2) := by omega
          omega
        rcases h_q with ⟨q, rfl, hq1, hqm⟩
        have h_rec : (2 * (2 * q) - 1).choose (2 * q - 1) % 2 = (2 * q - 1).choose (q - 1) % 2 := by
          have h1 : 2 * (2 * q) - 1 = 2 * (2 * q - 1) + 1 := by omega
          have h2 : 2 * q - 1 = 2 * (q - 1) + 1 := by omega
          have h_rec_one := choose_recurrence_one (2 * q - 1) (q - 1)
          rw [← h2] at h_rec_one
          rw [h1]
          exact h_rec_one
        rw [h_rec]
        have ih_q := ih q hqm hq1
        rw [ih_q]
        constructor
        · rintro ⟨k, rfl⟩
          exact ⟨k + 1, by ring⟩
        · rintro ⟨k, hk⟩
          have hk_pos : k ≥ 1 := by
            by_contra h_zero
            have : k = 0 := by omega
            subst this
            simp at hk
          have hk_ne : k ≠ 0 := by omega
          rcases Nat.exists_eq_succ_of_ne_zero hk_ne with ⟨d, rfl⟩
          have hq : q = 2 ^ d := by omega
          exact ⟨d, hq⟩
      · have h_q : ∃ q, m = 2 * q + 1 ∧ 1 ≤ q ∧ q < m := by
          refine ⟨m / 2, ?_⟩
          omega
        rcases h_q with ⟨q, rfl, hq1, hqm⟩
        have h_rec : (2 * (2 * q) + 1).choose (2 * q) % 2 = (2 * q).choose q % 2 := by
          exact choose_recurrence_zero (2 * q) q
        have h_goal_eq1 : 2 * (2 * q + 1) - 1 = 2 * (2 * q) + 1 := by omega
        have h_goal_eq2 : 2 * q + 1 - 1 = 2 * q := by omega
        rw [h_goal_eq1, h_goal_eq2]
        rw [h_rec]
        have h_zero : (2 * q).choose q % 2 = 0 := choose_two_mul q hq1
        rw [h_zero]
        simp only [zero_ne_one, false_iff]
        rintro ⟨k, hk⟩
        have hk0 : k = 0 := by
          by_contra h_ne
          rcases Nat.exists_eq_succ_of_ne_zero h_ne with ⟨d, rfl⟩
          have h_even_pow : 2 ^ (d + 1) % 2 = 0 := by
            rw [pow_succ]
            simp
          omega
        subst hk0
        omega

lemma z_pred_zero_iff (n : ℕ) (hn : 2 ≤ n) :
  z_pred n 0 ↔ ∃ k, n = 2^k := by
  unfold z_pred
  have h_cond : (0 + (n : ℤ)) % 2 = 0 ↔ n % 2 = 0 := by omega
  simp only [h_cond]
  by_cases h_even : n % 2 = 0
  · simp only [h_even, ↓reduceIte]
    have h_bounds : 0 ≤ (0 + (n : ℤ) - 2) / 2 ∧ (0 + (n : ℤ) - 2) / 2 < n := by omega
    simp only [h_bounds, ↓reduceIte, true_and]
    have h_m : ∃ m, n = 2 * m ∧ m ≥ 1 := by
      refine ⟨n / 2, ?_⟩
      omega
    rcases h_m with ⟨m, h_eq, hm⟩
    rw [h_eq]
    have h_div : (0 + ↑(2 * m) - 2) / 2 = (m : ℤ) - 1 := by omega
    rw [h_div]
    have h_toNat : ((m : ℤ) - 1).toNat = m - 1 := by omega
    rw [h_toNat]
    rw [choose_odd_iff_pow_two m hm]
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨k + 1, by ring⟩
    · rintro ⟨k, hk⟩
      have hk_pos : k ≥ 1 := by
        by_contra h_zero
        have : k = 0 := by omega
        subst this
        simp at hk
      have hk_ne : k ≠ 0 := by omega
      rcases Nat.exists_eq_succ_of_ne_zero hk_ne with ⟨d, rfl⟩
      have hq : m = 2 ^ d := by omega
      exact ⟨d, hq⟩
  · simp only [h_even, ↓reduceIte]
    constructor
    · intro h; contradiction
    · rintro ⟨k, hk⟩
      have hk_pos : k ≥ 1 := by
        by_contra h_zero
        have : k = 0 := by omega
        subst this
        simp at hk
        omega
      have h_even_n : n % 2 = 0 := by
        rw [hk]
        have hk_ne : k ≠ 0 := by omega
        rcases Nat.exists_eq_succ_of_ne_zero hk_ne with ⟨d, rfl⟩
        rw [pow_succ]
        simp
      exact h_even h_even_n

lemma a_rec (n : ℕ) (hn : n ≥ 1) :
  a n = 2 * a (n - 1) + middle_column_bit n := by
  unfold a
  rw [Finset.sum_range_succ]
  have h_term : middle_column_bit n * 2 ^ (n - n) = middle_column_bit n := by
    simp
  rw [h_term]
  congr 1
  have h_sum : Finset.sum (Finset.range n) (fun k => middle_column_bit k * 2 ^ (n - k)) =
               2 * Finset.sum (Finset.range n) (fun k => middle_column_bit k * 2 ^ (n - 1 - k)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [Finset.mem_range] at hk
    have h_pow : 2 ^ (n - k) = 2 * 2 ^ (n - 1 - k) := by
      have h1 : n - k = (n - 1 - k) + 1 := by omega
      rw [h1, Nat.pow_succ, mul_comm]
    rw [h_pow]
    ring
  rw [h_sum]
  rw [Nat.sub_add_cancel hn]

lemma le_pow_two_self (k : ℕ) : k ≤ 2 ^ k := by
  induction k with
  | zero => omega
  | succ d ih =>
    rw [pow_succ]
    have h_pos : 1 ≤ 2 ^ d := Nat.one_le_pow d 2 (by decide)
    omega

lemma oeis_floor_term_eq_one_iff (n : ℕ) (hn : 2 ≤ n) :
  oeis_floor_term n = 1 ↔ ∃ k, n = 2 ^ k := by
  unfold oeis_floor_term
  have hn0 : n ≠ 0 := by omega
  simp [hn0]
  rw [Nat.dvd_iff_mod_eq_zero.symm]
  rw [Nat.dvd_prime_pow Nat.prime_two]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, rfl⟩
  · rintro ⟨k, rfl⟩
    have hk_le : k ≤ 2 ^ k + 1 := by
      have := le_pow_two_self k
      omega
    exact ⟨k, hk_le, rfl⟩

lemma oeis_floor_term_eq_zero_iff (n : ℕ) (hn : 2 ≤ n) :
  oeis_floor_term n = 0 ↔ ¬ ∃ k, n = 2 ^ k := by
  have h_cases : oeis_floor_term n = 1 ∨ oeis_floor_term n = 0 := by
    unfold oeis_floor_term; split_ifs <;> omega
  constructor
  · intro h h1
    rw [← oeis_floor_term_eq_one_iff n hn] at h1
    rw [h] at h1
    contradiction
  · intro h
    rcases h_cases with h_one | h_zero
    · rw [oeis_floor_term_eq_one_iff n hn] at h_one
      contradiction
    · exact h_zero

/--
A267581 conjecture on the recurrence relation.

Assuming the conjecture that the positions of the 0-bits of the middle column ("Rule 167") are given by the sequence A000051, it follows that a possible formula could be: a(n) = 2*a(n-1) + 1 - floor((1/2)^((2^(n+1)) mod n)) with a(0)=1 and a(1)=3 (Not proved, but tested up to n = 10^4). - _Andres Cicuttin_, Mar 29 2016
-/
theorem oeis_267581_conjecture_0 (n : ℕ) (hn : 2 ≤ n) :
  a n = 2 * a (n - 1) + 1 - oeis_floor_term n := by
  have hn1 : n ≥ 1 := by omega
  have h_rec := a_rec n hn1
  rw [h_rec]
  unfold middle_column_bit
  by_cases h_pow : ∃ k, n = 2 ^ k
  · have h_floor : oeis_floor_term n = 1 := (oeis_floor_term_eq_one_iff n hn).mpr h_pow
    have h_bit_eq : ca_state n 0 = 0 := by
      rw [ca_state_eq_zero_iff n 0 hn1]
      rwa [z_pred_zero_iff n hn]
    rw [h_floor, h_bit_eq]
    omega
  · have h_floor : oeis_floor_term n = 0 := (oeis_floor_term_eq_zero_iff n hn).mpr h_pow
    have h_bit_eq : ca_state n 0 = 1 := by
      have h_lt := ca_state_lt_two n 0
      have h_nz : ca_state n 0 ≠ 0 := by
        intro hc
        rw [ca_state_eq_zero_iff n 0 hn1] at hc
        rw [z_pred_zero_iff n hn] at hc
        exact h_pow hc
      omega
    rw [h_floor, h_bit_eq]
    omega
