import Mathlib

open Nat

lemma div2_lt_self_of_pos {n : ℕ} (h : 0 < n) : div2 n < n := by
  have h1 := bodd_add_div2 n
  have hb : n.bodd.toNat ≤ 1 := by
    cases n.bodd <;> decide
  omega

lemma choose_mod_two_eq (n k : ℕ) : (n.choose k : ZMod 2) = (n % 2).choose (k % 2) * (n / 2).choose (k / 2) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h_rhs : ((n % 2).choose (k % 2) * (n / 2).choose (k / 2) : ZMod 2) = (((n % 2).choose (k % 2) * (n / 2).choose (k / 2) : ℕ) : ZMod 2) := by push_cast; rfl
  rw [h_rhs]
  rw [ZMod.natCast_eq_natCast_iff]
  exact Choose.choose_modEq_choose_mod_mul_choose_div_nat

lemma and_eq_self_of_choose_mod_two_eq_one (n k : ℕ) (h : (n.choose k : ZMod 2) = 1) : k &&& n = k := by
  induction n using Nat.strong_induction_on generalizing k with
  | h n ih =>
    by_cases hn : n = 0
    · rw [hn] at h
      have hk : k = 0 := by
        by_contra hk_ne
        have : Nat.choose 0 k = 0 := Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hk_ne)
        rw [this] at h
        exact zero_ne_one h
      rw [hk]
      rw [Nat.zero_and]
    · rw [choose_mod_two_eq] at h
      have h_mul : ∀ (x y : ZMod 2), x * y = 1 → x = 1 ∧ y = 1 := by
        decide
      rcases h_mul _ _ h with ⟨h1, h2⟩
      have h_div_lt : n / 2 < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide)
      have h_div2 : div2 n = n / 2 := div2_val n
      have h_k_div2 : div2 k = k / 2 := div2_val k
      have h2_eq : ((n / 2).choose (k / 2) : ZMod 2) = 1 := h2
      have ih_res := ih (n / 2) h_div_lt (k / 2) h2_eq
      have h_bodd : (bodd k = false) ∨ (bodd k = true ∧ bodd n = true) := by
        cases hk : bodd k <;> cases hn2 : bodd n
        · left; rfl
        · left; rfl
        · have h_n_mod_eq : n % 2 = n.bodd.toNat := by
            have := bodd_add_div2 n
            omega
          have h_k_mod_eq : k % 2 = k.bodd.toNat := by
            have := bodd_add_div2 k
            omega
          rw [h_n_mod_eq, hn2, h_k_mod_eq, hk] at h1
          simp at h1
        · right; exact ⟨rfl, rfl⟩
      have h_k_eq : k = bit (bodd k) (div2 k) := (bit_bodd_div2 k).symm
      have h_n_eq : n = bit (bodd n) (div2 n) := (bit_bodd_div2 n).symm
      rw [h_k_eq, h_n_eq]
      rw [land_bit]
      rw [h_div2, h_k_div2]
      rw [ih_res]
      rcases h_bodd with hk_false | ⟨hk_true, hn_true⟩
      · rw [hk_false]
        simp
      · rw [hk_true, hn_true]
        simp

lemma choose_mod_two_eq_one_of_and_eq_self (n k : ℕ) (h : k &&& n = k) : (n.choose k : ZMod 2) = 1 := by
  induction n using Nat.strong_induction_on generalizing k with
  | h n ih =>
    by_cases hn : n = 0
    · rw [hn] at h
      have hk : k = 0 := by
        rw [← h]
        rw [Nat.and_zero]
      rw [hn, hk]
      rfl
    · rw [choose_mod_two_eq]
      have h_div_lt : n / 2 < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide)
      have h_div2 : div2 n = n / 2 := div2_val n
      have h_k_div2 : div2 k = k / 2 := div2_val k
      have h_k_eq : k = bit (bodd k) (div2 k) := (bit_bodd_div2 k).symm
      have h_n_eq : n = bit (bodd n) (div2 n) := (bit_bodd_div2 n).symm
      have h_and : bit (bodd k) (div2 k) &&& bit (bodd n) (div2 n) = bit (bodd k) (div2 k) := by
        rw [← h_k_eq, ← h_n_eq]
        exact h
      rw [land_bit] at h_and
      have h_div : div2 k &&& div2 n = div2 k := by
        have h_d := congr_arg div2 h_and
        rw [div2_bit, div2_bit] at h_d
        exact h_d
      have h_bodd : (bodd k && bodd n) = bodd k := by
        have h_b := congr_arg bodd h_and
        rw [bodd_bit, bodd_bit] at h_b
        exact h_b
      have ih_res := ih (n / 2) h_div_lt (k / 2)
      rw [h_div2, h_k_div2] at h_div
      have h_ih_eq := ih_res h_div
      have h_mod : n % 2 = (bodd n).toNat := by
        have := bodd_add_div2 n
        omega
      have h_k_mod : k % 2 = (bodd k).toNat := by
        have := bodd_add_div2 k
        omega
      rw [h_mod, h_k_mod]
      cases h_bn : bodd n <;> cases h_bk : bodd k
      · simp [h_ih_eq]
      · rw [h_bn, h_bk] at h_bodd
        simp at h_bodd
      · simp [h_ih_eq]
      · simp [h_ih_eq]

lemma le_of_and_eq_self (a b : ℕ) (h : b &&& a = b) : b ≤ a := by
  induction a using Nat.strong_induction_on generalizing b with
  | h a ih =>
    by_cases ha : a = 0
    · rw [ha] at h
      have hb : b = 0 := by
        rw [← h]
        rw [Nat.and_zero]
      rw [hb, ha]
    · have h_div2_lt : div2 a < a := div2_lt_self_of_pos (Nat.pos_of_ne_zero ha)
      have h_a_eq : a = bit (bodd a) (div2 a) := (bit_bodd_div2 a).symm
      have h_b_eq : b = bit (bodd b) (div2 b) := (bit_bodd_div2 b).symm
      have h_and : bit (bodd b) (div2 b) &&& bit (bodd a) (div2 a) = bit (bodd b) (div2 b) := by
        rw [← h_b_eq, ← h_a_eq]
        exact h
      rw [land_bit] at h_and
      have h_div : div2 b &&& div2 a = div2 b := by
        have h_d := congr_arg div2 h_and
        rw [div2_bit, div2_bit] at h_d
        exact h_d
      have h_bodd : (bodd b && bodd a) = bodd b := by
        have h_b := congr_arg bodd h_and
        rw [bodd_bit, bodd_bit] at h_b
        exact h_b
      have h_ih := ih (div2 a) h_div2_lt (div2 b) h_div
      rw [h_a_eq, h_b_eq]
      rw [bit_val, bit_val]
      cases h1 : bodd a <;> cases h2 : bodd b
      · simp; omega
      · rw [h1, h2] at h_bodd
        simp at h_bodd
      · simp; omega
      · simp; omega

lemma sub_eq_ldiff_of_and_eq_self (a b : ℕ) (h : b &&& a = b) : a - b = ldiff a b := by
  induction a using Nat.strong_induction_on generalizing b with
  | h a ih =>
    by_cases ha : a = 0
    · rw [ha]
      rw [ha] at h
      have hb : b = 0 := by
        rw [← h]
        rw [Nat.and_zero]
      rw [hb]
      change 0 - 0 = Nat.bitwise (fun a b => a && !b) 0 0
      rw [Nat.bitwise_zero_left]
      rfl
    · have h_div2_lt : div2 a < a := div2_lt_self_of_pos (Nat.pos_of_ne_zero ha)
      have h_a_eq : a = bit (bodd a) (div2 a) := (bit_bodd_div2 a).symm
      have h_b_eq : b = bit (bodd b) (div2 b) := (bit_bodd_div2 b).symm
      have h_and : bit (bodd b) (div2 b) &&& bit (bodd a) (div2 a) = bit (bodd b) (div2 b) := by
        rw [← h_b_eq, ← h_a_eq]
        exact h
      rw [land_bit] at h_and
      have h_bodd : (bodd b && bodd a) = bodd b := by
        have h_b := congr_arg bodd h_and
        rw [bodd_bit, bodd_bit] at h_b
        exact h_b
      have h_div : div2 b &&& div2 a = div2 b := by
        have h_d := congr_arg div2 h_and
        rw [div2_bit, div2_bit] at h_d
        exact h_d
      have h_le := le_of_and_eq_self (div2 a) (div2 b) h_div
      have h_ih := ih (div2 a) h_div2_lt (div2 b) h_div
      rw [h_a_eq, h_b_eq]
      rw [ldiff_bit]
      rw [← h_ih]
      rw [bit_val, bit_val, bit_val]
      cases h1 : bodd a <;> cases h2 : bodd b
      · simp; omega
      · rw [h1, h2] at h_bodd
        simp at h_bodd
      · simp; omega
      · simp; omega

lemma add_eq_lor_of_and_eq_zero (a b : ℕ) (h : a &&& b = 0) : a + b = a ||| b := by
  induction a using Nat.strong_induction_on generalizing b with
  | h a ih =>
    by_cases ha : a = 0
    · rw [ha, zero_add]
      have h_lor : 0 ||| b = b := by
        change bitwise or 0 b = b
        rw [bitwise_zero_left]
        rfl
      rw [h_lor]
    · have h_div2_lt : div2 a < a := div2_lt_self_of_pos (Nat.pos_of_ne_zero ha)
      have h_a_eq : a = bit (bodd a) (div2 a) := (bit_bodd_div2 a).symm
      have h_b_eq : b = bit (bodd b) (div2 b) := (bit_bodd_div2 b).symm
      have h_and_zero : bit (bodd a) (div2 a) &&& bit (bodd b) (div2 b) = 0 := by
        rw [← h_a_eq, ← h_b_eq]
        exact h
      rw [land_bit] at h_and_zero
      rw [Nat.bit_eq_zero_iff] at h_and_zero
      rcases h_and_zero with ⟨h_div_zero, h_bodd_zero⟩
      have h_ih := ih (div2 a) h_div2_lt (div2 b) h_div_zero
      rw [h_a_eq, h_b_eq]
      rw [lor_bit]
      rw [bit_val, bit_val, bit_val]
      rw [← h_ih]
      have h_bodd : (bodd a || bodd b).toNat = (bodd a).toNat + (bodd b).toNat := by
        cases h1 : bodd a <;> cases h2 : bodd b <;> (try rfl)
        · rw [h1, h2] at h_bodd_zero
          simp at h_bodd_zero
      rw [h_bodd]
      omega

lemma land_zero_of_and_add_eq_self (n j : ℕ) (h : j &&& (n + j) = j) : n &&& j = 0 := by
  generalize h_sum : n + j = sum
  induction sum using Nat.strong_induction_on generalizing n j with
  | h sum ih =>
    by_cases hj : j = 0
    · rw [hj]
      rw [Nat.and_zero]
    · by_cases hn : n = 0
      · rw [hn, Nat.zero_and]
      · have h_sum_pos : 0 < n + j := by omega
        have h_div_lt : div2 (n + j) < n + j := div2_lt_self_of_pos h_sum_pos
        have h_j_eq : j = bit (bodd j) (div2 j) := (bit_bodd_div2 j).symm
        have h_n_eq : n = bit (bodd n) (div2 n) := (bit_bodd_div2 n).symm
        have h_sum_eq : n + j = bit (bodd (n + j)) (div2 (n + j)) := (bit_bodd_div2 (n + j)).symm
        have h_and : bit (bodd j) (div2 j) &&& bit (bodd (n + j)) (div2 (n + j)) = bit (bodd j) (div2 j) := by
          rw [← h_j_eq, ← h_sum_eq]
          exact h
        rw [land_bit] at h_and
        have h_bodd : (bodd j && bodd (n + j)) = bodd j := by
          have h_b := congr_arg bodd h_and
          rw [bodd_bit, bodd_bit] at h_b
          exact h_b
        have h_div : div2 j &&& div2 (n + j) = div2 j := by
          have h_d := congr_arg div2 h_and
          rw [div2_bit, div2_bit] at h_d
          exact h_d
        have h_bodd_n_j : (bodd n && bodd j) = false := by
          cases h_bj : bodd j
          · cases bodd n <;> rfl
          · cases h_bn : bodd n
            · rfl
            · have h_b_add : bodd (n + j) = false := by
                rw [bodd_add, h_bj, h_bn]
                rfl
              rw [h_bj, h_b_add] at h_bodd
              contradiction
        have h_div_add : div2 (n + j) = div2 n + div2 j := by
          have h_add_eq : n + j = 2 * div2 n + (bodd n).toNat + (2 * div2 j + (bodd j).toNat) := by
            have h1 := bodd_add_div2 n
            have h2 := bodd_add_div2 j
            omega
          have h_div_eq : div2 (n + j) = (n + j) / 2 := div2_val (n + j)
          rw [h_div_eq, h_add_eq]
          cases h_b : bodd n <;> cases h_bj : bodd j
          · simp; omega
          · simp; omega
          · simp; omega
          · rw [h_b, h_bj] at h_bodd_n_j
            contradiction
        rw [h_div_add] at h_div
        have h_lt : div2 n + div2 j < sum := by
          rw [← h_sum, ← h_div_add]
          exact h_div_lt
        have h_ih := ih (div2 n + div2 j) h_lt (div2 n) (div2 j) h_div rfl
        rw [h_n_eq, h_j_eq]
        rw [land_bit]
        rw [h_bodd_n_j, h_ih]
        rfl

lemma land_zero_of_choose_add_eq_one (n j : ℕ) (h : ((n + j).choose j : ZMod 2) = 1) : n &&& j = 0 := by
  have h_and := and_eq_self_of_choose_mod_two_eq_one (n + j) j h
  exact land_zero_of_and_add_eq_self n j h_and

lemma and_add_eq_self_of_land_zero (n j : ℕ) (h : n &&& j = 0) : j &&& (n + j) = j := by
  generalize h_sum : n + j = sum
  induction sum using Nat.strong_induction_on generalizing n j with
  | h sum ih =>
    rw [← h_sum]
    by_cases hj : j = 0
    · rw [hj]
      rw [Nat.zero_and]
    · by_cases hn : n = 0
      · rw [hn, zero_add]
        simp
      · have h_sum_pos : 0 < n + j := by omega
        have h_div_lt : div2 (n + j) < n + j := div2_lt_self_of_pos h_sum_pos
        have h_j_eq : j = bit (bodd j) (div2 j) := (bit_bodd_div2 j).symm
        have h_n_eq : n = bit (bodd n) (div2 n) := (bit_bodd_div2 n).symm
        have h_sum_eq : n + j = bit (bodd (n + j)) (div2 (n + j)) := (bit_bodd_div2 (n + j)).symm
        have h_and : bit (bodd n) (div2 n) &&& bit (bodd j) (div2 j) = 0 := by
          rw [← h_n_eq, ← h_j_eq]
          exact h
        rw [land_bit] at h_and
        rw [Nat.bit_eq_zero_iff] at h_and
        rcases h_and with ⟨h_div_zero, h_bodd_zero⟩
        have h_bodd_n_j : (bodd n && bodd j) = false := by
          cases h_bj : bodd j
          · cases bodd n <;> rfl
          · cases h_bn : bodd n
            · rfl
            · rw [h_bn, h_bj] at h_bodd_zero
              simp at h_bodd_zero
        have h_div_add : div2 (n + j) = div2 n + div2 j := by
          have h_add_eq : n + j = 2 * div2 n + (bodd n).toNat + (2 * div2 j + (bodd j).toNat) := by
            have h1 := bodd_add_div2 n
            have h2 := bodd_add_div2 j
            omega
          have h_div_eq : div2 (n + j) = (n + j) / 2 := div2_val (n + j)
          rw [h_div_eq, h_add_eq]
          cases h_b : bodd n <;> cases h_bj : bodd j
          · simp; omega
          · simp; omega
          · simp; omega
          · rw [h_b, h_bj] at h_bodd_n_j
            contradiction
        have h_lt : div2 n + div2 j < sum := by
          rw [← h_sum, ← h_div_add]
          exact h_div_lt
        have h_ih := ih (div2 n + div2 j) h_lt (div2 n) (div2 j) h_div_zero rfl
        have h_bodd_eq : (bodd j && bodd (n + j)) = bodd j := by
          cases h_bj : bodd j
          · rfl
          · have h_bodd_add : bodd (n + j) = (bodd n != bodd j) := bodd_add n j
            rw [h_bodd_add, h_bj]
            cases h_bn : bodd n
            · rfl
            · rw [h_bn, h_bj] at h_bodd_n_j
              contradiction
        have h_LHS : j &&& sum = bit (bodd j && bodd sum) (div2 j &&& div2 sum) := by
          rw [h_j_eq, ← h_sum, h_sum_eq, land_bit]
          simp only [bodd_bit, div2_bit]
        rw [h_sum]
        rw [h_LHS]
        rw [← h_sum]
        rw [h_bodd_eq, h_div_add, h_ih]
        exact h_j_eq.symm

lemma choose_add_eq_one_of_land_zero (n j : ℕ) (h : n &&& j = 0) : ((n + j).choose j : ZMod 2) = 1 := by
  have h_and := and_add_eq_self_of_land_zero n j h
  exact choose_mod_two_eq_one_of_and_eq_self (n + j) j h_and

lemma land_zero_of_and_eq_self_of_land_zero (n k j : ℕ) (h1 : k &&& n = k) (h2 : n &&& j = 0) : k &&& j = 0 := by
  have h_eq : (k &&& n) &&& j = k &&& (n &&& j) := Nat.and_assoc k n j
  rw [h1] at h_eq
  rw [h2] at h_eq
  have h_zero : k &&& 0 = 0 := by
    rw [Nat.and_zero]
  rw [h_zero] at h_eq
  exact h_eq

lemma land_add_eq_left_of_land_zero (n k j : ℕ) (h1 : k &&& n = k) (h2 : n &&& j = 0) : (k + j) &&& n = k := by
  have h_k_disj_j : k &&& j = 0 := land_zero_of_and_eq_self_of_land_zero n k j h1 h2
  have h_add : k + j = k ||| j := add_eq_lor_of_and_eq_zero k j h_k_disj_j
  rw [h_add]
  rw [Nat.and_or_distrib_right]
  rw [h1]
  have h2_comm : j &&& n = 0 := by
    rw [Nat.and_comm]
    exact h2
  rw [h2_comm]
  have h_or_zero : k ||| 0 = k := by
    change bitwise or k 0 = k
    rw [bitwise_zero_right]
    rfl
  exact h_or_zero

lemma land_ldiff_self_right (a b : ℕ) : a &&& (b.ldiff a) = 0 := by
  induction a using Nat.strong_induction_on generalizing b with
  | h a ih =>
    by_cases ha : a = 0
    · rw [ha]
      change bitwise and 0 (bitwise (fun x y => x && !y) b 0) = 0
      rw [bitwise_zero_left]
      rfl
    · have h_div2_lt : div2 a < a := div2_lt_self_of_pos (Nat.pos_of_ne_zero ha)
      have h_a_eq : a = bit (bodd a) (div2 a) := (bit_bodd_div2 a).symm
      have h_b_eq : b = bit (bodd b) (div2 b) := (bit_bodd_div2 b).symm
      rw [h_a_eq, h_b_eq]
      change bit (bodd a) (div2 a) &&& (bit (bodd b) (div2 b)).ldiff (bit (bodd a) (div2 a)) = 0
      rw [ldiff_bit]
      rw [land_bit]
      have h_ih := ih (div2 a) h_div2_lt (div2 b)
      rw [h_ih]
      have h_bodd : (bodd a && (bodd b && !bodd a)) = false := by
        cases bodd a <;> cases bodd b <;> rfl
      rw [h_bodd]
      rfl

def term_mod2 (m n k : ℕ) : ZMod 2 :=
  if _h1 : n * (k + 1) ≤ m then
    let remainder := m - n * (k + 1)
    if _h2 : (n + 1) ∣ remainder then
      let j := remainder / (n + 1)
      (n.choose k : ZMod 2) * ((n + j).choose j : ZMod 2)
    else 0
  else 0

lemma term_mod2_eq_one_iff (m n k : ℕ) :
  term_mod2 m n k = 1 ↔
    (n * (k + 1) ≤ m ∧
     (n + 1) ∣ (m - n * (k + 1)) ∧
     (n.choose k : ZMod 2) = 1 ∧
     ((n + ((m - n * (k + 1)) / (n + 1))).choose ((m - n * (k + 1)) / (n + 1)) : ZMod 2) = 1) := by
  unfold term_mod2
  by_cases h1 : n * (k + 1) ≤ m
  · simp [h1]
    by_cases h2 : (n + 1) ∣ (m - n * (k + 1))
    · simp [h2]
    · simp [h2]
  · simp [h1]

def g_pair (m : ℕ) (p : ℕ × ℕ) : ℕ × ℕ :=
  let n := p.1
  let k := p.2
  let j := (m - n * (k + 1)) / (n + 1)
  let s := k + j
  (s, n &&& s)

lemma s_le_m_of_term (m n k : ℕ) (h : term_mod2 m n k = 1) :
  let j := (m - n * (k + 1)) / (n + 1)
  k + j ≤ m := by
  intro j
  have h_eq : n * (k + 1) + j * (n + 1) = m := by
    rw [term_mod2_eq_one_iff] at h
    have h_div := h.2.1
    have h_div_eq : j * (n + 1) = m - n * (k + 1) := Nat.div_mul_cancel h_div
    omega
  by_cases hn : n = 0
  · rw [hn] at h_eq
    simp at h_eq
    rw [← h_eq]
    rw [hn] at h
    rw [term_mod2_eq_one_iff] at h
    have hk_zero : k = 0 := by
      have h_choose := h.2.2.1
      by_contra hk
      have : Nat.choose 0 k = 0 := Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hk)
      rw [this] at h_choose
      exact zero_ne_one h_choose
    rw [hk_zero]
    simp
  · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
    have h_ineq : k + j ≤ n * k + n + j * n + j := by
      have : k ≤ n * k := by
        have : 1 * k ≤ n * k := Nat.mul_le_mul_right k hn_pos
        omega
      have : 0 ≤ j * n := by omega
      omega
    have h_eq_expanded : n * (k + 1) + j * (n + 1) = n * k + n + j * n + j := by ring
    rw [h_eq_expanded] at h_eq
    omega

lemma g_pair_properties (m n k : ℕ) (hp : term_mod2 m n k = 1) :
  let j := (m - n * (k + 1)) / (n + 1)
  let s := k + j
  term_mod2 m s (n &&& s) = 1 ∧ s ≤ m ∧ n &&& s ≤ s ∧ g_pair m (s, n &&& s) = (n, k) := by
  intro j s
  have hs_eq : s = k + j := rfl
  have h_s_le_m : s ≤ m := s_le_m_of_term m n k hp
  rw [term_mod2_eq_one_iff] at hp
  rcases hp with ⟨h_le, h_div, h_c1, h_c2⟩
  have h_eq : n * (k + 1) + j * (n + 1) = m := by
    have h_div_eq : j * (n + 1) = m - n * (k + 1) := Nat.div_mul_cancel h_div
    omega
  have hk_sub_n : k &&& n = k := and_eq_self_of_choose_mod_two_eq_one n k h_c1
  have hn_disj_j : n &&& j = 0 := land_zero_of_choose_add_eq_one n j h_c2
  have h_k_eq : n &&& s = k := by
    rw [Nat.and_comm]
    exact land_add_eq_left_of_land_zero n k j hk_sub_n hn_disj_j
  have h_le_k_n : k ≤ n := le_of_and_eq_self n k hk_sub_n
  have h_ldiff_n_s : n.ldiff s = n - k := by
    have h_ld : n.ldiff s = n.ldiff (n &&& s) := by
      apply Nat.eq_of_testBit_eq
      intro i
      rw [testBit_ldiff, testBit_ldiff, testBit_land]
      cases testBit n i <;> cases testBit s i <;> rfl
    rw [h_ld, h_k_eq, ← sub_eq_ldiff_of_and_eq_self n k hk_sub_n]
  have h_algebra : s * ((n &&& s) + 1) + (n.ldiff s) * (s + 1) = m := by
    rw [h_k_eq, h_ldiff_n_s]
    have h_sk_j : s - k = j := by rw [hs_eq, Nat.add_sub_cancel_left]
    have h_eq_ring : s * (k + 1) + (n - k) * (s + 1) = n * (s + 1) + (s - k) := by
      rw [h_sk_j]
      zify [h_le_k_n, hs_eq]
      ring
    rw [h_eq_ring, h_sk_j]
    have h_m_expanded : n * (s + 1) + j = n * (k + 1) + j * (n + 1) := by ring
    rw [h_m_expanded, h_eq]
  have h_term1 : s * ((n &&& s) + 1) ≤ m := by omega
  have h_term2 : s + 1 ∣ m - s * ((n &&& s) + 1) := by
    use n.ldiff s
    rw [← h_algebra]
    rw [Nat.add_sub_cancel_left]
    rw [Nat.mul_comm]
  have h_term_div : (m - s * ((n &&& s) + 1)) / (s + 1) = n.ldiff s := by
    rw [← h_algebra]
    rw [Nat.add_sub_cancel_left]
    rw [Nat.mul_div_cancel]
    exact Nat.succ_pos s
  have h_s_choose : (s.choose (n &&& s) : ZMod 2) = 1 := by
    apply choose_mod_two_eq_one_of_and_eq_self
    rw [Nat.and_assoc, Nat.and_self]
  have h_s_j'_choose : ((s + n.ldiff s).choose (n.ldiff s) : ZMod 2) = 1 := by
    apply choose_add_eq_one_of_land_zero
    exact land_ldiff_self_right s n
  have h_term_mod2_s : term_mod2 m s (n &&& s) = 1 := by
    rw [term_mod2_eq_one_iff]
    rw [h_term_div]
    refine ⟨h_term1, h_term2, h_s_choose, h_s_j'_choose⟩
  refine ⟨h_term_mod2_s, h_s_le_m, ?_, ?_⟩
  · have h_and_self : (n &&& s) &&& s = n &&& s := by
      rw [Nat.and_assoc, Nat.and_self]
    exact le_of_and_eq_self s (n &&& s) h_and_self
  · unfold g_pair
    simp only [h_k_eq]
    have h_s'_eq : k + (m - s * (k + 1)) / (s + 1) = n := by
      rw [h_k_eq] at h_term_div
      rw [h_term_div, h_ldiff_n_s]
      omega
    rw [h_s'_eq]
    have h_snd_eq : s &&& n = k := by
      rw [Nat.and_comm, h_k_eq]
    rw [h_snd_eq]
