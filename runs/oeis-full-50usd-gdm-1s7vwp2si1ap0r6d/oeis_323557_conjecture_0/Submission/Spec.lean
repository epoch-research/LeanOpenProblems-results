import FormalConjectures.Util.ProblemImports

open Nat

/--
A323557: G.f.: $\sum_{n\ge 0} x^n \cdot \frac{(1 + x^n)^n}{(1 + x^{n+1})^{n+1}}$.
The $m$-th term $a(m)$ is the coefficient of $x^m$, which is explicitly given by the sum:
$$ a(m) = \sum_{n=0}^m \sum_{k=0}^n \binom{n}{k} (-1)^j \binom{n+j}{j},$$
where $j = \frac{m - n(k+1)}{n+1}$, and the term is zero unless $j$ is a natural number.
-/
def a (m : ℕ) : ℤ :=
  Finset.sum (Finset.range (m + 1)) fun n =>
    Finset.sum (Finset.range (n + 1)) fun k =>
      let exp_x_num := n * (k + 1)
      if exp_x_num ≤ m then
        let remainder := m - exp_x_num
        if (n + 1) ∣ remainder then
          let j : ℕ := remainder / (n + 1)
          let c₁ : ℤ := (n.choose k)
          let c₂ : ℤ := (choose (n + j) j)
          let sign : ℤ := if Even j then 1 else -1
          sign * c₁ * c₂
        else
          0
      else
        0

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

lemma sum_mod2_eq_zero_of_free_involution {α : Type*} [DecidableEq α] (S : Finset α)
  (g : α → α) (hg : ∀ x ∈ S, g x ∈ S ∧ g (g x) = x ∧ g x ≠ x)
  (f : α → ZMod 2) (hf : ∀ x ∈ S, f (g x) = f x) :
  S.sum f = 0 := by
  generalize h_card : S.card = c
  induction c using Nat.strong_induction_on generalizing S with
  | h c ih =>
  by_cases hS : S.Nonempty
  · obtain ⟨x, hx⟩ := hS
    have hgx : g x ∈ S := (hg x hx).1
    have hggx : g (g x) = x := (hg x hx).2.1
    have hg_ne : g x ≠ x := (hg x hx).2.2
    let S' := S.erase x |>.erase (g x)
    have h_S'_card : S'.card < S.card := by
      have hg_mem : g x ∈ S.erase x := by
        rw [Finset.mem_erase]
        exact ⟨hg_ne, hgx⟩
      rw [Finset.card_erase_of_mem hg_mem, Finset.card_erase_of_mem hx]
      have : S.card > 0 := Finset.card_pos.mpr ⟨x, hx⟩
      omega
    have hg' : ∀ y ∈ S', g y ∈ S' ∧ g (g y) = y ∧ g y ≠ y := by
      intro y hy
      rw [Finset.mem_erase, Finset.mem_erase] at hy
      have hy_S : y ∈ S := hy.2.2
      have hgy : g y ∈ S := (hg y hy_S).1
      have hggy : g (g y) = y := (hg y hy_S).2.1
      have hgy_ne : g y ≠ y := (hg y hy_S).2.2
      refine ⟨?_, hggy, hgy_ne⟩
      rw [Finset.mem_erase, Finset.mem_erase]
      refine ⟨?_, ?_, hgy⟩
      · intro h
        have h_eq : g (g y) = g (g x) := congr_arg g h
        rw [hggy, hggx] at h_eq
        exact hy.2.1 h_eq
      · intro h
        have h_eq : g (g y) = g x := congr_arg g h
        rw [hggy] at h_eq
        exact hy.1 h_eq
    have hf' : ∀ y ∈ S', f (g y) = f y := by
      intro y hy
      rw [Finset.mem_erase, Finset.mem_erase] at hy
      exact hf y hy.2.2
    have h_S'_card_c : S'.card < c := by
      rw [← h_card]
      exact h_S'_card
    have h_sum_S' := ih S'.card h_S'_card_c S' hg' hf' rfl
    have h_split : S = S' ∪ {x, g x} := by
      ext y
      simp [S']
      by_cases h_yx : y = x
      · simp [h_yx, hx]
      · by_cases h_ygx : y = g x
        · simp [h_ygx, hgx]
        · simp [h_yx, h_ygx]
    rw [h_split]
    have h_disj : Disjoint S' {x, g x} := by
      rw [Finset.disjoint_insert_right, Finset.disjoint_singleton_right]
      simp [S']
    rw [Finset.sum_union h_disj]
    rw [h_sum_S']
    have h_sum_doublet : ({x, g x} : Finset α).sum f = 0 := by
      rw [Finset.sum_pair hg_ne.symm]
      rw [hf x hx]
      have h_double : ∀ (y : ZMod 2), y + y = 0 := by decide
      exact h_double (f x)
    rw [h_sum_doublet, zero_add]
  · rw [Finset.not_nonempty_iff_eq_empty] at hS
    rw [hS]
    exact Finset.sum_empty

def AllPairs (m : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Iic m ×ˢ Finset.Iic m).filter (fun p => p.2 ≤ p.1)

lemma double_sum_eq_sum_all_pairs (m : ℕ) (f : ℕ → ℕ → ZMod 2) :
  Finset.sum (Finset.range (m + 1)) (fun n => Finset.sum (Finset.range (n + 1)) (fun k => f n k)) =
  (AllPairs m).sum (fun p => f p.1 p.2) := by
  have h_range : ∀ (x : ℕ), Finset.range (x + 1) = Finset.Iic x := by
    intro x
    ext y
    simp only [Finset.mem_range, Finset.mem_Iic, Nat.lt_succ_iff]
  rw [h_range m]
  simp_rw [h_range]
  unfold AllPairs
  rw [Finset.sum_filter]
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro n hn
  have hn_le : n ≤ m := Finset.mem_Iic.mp hn
  have h_split : Finset.Iic m = Finset.Iic n ∪ (Finset.Iic m \ Finset.Iic n) := by
    ext x
    simp only [Finset.mem_Iic, Finset.mem_union, Finset.mem_sdiff]
    omega
  rw [h_split]
  have h_disj : Disjoint (Finset.Iic n) (Finset.Iic m \ Finset.Iic n) := by
    rw [Finset.disjoint_iff_ne]
    intro x hx y hy
    simp only [Finset.mem_Iic, Finset.mem_sdiff] at hx hy
    omega
  rw [Finset.sum_union h_disj]
  have h_zero : ((Finset.Iic m \ Finset.Iic n) : Finset ℕ).sum (fun x => if x ≤ n then f n x else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    simp only [Finset.mem_sdiff, Finset.mem_Iic] at hx
    have : ¬ x ≤ n := hx.2
    simp [this]
  rw [h_zero, add_zero]
  apply Finset.sum_congr rfl
  intro x hx
  simp only [Finset.mem_Iic] at hx
  simp [hx]

lemma a_cast_eq_sum (m : ℕ) : (a m : ZMod 2) = Finset.sum (Finset.range (m + 1)) (fun n => Finset.sum (Finset.range (n + 1)) (fun k => term_mod2 m n k)) := by
  unfold a term_mod2
  push_cast
  congr 1 with n
  congr 1 with k
  split_ifs
  · ring
  · have h_neg : ∀ (y : ZMod 2), -y = y := by decide
    rw [h_neg]
    ring
  · rfl
  · rfl

lemma sum_eq_card_filter (m : ℕ) :
  (AllPairs m).sum (fun p => term_mod2 m p.1 p.2) = (((AllPairs m).filter (fun p => term_mod2 m p.1 p.2 = 1)).card : ZMod 2) := by
  have h_eq : (fun p => term_mod2 m p.1 p.2) = (fun (p : ℕ × ℕ) => if term_mod2 m p.1 p.2 = 1 then (1 : ZMod 2) else (0 : ZMod 2)) := by
    ext p
    by_cases h : term_mod2 m p.1 p.2 = 1
    · simp [h]
    · have h0 : term_mod2 m p.1 p.2 = 0 := by
        generalize term_mod2 m p.1 p.2 = x at *
        fin_cases x
        · rfl
        · contradiction
      rw [h0]
      rfl
  rw [h_eq]
  rw [← Finset.sum_filter]
  simp

lemma odd_iff_zmod (x : ℤ) : Odd x ↔ (x : ZMod 2) = 1 := by
  constructor
  · rintro ⟨k, rfl⟩
    push_cast
    have : (2 : ZMod 2) = 0 := rfl
    rw [this]
    ring
  · intro h
    rcases Int.even_or_odd x with h_even | h_odd
    · rcases h_even with ⟨k, rfl⟩
      push_cast at h
      have h_zero : ∀ (y : ZMod 2), y + y = 0 := by decide
      rw [h_zero] at h
      contradiction
    · exact h_odd

/-- oeis_323557_conjecture_0: Odd terms occur only at positions n*(n+1) for n >= 0 (conjecture; verified for initial 32600 terms). -/
theorem oeis_323557_conjecture_0 (m : ℕ) : Odd (a m) → ∃ n : ℕ, m = n * (n + 1) := by
  intro h_odd
  rw [odd_iff_zmod] at h_odd
  rw [a_cast_eq_sum] at h_odd
  rw [double_sum_eq_sum_all_pairs] at h_odd
  rw [sum_eq_card_filter] at h_odd
  set S := (AllPairs m).filter (fun p => term_mod2 m p.1 p.2 = 1)
  have h_S_ne : S.card ≠ 0 := by
    intro hc
    rw [hc] at h_odd
    contradiction
  have h_nonempty : S.Nonempty := Finset.card_pos.mp (Nat.pos_of_ne_zero h_S_ne)
  by_contra h_no_n
  push_neg at h_no_n
  have hg : ∀ p ∈ S, g_pair m p ∈ S ∧ g_pair m (g_pair m p) = p ∧ g_pair m p ≠ p := by
    intro p hp
    rw [Finset.mem_filter] at hp
    rcases hp with ⟨hp_all, hp_term⟩
    have h_prop := g_pair_properties m p.1 p.2 hp_term
    rcases h_prop with ⟨h_term_g, h_s_le, h_and_le, h_inv⟩
    have hg_mem : g_pair m p ∈ S := by
      rw [Finset.mem_filter]
      refine ⟨?_, h_term_g⟩
      unfold AllPairs
      rw [Finset.mem_filter, Finset.mem_product]
      simp only [Finset.mem_Iic]
      refine ⟨⟨h_s_le, ?_⟩, h_and_le⟩
      exact le_trans h_and_le h_s_le
    have hg_inv : g_pair m (g_pair m p) = p := by
      have : g_pair m p = (p.2 + (m - p.1 * (p.2 + 1)) / (p.1 + 1), p.1 &&& (p.2 + (m - p.1 * (p.2 + 1)) / (p.1 + 1))) := rfl
      rw [this, h_inv]
    have hg_ne : g_pair m p ≠ p := by
      intro hc
      have h_eq : g_pair m p = p := hc
      have h_eq_1 : (g_pair m p).1 = p.1 := congr_arg Prod.fst h_eq
      have h_eq_2 : (g_pair m p).2 = p.2 := congr_arg Prod.snd h_eq
      unfold g_pair at h_eq_1 h_eq_2
      dsimp at h_eq_1 h_eq_2
      have hp1_eq : p.1 = p.2 := by
        rw [h_eq_1] at h_eq_2
        rw [Nat.and_self] at h_eq_2
        exact h_eq_2
      have hj_zero : (m - p.1 * (p.2 + 1)) / (p.1 + 1) = 0 := by
        have : p.2 + (m - p.1 * (p.2 + 1)) / (p.1 + 1) = p.1 := h_eq_1
        rw [hp1_eq] at this
        omega
      have h_div_prop : p.1 + 1 ∣ m - p.1 * (p.2 + 1) := by
        rw [term_mod2_eq_one_iff] at hp_term
        exact hp_term.2.1
      have h_rem_zero : m - p.1 * (p.2 + 1) = 0 := by
        have h_div_eq : (m - p.1 * (p.2 + 1)) / (p.1 + 1) * (p.1 + 1) = m - p.1 * (p.2 + 1) := Nat.div_mul_cancel h_div_prop
        rw [hj_zero, zero_mul] at h_div_eq
        exact h_div_eq.symm
      have h_m_eq : m = p.1 * (p.1 + 1) := by
        rw [term_mod2_eq_one_iff] at hp_term
        have h_le_p1 : p.1 * (p.2 + 1) ≤ m := hp_term.1
        rw [← hp1_eq] at h_rem_zero
        rw [← hp1_eq] at h_le_p1
        omega
      exact h_no_n p.1 h_m_eq
    exact ⟨hg_mem, hg_inv, hg_ne⟩
  have h_sum_zero := sum_mod2_eq_zero_of_free_involution S (g_pair m) hg (fun _ => 1) (by simp)
  have h_sum_S : S.sum (fun _ => 1) = (S.card : ZMod 2) := by simp
  rw [h_sum_S] at h_sum_zero
  rw [h_sum_zero] at h_odd
  contradiction
