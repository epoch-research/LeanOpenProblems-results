import FormalConjectures.Util.ProblemImports

open Nat Int

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


lemma ca_rule_167_bound (L C R : ℕ) : ca_rule_167 L C R ≤ 1 := by
  dsimp [ca_rule_167]
  omega

lemma ca_state_bound (t : ℕ) (x : ℤ) : ca_state t x ≤ 1 := by
  cases t
  · dsimp [ca_state]
    split_ifs <;> omega
  · dsimp [ca_state]
    apply ca_rule_167_bound

lemma ca_rule_167_cases (L C R : ℕ) (hL : L ≤ 1) (hC : C ≤ 1) (hR : R ≤ 1) :
    ca_rule_167 L C R =
    if L = 0 ∧ C = 0 ∧ R = 0 then 1 else
    if L = 0 ∧ C = 0 ∧ R = 1 then 1 else
    if L = 0 ∧ C = 1 ∧ R = 0 then 1 else
    if L = 0 ∧ C = 1 ∧ R = 1 then 0 else
    if L = 1 ∧ C = 0 ∧ R = 0 then 0 else
    if L = 1 ∧ C = 0 ∧ R = 1 then 1 else
    if L = 1 ∧ C = 1 ∧ R = 0 then 0 else
    if L = 1 ∧ C = 1 ∧ R = 1 then 1 else 0 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hL with rfl | rfl <;>
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hC with rfl | rfl <;>
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hR with rfl | rfl <;>
  decide

lemma ca_state_one (x : ℤ) : ca_state 1 x = if x = 1 then 0 else 1 := by
  dsimp [ca_state]
  by_cases hx1 : x = 1
  · subst hx1
    rfl
  · by_cases hx0 : x = 0
    · subst hx0
      rfl
    · by_cases hxm1 : x = -1
      · subst hxm1
        rfl
      · have h1 : x - 1 ≠ 0 := by omega
        have h2 : x ≠ 0 := hx0
        have h3 : x + 1 ≠ 0 := by omega
        rw [if_neg h1, if_neg h2, if_neg h3]
        rw [if_neg hx1]
        rfl

def v (t : ℕ) (x : ℤ) : ℕ := 1 - ca_state t x

lemma v_bound (t : ℕ) (x : ℤ) : v t x ≤ 1 := by
  dsimp [v]
  omega

lemma v_one (x : ℤ) : v 1 x = if x = 1 then 1 else 0 := by
  dsimp [v]
  rw [ca_state_one x]
  split_ifs <;> rfl

lemma v_eq_one_iff_ca_state_eq_zero (t : ℕ) (x : ℤ) : v t x = 1 ↔ ca_state t x = 0 := by
  dsimp [v]
  have := ca_state_bound t x
  omega

lemma v_eq_zero_iff_ca_state_eq_one (t : ℕ) (x : ℤ) : v t x = 0 ↔ ca_state t x = 1 := by
  dsimp [v]
  have := ca_state_bound t x
  omega

lemma ca_state_step (t : ℕ) (x : ℤ) :
    ca_state (t + 1) x = ca_rule_167 (ca_state t (x - 1)) (ca_state t x) (ca_state t (x + 1)) := by
  rfl

lemma v_step (t : ℕ) (x : ℤ) :
    v (t + 1) x =
    if v t (x - 1) = 0 ∧ v t x = 0 ∧ v t (x + 1) = 0 then 0 else
    if v t (x - 1) = 0 ∧ v t x = 0 ∧ v t (x + 1) = 1 then 1 else
    if v t (x - 1) = 0 ∧ v t x = 1 ∧ v t (x + 1) = 0 then 0 else
    if v t (x - 1) = 0 ∧ v t x = 1 ∧ v t (x + 1) = 1 then 1 else
    if v t (x - 1) = 1 ∧ v t x = 0 ∧ v t (x + 1) = 0 then 1 else
    if v t (x - 1) = 1 ∧ v t x = 0 ∧ v t (x + 1) = 1 then 0 else
    if v t (x - 1) = 1 ∧ v t x = 1 ∧ v t (x + 1) = 0 then 0 else
    if v t (x - 1) = 1 ∧ v t x = 1 ∧ v t (x + 1) = 1 then 0 else 0 := by
  dsimp [v]
  rw [ca_state_step]
  have ha : ca_state t (x - 1) ≤ 1 := ca_state_bound t (x - 1)
  have hb : ca_state t x ≤ 1 := ca_state_bound t x
  have hc : ca_state t (x + 1) ≤ 1 := ca_state_bound t (x + 1)
  generalize h_a : ca_state t (x - 1) = a
  generalize h_b : ca_state t x = b
  generalize h_c : ca_state t (x + 1) = c
  rw [h_a] at ha
  rw [h_b] at hb
  rw [h_c] at hc
  rw [ca_rule_167_cases _ _ _ ha hb hc]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ha with rfl | rfl <;>
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with rfl | rfl <;>
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc with rfl | rfl <;> rfl

lemma v_parity (t : ℕ) (ht : 1 ≤ t) : ∀ x : ℤ, v t x = 1 → (x - (t : ℤ)) % 2 = 0 := by
  induction' t, ht using Nat.le_induction with t ht ih
  · intro x hx
    rw [v_one] at hx
    split_ifs at hx with h
    · subst h
      decide
  · intro x hx
    rw [v_step] at hx
    have ha : v t (x - 1) ≤ 1 := v_bound t (x - 1)
    have hb : v t x ≤ 1 := v_bound t x
    have hc : v t (x + 1) ≤ 1 := v_bound t (x + 1)
    generalize h_a : v t (x - 1) = a at hx ha
    generalize h_b : v t x = b at hx hb
    generalize h_c : v t (x + 1) = c at hx hc
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ha with rfl | rfl
    · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with rfl | rfl
      · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc with rfl | rfl
        · contradiction
        · have := ih (x + 1) h_c
          push_cast
          have h_eq : x - (↑t + 1) = (x + 1) - ↑t - 2 := by omega
          rw [h_eq]
          have h_mod : ((x + 1) - ↑t - 2) % 2 = ((x + 1) - ↑t) % 2 := by omega
          rw [h_mod, this]
      · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc with rfl | rfl
        · contradiction
        · have := ih (x + 1) h_c
          push_cast
          have h_eq : x - (↑t + 1) = (x + 1) - ↑t - 2 := by omega
          rw [h_eq]
          have h_mod : ((x + 1) - ↑t - 2) % 2 = ((x + 1) - ↑t) % 2 := by omega
          rw [h_mod, this]
    · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with rfl | rfl
      · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc with rfl | rfl
        · have := ih (x - 1) h_a
          push_cast
          have h_eq : x - (↑t + 1) = (x - 1) - ↑t := by omega
          rw [h_eq, this]
        · contradiction
      · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc with rfl | rfl
        · contradiction
        · contradiction

lemma Int.mod_two_sub (a b : ℤ) : (a - b) % 2 = ((a % 2) - (b % 2)) % 2 := by omega

lemma v_no_adj_ones (t : ℕ) (ht : 1 ≤ t) (x : ℤ) (hx : v t x = 1) : v t (x + 1) = 0 := by
  have h1 := v_parity t ht x hx
  by_contra h2
  have h2' : v t (x + 1) = 1 := by
    have := v_bound t (x + 1)
    omega
  have h3 := v_parity t ht (x + 1) h2'
  have h4 : ((x + 1 - ↑t) - (x - ↑t)) % 2 = (0 - 0) % 2 := by
    rw [Int.mod_two_sub, h1, h3]
  have h5 : ((x + 1 - ↑t) - (x - ↑t)) = 1 := by omega
  rw [h5] at h4
  revert h4
  decide

lemma v_step_simplified (t : ℕ) (ht : 1 ≤ t) (x : ℤ) :
    v (t + 1) x = (v t (x - 1) + v t (x + 1)) % 2 := by
  rw [v_step]
  have h_adj1 : ¬ (v t (x - 1) = 1 ∧ v t x = 1) := by
    intro h
    have := v_no_adj_ones t ht (x - 1) h.1
    have h_eq : x - 1 + 1 = x := by omega
    rw [h_eq] at this
    omega
  have h_adj2 : ¬ (v t x = 1 ∧ v t (x + 1) = 1) := by
    intro h
    have := v_no_adj_ones t ht x h.1
    omega
  have hL := v_bound t (x - 1)
  have hC := v_bound t x
  have hR := v_bound t (x + 1)
  generalize h_a : v t (x - 1) = a at h_adj1 hL ⊢
  generalize h_b : v t x = b at h_adj1 h_adj2 hC ⊢
  generalize h_c : v t (x + 1) = c at h_adj2 hR ⊢
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hL with rfl | rfl
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hC with rfl | rfl
    · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hR with rfl | rfl <;> decide
    · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hR with rfl | rfl
      · decide
      · tauto
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hC with rfl | rfl
    · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hR with rfl | rfl <;> decide
    · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hR with rfl | rfl <;> tauto


def f (k : ℕ) (x : ℤ) : ℕ :=
  if (x - 1 + (k : ℤ)) % 2 = 0 ∧ 0 ≤ x - 1 + k then (Nat.choose k ((x - 1 + k) / 2).toNat) % 2 else 0

lemma f_zero (x : ℤ) : f 0 x = if x = 1 then 1 else 0 := by
  dsimp [f]
  by_cases hx : x = 1
  · subst hx
    simp
  · by_cases hx2 : (x - 1) % 2 = 0 ∧ 0 ≤ x - 1
    · rw [if_pos (by omega)]
      have h_pos : 0 < (x - 1) / 2 := by omega
      have h_nat : 0 < ((x - 1) / 2).toNat := by omega
      have h_choose : Nat.choose 0 ((x - 1) / 2).toNat = 0 := by
        apply Nat.choose_eq_zero_of_lt
        omega
      have h_eq : ((x - 1 + 0) / 2).toNat = ((x - 1) / 2).toNat := by omega
      rw [h_eq, h_choose]
      simp [hx]
    · rw [if_neg (by omega)]
      by_cases hx3 : x = 1 <;> simp_all

lemma choose_mod_two_succ_succ (n k : ℕ) :
    (n + 1).choose (k + 1) % 2 = (n.choose k + n.choose (k + 1)) % 2 := by
  rw [Nat.choose_succ_succ]

lemma choose_mod_two_succ_zero (n : ℕ) :
    (n + 1).choose 0 % 2 = (n.choose 0) % 2 := by
  simp

lemma Int.toNat_sub_one (a : ℤ) (h : 0 < a) : (a - 1).toNat = a.toNat - 1 := by
  omega

lemma f_step (k : ℕ) (x : ℤ) : f (k + 1) x = (f k (x - 1) + f k (x + 1)) % 2 := by
  dsimp [f]
  have h_par1 : (x - 1 + (k + 1 : ℤ)) = x + k := by omega
  have h_par2 : (x - 1 - 1 + (k : ℤ)) = x - 2 + k := by omega
  have h_par3 : (x + 1 - 1 + (k : ℤ)) = x + k := by omega
  have h_par_eq : (x + k) % 2 = (x - 2 + k) % 2 := by omega
  by_cases h_par : (x + k) % 2 = 0
  · by_cases h_pos : 0 ≤ x + k
    · by_cases h_pos2 : 0 ≤ x - 2 + k
      · rw [if_pos (by omega), if_pos (by omega), if_pos (by omega)]
        have h_div1 : (x - 1 + (k + 1 : ℤ)) / 2 = (x + k) / 2 := by omega
        have h_div2 : (x - 1 - 1 + (k : ℤ)) / 2 = (x + k) / 2 - 1 := by omega
        have h_div3 : (x + 1 - 1 + (k : ℤ)) / 2 = (x + k) / 2 := by omega
        rw [h_div1, h_div2, h_div3]
        have h_pos_div : 0 < (x + k) / 2 := by omega
        have h_nat_div2 : ((x + k) / 2 - 1).toNat = ((x + k) / 2).toNat - 1 := by
          apply Int.toNat_sub_one _ h_pos_div
        rw [h_nat_div2]
        let n := ((x + k) / 2).toNat - 1
        have h_succ : ((x + k) / 2).toNat = n + 1 := by
          have h_nat_div : 0 < ((x + k) / 2).toNat := by omega
          dsimp [n]
          omega
        have h_rw1 : Nat.choose (k + 1) ((x + k) / 2).toNat = Nat.choose (k + 1) (n + 1) := by rw [h_succ]
        have h_rw3 : Nat.choose k ((x + k) / 2).toNat = Nat.choose k (n + 1) := by rw [h_succ]
        rw [h_rw1, h_rw3]
        have h_mod : (k.choose n % 2 + k.choose (n + 1) % 2) % 2 = (k.choose n + k.choose (n + 1)) % 2 := by omega
        rw [h_mod]
        exact choose_mod_two_succ_succ k n
      · have h_zero : x + k = 0 := by omega
        rw [if_pos (by omega), if_neg (by omega), if_pos (by omega)]
        have h_div1 : (x - 1 + (k + 1 : ℤ)) / 2 = 0 := by omega
        have h_div3 : (x + 1 - 1 + (k : ℤ)) / 2 = 0 := by omega
        rw [h_div1, h_div3]
        simp
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]


lemma v_eq_f (k : ℕ) : ∀ x : ℤ, v (k + 1) x = f k x := by
  induction' k with k ih
  · intro x
    rw [v_one x, f_zero x]
  · intro x
    rw [v_step_simplified (k + 1) (by omega) x]
    rw [ih (x - 1), ih (x + 1)]
    rw [← f_step k x]

lemma f_even (m : ℕ) : f (2 * m) 0 = 0 := by
  dsimp [f]
  by_cases hm : m = 0
  · subst hm
    simp
  · rw [if_neg (by omega)]

lemma f_odd (m : ℕ) (hm : 1 ≤ m) : f (2 * m - 1) 0 = Nat.choose (2 * m - 1) (m - 1) % 2 := by
  dsimp [f]
  split_ifs with h_cond
  · have h_div : (-1 + (↑(2 * m - 1) : ℤ)) / 2 = (m : ℤ) - 1 := by omega
    rw [h_div]
    have h_nat : ((m : ℤ) - 1).toNat = m - 1 := by omega
    rw [h_nat]
  · have : False := by omega
    contradiction

lemma ca_state_even (m : ℕ) (hm : 1 ≤ m) : ca_state (2 * m) 0 = 1 - Nat.choose (2 * m - 1) (m - 1) % 2 := by
  have := v_eq_f (2 * m - 1) 0
  have h_eq : 2 * m - 1 + 1 = 2 * m := by omega
  rw [h_eq] at this
  rw [f_odd m hm] at this
  have h_ca : ca_state (2 * m) 0 = 1 - v (2 * m) 0 := by
    dsimp [v]
    have := ca_state_bound (2 * m) 0
    omega
  rw [h_ca, this]

lemma ca_state_odd (m : ℕ) : ca_state (2 * m + 1) 0 = 1 := by
  have := v_eq_f (2 * m) 0
  have h_eq : 2 * m + 1 = 2 * m + 1 := by omega
  rw [f_even m] at this
  have h_ca : ca_state (2 * m + 1) 0 = 1 - v (2 * m + 1) 0 := by
    dsimp [v]
    have := ca_state_bound (2 * m + 1) 0
    omega
  rw [h_ca, this]


lemma n_dvd_two_pow (n : ℕ) (hn : 2 ≤ n) : n ∣ 2 ^ (n + 1) ↔ ∃ k, n = 2 ^ k := by
  constructor
  · intro h
    have h1 : Nat.Prime 2 := Nat.prime_two
    have h2 := (Nat.dvd_prime_pow h1).mp h
    rcases h2 with ⟨k, _, hk2⟩
    exact ⟨k, hk2⟩
  · intro h
    rcases h with ⟨k, hk⟩
    subst hk
    apply Nat.pow_dvd_pow
    have h_lt : k < 2 ^ k := Nat.lt_pow_self (by decide)
    omega

lemma oeis_floor_term_eq_one (n : ℕ) (hn : 2 ≤ n) : oeis_floor_term n = 1 ↔ ∃ k, n = 2 ^ k := by
  dsimp [oeis_floor_term]
  rw [if_neg (by omega)]
  have h_dvd : (2 ^ (n + 1)) % n = 0 ↔ n ∣ 2 ^ (n + 1) := Nat.dvd_iff_mod_eq_zero.symm
  have h_pow := n_dvd_two_pow n hn
  split_ifs with h_mod
  · have h_div : n ∣ 2 ^ (n + 1) := h_dvd.mp h_mod
    have h_ex := h_pow.mp h_div
    tauto
  · have h_ndiv : ¬ n ∣ 2 ^ (n + 1) := mt h_dvd.mpr h_mod
    have h_nex : ¬ ∃ k, n = 2 ^ k := mt h_pow.mpr h_ndiv
    tauto

lemma choose_mod_two_eq (n k : ℕ) :
    choose n k % 2 = (choose (n % 2) (k % 2) * choose (n / 2) (k / 2)) % 2 := by
  have _inst : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := n) (k := k) (p := 2)
  exact h


lemma choose_two_j_j_mod_two_eq_zero (j : ℕ) (hj : 1 ≤ j) : choose (2 * j) j % 2 = 0 := by
  induction' j using Nat.strong_induction_on with j ih
  have h := choose_mod_two_eq (2 * j) j
  by_cases h_par : j % 2 = 1
  · have h_mod_2 : (2 * j) % 2 = 0 := by omega
    rw [h_par, h_mod_2] at h
    have h01 : choose 0 1 = 0 := by rfl
    rw [h01] at h
    have hm : 0 * choose ((2 * j) / 2) (j / 2) = 0 := MulZeroClass.zero_mul _
    rw [hm] at h
    exact h
  · have h_par2 : j % 2 = 0 := by omega
    have h_mod_2 : (2 * j) % 2 = 0 := by omega
    rw [h_par2, h_mod_2] at h
    have h00 : choose 0 0 = 1 := by rfl
    rw [h00] at h
    have h_div1 : (2 * j) / 2 = j := by omega
    rw [h_div1] at h
    have hj_even : ∃ l, j = 2 * l := by
      use j / 2
      omega
    rcases hj_even with ⟨l, hl⟩
    subst hl
    by_cases hl_zero : l = 0
    · omega
    · have hl_pos : 1 ≤ l := by omega
      have h_div2 : (2 * l) / 2 = l := by omega
      rw [h_div2] at h
      have h_mul : 1 * choose (2 * l) l = choose (2 * l) l := by omega
      rw [h_mul] at h
      have h_ih := ih l (by omega) hl_pos
      rw [h_ih] at h
      exact h


lemma choose_mod_two_odd (m : ℕ) (hm : 1 ≤ m) :
    choose (2 * m - 1) (m - 1) % 2 = 1 ↔ ∃ k, 2 * m = 2 ^ k := by
  induction' m using Nat.strong_induction_on with m ih
  by_cases h1 : m = 1
  · subst h1
    simp
    use 1
    rfl
  · have h_m : 1 < m := by omega
    have h := choose_mod_two_eq (2 * m - 1) (m - 1)
    by_cases h_par : (m - 1) % 2 = 1
    · have h_mod_2 : (2 * m - 1) % 2 = 1 := by omega
      rw [h_par, h_mod_2] at h
      have h11 : choose 1 1 = 1 := by rfl
      rw [h11] at h
      have hm1 : 1 * choose ((2 * m - 1) / 2) ((m - 1) / 2) = choose ((2 * m - 1) / 2) ((m - 1) / 2) := by omega
      rw [hm1] at h
      have hj : ∃ j, m - 1 = 2 * j + 1 := by
        use (m - 1) / 2
        omega
      rcases hj with ⟨j, hj_eq⟩
      have hj_pos : 1 ≤ j + 1 := by omega
      have hm_eq : m = 2 * (j + 1) := by omega
      have h_div1 : (2 * m - 1) / 2 = 2 * (j + 1) - 1 := by omega
      have h_div2 : (m - 1) / 2 = j + 1 - 1 := by omega
      rw [h_div1, h_div2] at h
      have h_ih := ih (j + 1) (by omega) hj_pos
      rw [h, h_ih]
      constructor
      · intro ⟨k, hk⟩
        use k + 1
        have h_pow : 2 ^ (k + 1) = 2 ^ k * 2 := by ring
        rw [h_pow, ← hk]
        omega
      · intro ⟨k, hk⟩
        cases' k with a
        · omega
        · use a
          have h_pow : 2 ^ (a + 1) = 2 ^ a * 2 := by ring
          rw [h_pow] at hk
          omega
    · have h_par_0 : (m - 1) % 2 = 0 := by omega
      have h_mod_2 : (2 * m - 1) % 2 = 1 := by omega
      rw [h_par_0, h_mod_2] at h
      have h10 : choose 1 0 = 1 := by rfl
      rw [h10] at h
      have hm1 : 1 * choose ((2 * m - 1) / 2) ((m - 1) / 2) = choose ((2 * m - 1) / 2) ((m - 1) / 2) := by omega
      rw [hm1] at h
      have hj : ∃ j, m - 1 = 2 * j := by
        use (m - 1) / 2
        omega
      rcases hj with ⟨j, hj_eq⟩
      have hj_pos : 1 ≤ j := by omega
      have hm_eq : m = 2 * j + 1 := by omega
      have h_div1 : (2 * m - 1) / 2 = 2 * j := by omega
      have h_div2 : (m - 1) / 2 = j := by omega
      rw [h_div1, h_div2] at h
      have h_zero := choose_two_j_j_mod_two_eq_zero j hj_pos
      rw [h_zero] at h
      rw [h]
      constructor
      · intro h_eq_one
        omega
      · intro ⟨k, hk⟩
        have h_mod_4_left : (2 * m) % 4 = 2 := by
          rw [hm_eq]
          have : 2 * (2 * j + 1) = 4 * j + 2 := by omega
          rw [this]
          omega
        have h_mod_4_right : (2 ^ k) % 4 = 0 := by
          have hk_ge : 2 ≤ k := by
            have : 6 ≤ 2 ^ k := by
              rw [← hk]
              omega
            cases' k with k_1
            · omega
            · cases' k_1 with k_2
              · omega
              · omega
          have : 2 ^ k = 4 * 2 ^ (k - 2) := by
            have h_pow : 2 ^ k = 2 ^ 2 * 2 ^ (k - 2) := by
              rw [← pow_add]
              congr 1
              omega
            rw [h_pow]
            rfl
          rw [this]
          omega
        rw [hk] at h_mod_4_left
        omega


lemma ca_state_zero_iff_pow_two (n : ℕ) (hn : 2 ≤ n) : ca_state n 0 = 0 ↔ ∃ k, n = 2 ^ k := by
  by_cases h_odd : n % 2 = 1
  · have h_ca : ca_state n 0 = 1 := by
      have : ∃ m, n = 2 * m + 1 := by
        use n / 2
        omega
      rcases this with ⟨m, hm⟩
      subst hm
      apply ca_state_odd
    rw [h_ca]
    constructor
    · intro h
      omega
    · intro ⟨k, hk⟩
      have h_mod : (2 ^ k) % 2 = 0 := by
        cases' k with a
        · omega
        · have : 2 ^ (a + 1) = 2 ^ a * 2 := by ring
          rw [this]
          omega
      rw [hk] at h_odd
      omega
  · have h_even : ∃ m, n = 2 * m := by
      use n / 2
      omega
    rcases h_even with ⟨m, hm⟩
    have hm_pos : 1 ≤ m := by omega
    have h_ca : ca_state n 0 = 1 - choose (2 * m - 1) (m - 1) % 2 := by
      subst hm
      apply ca_state_even m hm_pos
    rw [h_ca]
    have h_choose := choose_mod_two_odd m hm_pos
    constructor
    · intro h
      have h1 : choose (2 * m - 1) (m - 1) % 2 = 1 := by omega
      rw [h_choose] at h1
      subst hm
      exact h1
    · intro h
      have h1 : choose (2 * m - 1) (m - 1) % 2 = 1 := by
        rw [h_choose]
        subst hm
        exact h
      omega

lemma middle_column_bit_eq_one_sub_floor_term (n : ℕ) (hn : 2 ≤ n) :
    middle_column_bit n = 1 - oeis_floor_term n := by
  dsimp [middle_column_bit]
  have h_floor := oeis_floor_term_eq_one n hn
  have h_ca := ca_state_zero_iff_pow_two n hn
  have h_ca_bound := ca_state_bound n 0
  have h_floor_bound : oeis_floor_term n ≤ 1 := by
    dsimp [oeis_floor_term]
    split_ifs <;> omega
  by_cases h_pow : ∃ k, n = 2 ^ k
  · have h_floor_1 : oeis_floor_term n = 1 := h_floor.mpr h_pow
    have h_ca_0 : ca_state n 0 = 0 := h_ca.mpr h_pow
    omega
  · have h_floor_0 : oeis_floor_term n = 0 := by
      by_contra h
      have : oeis_floor_term n = 1 := by omega
      have := h_floor.mp this
      contradiction
    have h_ca_1 : ca_state n 0 = 1 := by
      by_contra h
      have : ca_state n 0 = 0 := by omega
      have := h_ca.mp this
      contradiction
    omega

lemma a_recurrence (n : ℕ) (hn : 1 ≤ n) : a n = 2 * a (n - 1) + middle_column_bit n := by
  dsimp [a]
  have h_range : Finset.range (n + 1) = insert n (Finset.range n) := by
    exact Finset.range_add_one
  rw [h_range]
  rw [Finset.sum_insert (by simp)]
  have h_sub : n - n = 0 := by omega
  rw [h_sub, pow_zero, mul_one]
  have h_sum : (Finset.range n).sum (fun k => middle_column_bit k * 2 ^ (n - k)) =
      2 * (Finset.range ((n - 1) + 1)).sum (fun k => middle_column_bit k * 2 ^ (n - 1 - k)) := by
    have hn_eq : n = n - 1 + 1 := by omega
    nth_rw 1 [hn_eq]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    have hx_lt : x < n := by have : x < n - 1 + 1 := Finset.mem_range.mp hx; omega
    have h_pow : 2 ^ (n - x) = 2 * 2 ^ (n - 1 - x) := by
      have h1 : n - x = n - 1 - x + 1 := by omega
      rw [h1, pow_add, pow_one, mul_comm]
    rw [h_pow]
    ring
  rw [h_sum]
  ring

lemma oeis_267581_conjecture_0_proof (n : ℕ) (hn : 2 ≤ n) :
    a n = 2 * a (n - 1) + 1 - oeis_floor_term n := by
  have hn1 : 1 ≤ n := by omega
  rw [a_recurrence n hn1]
  rw [middle_column_bit_eq_one_sub_floor_term n hn]
  have h_floor_bound : oeis_floor_term n ≤ 1 := by
    dsimp [oeis_floor_term]
    split_ifs <;> omega
  omega


/--
A267581 conjecture on the recurrence relation.

Assuming the conjecture that the positions of the 0-bits of the middle column ("Rule 167") are given by the sequence A000051, it follows that a possible formula could be: a(n) = 2*a(n-1) + 1 - floor((1/2)^((2^(n+1)) mod n)) with a(0)=1 and a(1)=3 (Not proved, but tested up to n = 10^4). - _Andres Cicuttin_, Mar 29 2016
-/
theorem oeis_267581_conjecture_0 (n : ℕ) (hn : 2 ≤ n) :
  a n = 2 * a (n - 1) + 1 - oeis_floor_term n :=
by exact oeis_267581_conjecture_0_proof n hn

theorem oeis_267581_conjecture_0.disproof : ¬ (type_of% @oeis_267581_conjecture_0) := sorry
