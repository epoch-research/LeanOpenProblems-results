import FormalConjectures.Util.ProblemImports

open Nat Classical

/-- The number whose digits in base 10 are $n$'s digits reversed. -/
def reverse_nat (k : ℕ) : ℕ :=
  ofDigits 10 (digits 10 k).reverse

/--
A062567: First multiple of $n$ whose reverse is also divisible by $n$, or 0 if no such multiple exists.
-/
noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    -- P(k) is the predicate for the multiplier k: k > 0 and n divides the reverse of (k*n).
    let P (k : ℕ) : Prop := k > 0 ∧ n ∣ reverse_nat (k * n)

    -- We check if a solution exists (using classical reasoning, since P is decidable).
    if h_ex : ∃ k, P k then
      -- Nat.find requires a DecidablePred instance, which holds for this property on ℕ.
      have HP : DecidablePred P := by infer_instance
      -- k_min is the smallest multiplier k >= 1.
      let k_min : ℕ := Nat.find h_ex
      k_min * n
    else
      0

def digits10_fuel : ℕ → ℕ → List ℕ
  | 0, _ => []
  | fuel + 1, n =>
    if n = 0 then []
    else (n % 10) :: digits10_fuel fuel (n / 10)

theorem digits10_fuel_eq_digits (fuel n : ℕ) (h : n < fuel) :
    digits10_fuel fuel n = digits 10 n := by
  induction fuel generalizing n with
  | zero =>
    contradiction
  | succ m ih =>
    rw [digits10_fuel]
    split_ifs with hn
    · subst hn
      rw [digits_zero]
    · -- n > 0
      have hn_pos : n > 0 := Nat.pos_of_ne_zero hn
      have h_digits := digits_add_two_add_one 8 (n - 1)
      have h_ten : 8 + 2 = 10 := rfl
      have h_n : (n - 1) + 1 = n := by omega
      rw [h_ten, h_n] at h_digits
      rw [h_digits]
      congr 1
      have h_div : n / 10 < m := by
        have h_lt : n / 10 < n := Nat.div_lt_self hn_pos (by decide)
        omega
      exact ih (n / 10) h_div

theorem reverse_nat_eq_eval (n : ℕ) :
    reverse_nat n = ofDigits 10 (digits10_fuel (n + 1) n).reverse := by
  unfold reverse_nat
  rw [digits10_fuel_eq_digits (n + 1) n (by omega)]

def computable_P (n : ℕ) (k : ℕ) : Bool :=
  (k > 0) && (ofDigits 10 (digits10_fuel (k * n + 1) (k * n)).reverse % n == 0)

lemma computable_P_iff (n k : ℕ) : computable_P n k = true ↔ (k > 0 ∧ n ∣ reverse_nat (k * n)) := by
  dsimp [computable_P]
  rw [Bool.and_eq_true]
  simp [reverse_nat_eq_eval, Nat.dvd_iff_mod_eq_zero]

def computable_forall_lt (n : ℕ) : ℕ → Bool
  | 0 => true
  | i + 1 => (!computable_P n (i + 1)) && computable_forall_lt n i

lemma computable_forall_lt_iff (n m : ℕ) :
    computable_forall_lt n m = true ↔ ∀ i ≤ m, i > 0 → ¬ (n ∣ reverse_nat (i * n)) := by
  induction m with
  | zero =>
    simp [computable_forall_lt]
  | succ m ih =>
    simp [computable_forall_lt, ih]
    have h_false : computable_P n (m + 1) = false ↔ ¬ (computable_P n (m + 1) = true) := by
      exact Bool.eq_false_iff
    constructor
    · rintro ⟨h1, h2⟩ i hi hi_pos
      have h_cases : i = m + 1 ∨ i ≤ m := by omega
      rcases h_cases with rfl | h_lt
      · rw [h_false, computable_P_iff] at h1
        intro h_dvd
        exact h1 ⟨by omega, h_dvd⟩
      · exact h2 i h_lt hi_pos
    · intro h
      constructor
      · rw [h_false, computable_P_iff]
        intro ⟨h_pos, h_dvd⟩
        exact h (m + 1) (by omega) (by omega) h_dvd
      · intro i hi hi_pos
        exact h i (by omega) hi_pos

theorem a_nine : a 9 = 9 := by
  unfold a
  have h0 : ¬ 9 = 0 := by decide
  rw [if_neg h0]
  have h_ex : ∃ k, k > 0 ∧ 9 ∣ reverse_nat (k * 9) := by
    use 1
    rw [← computable_P_iff]
    rfl
  rw [dif_pos h_ex]
  dsimp
  have h_find : Nat.find h_ex = 1 := by
    rw [Nat.find_eq_iff]
    constructor
    · rw [← computable_P_iff]
      rfl
    · intro n hn
      rw [← computable_P_iff]
      have : n = 0 := by omega
      subst this
      decide
  rw [h_find]

theorem a_twenty_seven : a 27 = 999 := by
  unfold a
  have h0 : ¬ 27 = 0 := by decide
  rw [if_neg h0]
  have h_ex : ∃ k, k > 0 ∧ 27 ∣ reverse_nat (k * 27) := by
    use 37
    rw [← computable_P_iff]
    rfl
  rw [dif_pos h_ex]
  dsimp
  have h_find : Nat.find h_ex = 37 := by
    rw [Nat.find_eq_iff]
    constructor
    · rw [← computable_P_iff]
      rfl
    · intro n hn
      rw [← computable_P_iff]
      have h_all : computable_forall_lt 27 36 = true := by rfl
      rw [computable_forall_lt_iff] at h_all
      rcases n with _ | n'
      · intro h_P
        rw [computable_P_iff] at h_P
        have : 0 > 0 := h_P.1
        contradiction
      · intro h_P
        rw [computable_P_iff] at h_P
        have : n' + 1 ≤ 36 := by omega
        exact h_all (n' + 1) this (by omega) h_P.2
  rw [h_find]

def sum_indices : List ℕ → ℕ → ℕ
  | [] => 0
  | d :: l => fun i => i * d + sum_indices l (i + 1)

lemma ten_pow_mod_81 (i : ℕ) : 10 ^ i % 81 = (1 + 9 * i) % 81 := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have h1 : 10 ^ (i + 1) = 10 * 10 ^ i := by ring
    rw [h1, Nat.mul_mod, ih, ← Nat.mul_mod]
    have h2 : 10 * (1 + 9 * i) = 1 + 9 * (i + 1) + 81 * i := by ring
    rw [h2]
    have h3 (a b : ℕ) : (a + 81 * b) % 81 = a % 81 := by
      rw [Nat.add_mul_mod_self_left]
    rw [h3]

lemma ofDigits_weighted_mod_81 (L : List ℕ) (start : ℕ) :
    (ofDigits 10 L * 10^start) % 81 = (L.sum + 9 * sum_indices L start) % 81 := by
  induction L generalizing start with
  | nil =>
    simp [ofDigits, sum_indices]
  | cons d l ih =>
    have h1 : ofDigits 10 (d :: l) * 10 ^ start = d * 10 ^ start + ofDigits 10 l * 10 ^ (start + 1) := by
      dsimp [ofDigits]
      ring
    rw [h1, Nat.add_mod, Nat.mul_mod, ten_pow_mod_81, ← Nat.mul_mod, ih (start + 1)]
    rw [← Nat.add_mod]
    have h2 : d * (1 + 9 * start) + (l.sum + 9 * sum_indices l (start + 1)) =
              (d + l.sum) + 9 * (start * d + sum_indices l (start + 1)) := by ring
    rw [h2]
    rfl

lemma ofDigits_mod_81 (L : List ℕ) :
    ofDigits 10 L % 81 = (L.sum + 9 * sum_indices L 0) % 81 := by
  have := ofDigits_weighted_mod_81 L 0
  simp at this
  exact this

lemma ofDigits_mod_9 (L : List ℕ) : ofDigits 10 L % 9 = L.sum % 9 := by
  have h1 : ofDigits 10 L % 9 = (ofDigits 10 L % 81) % 9 := by
    omega
  have h2 (a : ℕ) : (a % 81) % 9 = a % 9 := by
    omega
  rw [h1, ofDigits_mod_81, h2, Nat.add_mul_mod_self_left]

lemma sum_indices_shift (L : List ℕ) (start : ℕ) :
    sum_indices L (start + 1) = sum_indices L start + L.sum := by
  induction L generalizing start with
  | nil => rfl
  | cons a l ih =>
    dsimp [sum_indices]
    rw [ih (start + 1)]
    ring

lemma sum_indices_append (L : List ℕ) (d : ℕ) (start : ℕ) :
    sum_indices (L ++ [d]) start = sum_indices L start + (start + L.length) * d := by
  induction L generalizing start with
  | nil => simp [sum_indices]
  | cons a l ih =>
    dsimp [sum_indices]
    rw [ih (start + 1)]
    ring

lemma sum_indices_reverse_add (L : List ℕ) (start : ℕ) :
    sum_indices L.reverse start + sum_indices L start + L.sum = (2 * start + L.length) * L.sum := by
  induction L using List.reverseRecOn generalizing start with
  | nil => simp [sum_indices]
  | append_singleton l d ih =>
    have h_rev : (l ++ [d]).reverse = d :: l.reverse := by simp
    rw [h_rev]
    dsimp [sum_indices]
    rw [sum_indices_shift l.reverse start]
    rw [sum_indices_append l d start]
    have h_sum_rev : l.reverse.sum = l.sum := by simp
    rw [h_sum_rev]
    have ih_start := ih start
    have h_sum : (l ++ [d]).sum = l.sum + d := by simp
    have h_len : (l ++ [d]).length = l.length + 1 := by simp
    rw [h_sum, h_len]
    have h_assoc : start * d + (sum_indices l.reverse start + l.sum) + (sum_indices l start + (start + l.length) * d) + (l.sum + d) =
                   (sum_indices l.reverse start + sum_indices l start + l.sum) + l.sum + d + (2 * start + l.length) * d := by ring
    rw [h_assoc, ih_start]
    ring

lemma sum_indices_reverse_add_zero (L : List ℕ) :
    sum_indices L.reverse 0 + sum_indices L 0 + L.sum = L.length * L.sum := by
  have := sum_indices_reverse_add L 0
  simp at this
  exact this

lemma nine_mul_sum_indices_mod_81 (L : List ℕ) (s : ℕ) (hs : L.sum = 9 * s) :
    (9 * (sum_indices L.reverse 0 + sum_indices L 0)) % 81 = 0 := by
  have h1 : 9 * (sum_indices L.reverse 0 + sum_indices L 0) + 81 * s = 81 * L.length * s := by
    calc
      9 * (sum_indices L.reverse 0 + sum_indices L 0) + 81 * s
      _ = 9 * (sum_indices L.reverse 0 + sum_indices L 0) + 9 * (9 * s) := by ring
      _ = 9 * (sum_indices L.reverse 0 + sum_indices L 0 + 9 * s) := by ring
      _ = 9 * (sum_indices L.reverse 0 + sum_indices L 0 + L.sum) := by rw [hs]
      _ = 9 * (L.length * L.sum) := by rw [sum_indices_reverse_add_zero]
      _ = 9 * (L.length * (9 * s)) := by rw [hs]
      _ = 81 * L.length * s := by ring
  have h2 : (9 * (sum_indices L.reverse 0 + sum_indices L 0) + 81 * s) % 81 = 0 := by
    rw [h1]
    have h_div : 81 ∣ 81 * L.length * s := by
      use L.length * s
      ring
    exact Nat.dvd_iff_mod_eq_zero.mp h_div
  have h3 : (9 * (sum_indices L.reverse 0 + sum_indices L 0) + 81 * s) % 81 = (9 * (sum_indices L.reverse 0 + sum_indices L 0)) % 81 := by
    rw [Nat.add_mul_mod_self_left]
  rw [h3] at h2
  exact h2

lemma two_mul_sum_mod_81 (L : List ℕ) (s : ℕ) (hs : L.sum = 9 * s)
    (hL : ofDigits 10 L % 81 = 0) (hR : ofDigits 10 L.reverse % 81 = 0) :
    (2 * L.sum) % 81 = 0 := by
  have h_add : ((ofDigits 10 L % 81) + (ofDigits 10 L.reverse % 81)) % 81 = 0 := by
    rw [hL, hR]
  rw [ofDigits_mod_81 L, ofDigits_mod_81 L.reverse] at h_add
  rw [List.sum_reverse] at h_add
  rw [← Nat.add_mod] at h_add
  have h_ring : (L.sum + 9 * sum_indices L 0) + (L.sum + 9 * sum_indices L.reverse 0) =
                2 * L.sum + 9 * (sum_indices L.reverse 0 + sum_indices L 0) := by ring
  rw [h_ring] at h_add
  have h_nine := nine_mul_sum_indices_mod_81 L s hs
  rw [Nat.add_mod, h_nine] at h_add
  simp at h_add
  exact h_add

lemma dvd_sum_of_two_mul_sum_mod_81 (L : List ℕ) (s : ℕ) (hs : L.sum = 9 * s)
    (hL : ofDigits 10 L % 81 = 0) (hR : ofDigits 10 L.reverse % 81 = 0) :
    81 ∣ L.sum := by
  have h_div : 81 ∣ 2 * L.sum := Nat.dvd_iff_mod_eq_zero.mpr (two_mul_sum_mod_81 L s hs hL hR)
  have h_cop : Nat.Coprime 81 2 := by decide
  exact h_cop.dvd_of_dvd_mul_left h_div

lemma sum_le_nine_mul_length (L : List ℕ) (h : ∀ x ∈ L, x ≤ 9) :
    L.sum ≤ 9 * L.length := by
  induction L with
  | nil => simp
  | cons a l ih =>
    rw [List.sum_cons, List.length_cons]
    have ha : a ≤ 9 := h a (by simp)
    have hl : ∀ x ∈ l, x ≤ 9 := fun x hx => h x (by simp [hx])
    have ih' := ih hl
    omega

lemma eq_nine_of_sum_eq_nine_mul_length (L : List ℕ) (h : ∀ x ∈ L, x ≤ 9) (h_sum : L.sum = 9 * L.length) :
    ∀ x ∈ L, x = 9 := by
  induction L with
  | nil =>
    intro x hx
    contradiction
  | cons a l ih =>
    intro x hx
    have ha : a ≤ 9 := h a (by simp)
    have hl : ∀ y ∈ l, y ≤ 9 := fun y hy => h y (by simp [hy])
    have ih_le := sum_le_nine_mul_length l hl
    have h_sum_cons : a + l.sum = 9 * (l.length + 1) := by
      rw [← List.sum_cons, h_sum, List.length_cons]
    have h_a_eq : a = 9 := by omega
    have h_sum_eq : l.sum = 9 * l.length := by omega
    rcases List.mem_cons.mp hx with rfl | hx_l
    · exact h_a_eq
    · exact ih hl h_sum_eq x hx_l

lemma ofDigits_nine (L : List ℕ) (h : ∀ x ∈ L, x = 9) :
    ofDigits 10 L = 10 ^ L.length - 1 := by
  induction L with
  | nil => rfl
  | cons a l ih =>
    have ha_eq : a = 9 := h a (by simp)
    have hl_eq : ∀ x ∈ l, x = 9 := fun x hx => h x (by simp [hx])
    have ih' := ih hl_eq
    rw [List.length_cons]
    dsimp [ofDigits]
    rw [ha_eq, ih']
    have h_pow : 10 ^ l.length ≥ 1 := Nat.one_le_pow l.length 10 (by decide)
    omega

lemma length_digits_le_nine (n : ℕ) (hn_pos : n > 0) (hn_lt : n < 1000000000) :
    (digits 10 n).length ≤ 9 := by
  have h_le := Nat.base_pow_length_digits_le 10 n (by decide) (by omega)
  have h_lt : 10 * n < 10 ^ 10 := by omega
  have h_pow : 10 ^ (digits 10 n).length < 10 ^ 10 := lt_of_le_of_lt h_le h_lt
  have h_len : (digits 10 n).length < 10 := Nat.pow_lt_pow_iff_right (by decide) |>.mp h_pow
  omega

lemma ofDigits_eq_zero_of_sum_eq_zero (L : List ℕ) (h : L.sum = 0) : ofDigits 10 L = 0 := by
  induction L with
  | nil => rfl
  | cons a l ih =>
    rw [List.sum_cons] at h
    have ha : a = 0 := by omega
    have hl : l.sum = 0 := by omega
    dsimp [ofDigits]
    rw [ha, ih hl]
    rfl

theorem eighty_one_multiple (n : ℕ) (hn_pos : n > 0) (hn_lt : n < 1000000000) (h1 : n % 81 = 0) (h2 : reverse_nat n % 81 = 0) : n = 999999999 := by
  let L := digits 10 n
  have h_of_digits : ofDigits 10 L = n := ofDigits_digits 10 n
  have hL : ofDigits 10 L % 81 = 0 := by rw [h_of_digits, h1]
  have hR : ofDigits 10 L.reverse % 81 = 0 := by
    have h_rev : reverse_nat n = ofDigits 10 L.reverse := rfl
    rw [← h_rev, h2]
  have h_mod_9 : ofDigits 10 L % 9 = 0 := by
    rw [h_of_digits]
    omega
  have h_sum_mod_9 : L.sum % 9 = 0 := by
    rw [← ofDigits_mod_9, h_mod_9]
  have h_dvd_9 : 9 ∣ L.sum := Nat.dvd_of_mod_eq_zero h_sum_mod_9
  rcases h_dvd_9 with ⟨s, hs⟩
  have h_dvd_81 : 81 ∣ L.sum := dvd_sum_of_two_mul_sum_mod_81 L s hs hL hR
  have h_sum_nz : L.sum ≠ 0 := by
    intro h_zero
    have h_n_zero : ofDigits 10 L = 0 := ofDigits_eq_zero_of_sum_eq_zero L h_zero
    rw [h_of_digits] at h_n_zero
    omega
  have h_sum_ge : L.sum ≥ 81 := Nat.le_of_dvd (by omega) h_dvd_81
  have h_digits_lt : ∀ x ∈ L, x ≤ 9 := by
    intro x hx
    have := digits_lt_base' hx
    omega
  have h_sum_le : L.sum ≤ 9 * L.length := sum_le_nine_mul_length L h_digits_lt
  have h_length_le : L.length ≤ 9 := length_digits_le_nine n hn_pos hn_lt
  have h_sum_81 : L.sum = 81 := by omega
  have h_length_9 : L.length = 9 := by omega
  have h_all_nine : ∀ x ∈ L, x = 9 := eq_nine_of_sum_eq_nine_mul_length L h_digits_lt (by omega)
  have h_n_eq : ofDigits 10 L = 10 ^ 9 - 1 := by
    rw [ofDigits_nine L h_all_nine, h_length_9]
  rw [h_of_digits] at h_n_eq
  have h_calc : 10 ^ 9 - 1 = 999999999 := rfl
  rw [h_calc] at h_n_eq
  exact h_n_eq

theorem a_eighty_one : a 81 = 999999999 := by
  unfold a
  have h0 : ¬ 81 = 0 := by decide
  rw [if_neg h0]
  have h_ex : ∃ k, k > 0 ∧ 81 ∣ reverse_nat (k * 81) := by
    use 12345679
    rw [← computable_P_iff]
    rfl
  rw [dif_pos h_ex]
  dsimp
  have h_find : Nat.find h_ex * 81 = 999999999 := by
    let n := Nat.find h_ex * 81
    have hn_pos : n > 0 := by
      have h_prop := Nat.find_spec h_ex
      have h_k_pos : Nat.find h_ex > 0 := h_prop.1
      exact Nat.mul_pos h_k_pos (by decide)
    have hn_lt : n < 1000000000 := by
      have h_le : Nat.find h_ex ≤ 12345679 := Nat.find_min' h_ex (by rw [← computable_P_iff]; rfl)
      have : n ≤ 12345679 * 81 := Nat.mul_le_mul_right 81 h_le
      omega
    have h1 : n % 81 = 0 := by
      omega
    have h2 : reverse_nat n % 81 = 0 := by
      have h_prop := Nat.find_spec h_ex
      exact Nat.mod_eq_zero_of_dvd h_prop.2
    have hn_eq := eighty_one_multiple n hn_pos hn_lt h1 h2
    exact hn_eq
  exact h_find

def sum_powers : ℕ → ℕ
  | 0 => 0
  | m + 1 => 1 + 10 ^ 11 * sum_powers m

lemma sum_powers_add (a b : ℕ) : sum_powers (a + b) = sum_powers b + 10^(11 * b) * sum_powers a := by
  induction b with
  | zero =>
    have h_0 : sum_powers 0 = 0 := rfl
    rw [h_0, Nat.add_zero]
    simp
  | succ b ih =>
    dsimp [sum_powers]
    rw [ih]
    have h1 : 11 * (b + 1) = 11 * b + 11 := by ring
    rw [h1]
    have h2 : 10 ^ (11 * b + 11) = 10 ^ (11 * b) * 10 ^ 11 := by ring
    rw [h2]
    ring

lemma sum_powers_mul_three (m : ℕ) :
    sum_powers (3 * m) = sum_powers m * (1 + 10^(11 * m) + 10^(22 * m)) := by
  have h_add : 3 * m = m + (m + m) := by ring
  rw [h_add, sum_powers_add]
  rw [sum_powers_add m m]
  have h_pow : 11 * (m + m) = 11 * m + 11 * m := by ring
  rw [h_pow]
  have h_pow2 : 10 ^ (11 * m + 11 * m) = 10 ^ (11 * m) * 10 ^ (11 * m) := by ring
  rw [h_pow2]
  have h_pow22 : 22 * m = 11 * m + 11 * m := by ring
  rw [h_pow22]
  have h_pow22' : 10 ^ (11 * m + 11 * m) = 10 ^ (11 * m) * 10 ^ (11 * m) := by ring
  rw [h_pow22']
  ring

lemma ten_pow_mod_3 (k : ℕ) : 10 ^ k % 3 = 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h1 : 10 ^ (k + 1) = 10 * 10 ^ k := by ring
    rw [h1, Nat.mul_mod, ih]

lemma three_dvd_geom_sum (m : ℕ) : 3 ∣ 1 + 10^(11 * m) + 10^(22 * m) := by
  have h_11 := ten_pow_mod_3 (11 * m)
  have h_22 := ten_pow_mod_3 (22 * m)
  have h_mod : (1 + 10^(11 * m) + 10^(22 * m)) % 3 = 0 := by
    omega
  exact Nat.dvd_iff_mod_eq_zero.mpr h_mod

lemma power_of_three_dvd_sum_powers (k : ℕ) : 3 ^ k ∣ sum_powers (3 ^ k) := by
  induction k with
  | zero =>
    simp [sum_powers]
  | succ k ih =>
    have h_pow : 3 ^ (k + 1) = 3 * 3 ^ k := by ring
    rw [h_pow, sum_powers_mul_three]
    have h_comm : 3 * 3 ^ k = 3 ^ k * 3 := by ring
    rw [h_comm]
    exact mul_dvd_mul ih (three_dvd_geom_sum (3 ^ k))


lemma sum_powers_pos (m : ℕ) (h : m > 0) : sum_powers m > 0 := by
  rcases m with _ | k
  · contradiction
  · dsimp [sum_powers]
    omega
lemma flatten_replicate_comm (m : ℕ) (D : List ℕ) :
    List.flatten (List.replicate m D) ++ D = D ++ List.flatten (List.replicate m D) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.replicate_succ, List.flatten_cons, List.append_assoc, ih]

lemma replicate_flatten_reverse (m : ℕ) (D : List ℕ) (hD : D.reverse = D) :
    (List.flatten (List.replicate m D)).reverse = List.flatten (List.replicate m D) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.replicate_succ, List.flatten_cons, List.reverse_append, ih, hD]
    rw [flatten_replicate_comm]

lemma mem_flatten_replicate {α : Type*} (m : ℕ) (D : List α) (l : α)
    (hl : l ∈ List.flatten (List.replicate m D)) : l ∈ D := by
  induction m with
  | zero =>
    simp [List.replicate, List.flatten] at hl
  | succ m ih =>
    rw [List.replicate_succ, List.flatten_cons, List.mem_append] at hl
    rcases hl with h | h
    · exact h
    · exact ih h

lemma getLast_flatten_replicate {α : Type*} (m : ℕ) (D : List α) (hD : D ≠ []) :
    ∀ (h_ne : List.flatten (List.replicate m D) ≠ []),
    (List.flatten (List.replicate m D)).getLast h_ne = D.getLast hD := by
  induction m with
  | zero =>
    intro h_ne
    contradiction
  | succ m ih =>
    intro h_ne
    have h_flat : (List.flatten (List.replicate (m + 1) D)) = List.flatten (List.replicate m D) ++ D := by
      rw [List.replicate_succ', List.flatten_append, List.flatten_singleton]
    have h_ne' : List.flatten (List.replicate m D) ++ D ≠ [] := by
      rw [← h_flat]
      exact h_ne
    have h_eq : (List.flatten (List.replicate (m + 1) D)).getLast h_ne =
                (List.flatten (List.replicate m D) ++ D).getLast h_ne' := by
      congr 1
    rw [h_eq, List.getLast_append_of_right_ne_nil _ _ hD]

lemma list_ofDigits_rep (m : ℕ) :
    ofDigits 10 (List.flatten (List.replicate m (digits 10 68899199886))) = 68899199886 * sum_powers m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.replicate_succ, List.flatten_cons, ofDigits_append]
    have h_len : (digits 10 68899199886).length = 11 := by
      rw [← digits10_fuel_eq_digits (68899199886 + 1) 68899199886 (by omega)]
      rfl
    rw [h_len, ofDigits_digits 10 68899199886]
    rw [ih]
    dsimp [sum_powers]
    ring

lemma geom_sum (m : ℕ) : 99999999999 * sum_powers m = 10^(11 * m) - 1 := by
  induction m with
  | zero => rfl
  | succ m ih =>
    dsimp [sum_powers]
    rw [mul_add]
    have h_assoc : 99999999999 * (100000000000 * sum_powers m) = 100000000000 * (99999999999 * sum_powers m) := by ring
    rw [h_assoc, ih]
    have h1 : 11 * (m + 1) = 11 * m + 11 := by ring
    rw [h1]
    have h2 : 10 ^ (11 * m + 11) = 10 ^ (11 * m) * 10 ^ 11 := by ring
    rw [h2]
    have h_pow : 10 ^ (11 * m) ≥ 1 := Nat.one_le_pow _ 10 (by decide)
    have h_pow11 : 10 ^ 11 ≥ 1 := by decide
    omega

theorem oeis_62567_conjecture_0 (n : ℕ) :
  2 ≤ n → (a (3^n) = 10 ^ (3 ^ (n - 2)) - 1 ↔ n = 2 ∨ n = 3 ∨ n = 4) := by
  intro hn
  rcases n with _ | _ | _ | _ | _ | n'
  · contradiction
  · contradiction
  · -- n = 2
    simp
    exact a_nine
  · -- n = 3
    simp
    exact a_twenty_seven
  · -- n = 4
    simp
    exact a_eighty_one
  · -- n >= 5
          simp
          intro h_eq
          have h_eq_simp : a (3 ^ (n' + 5)) = 10 ^ (3 ^ (n' + 3)) - 1 := h_eq
          let m := 3 ^ n'
          let D := digits 10 68899199886
          let L := List.flatten (List.replicate m D)
          let W := ofDigits 10 L
          have hm : m > 0 := Nat.pow_pos (by decide)
          have hW_eq : W = 68899199886 * sum_powers m := list_ofDigits_rep m
          have hW_pos : W > 0 := by
            rw [hW_eq]
            exact Nat.mul_pos (by decide) (sum_powers_pos m hm)
          have h_div_W : 3 ^ (n' + 5) ∣ W := by
            rw [hW_eq]
            have h_3_5 : 3 ^ (n' + 5) = 243 * 3 ^ n' := by ring
            rw [h_3_5]
            have h_688 : 68899199886 = 243 * 283535802 := by rfl
            rw [h_688]
            have h_sum_pow := power_of_three_dvd_sum_powers n'
            rcases h_sum_pow with ⟨q, hq⟩
            use 283535802 * q
            rw [hq]
            ring
          have h_D_eq : D = digits10_fuel (68899199886 + 1) 68899199886 :=
            (digits10_fuel_eq_digits (68899199886 + 1) 68899199886 (by omega)).symm
          have h_D_rev : D.reverse = D := by
            rw [h_D_eq]
            rfl
          have h_L_rev : L.reverse = L := replicate_flatten_reverse m D h_D_rev
          have h_D_ne : D ≠ [] := by
            rw [h_D_eq]
            decide
          have h_L_ne : L ≠ [] := by
            intro h_nil
            have h_flatten : List.flatten (List.replicate m D) = [] := h_nil
            rcases m with _ | m'
            · contradiction
            · rw [List.replicate_succ, List.flatten_cons] at h_flatten
              exact h_D_ne (List.append_eq_nil_iff.mp h_flatten).1
          have h_digits : digits 10 W = L := by
            apply digits_ofDigits 10 (by decide) L
            · intro l hl
              have hl_mem := mem_flatten_replicate m D l hl
              exact digits_lt_base' hl_mem
            · intro h_ne'
              rw [getLast_flatten_replicate m D h_D_ne h_ne']
              have h_D_eq_concrete : D = [6, 8, 8, 9, 9, 1, 9, 9, 8, 8, 6] := by
                rw [h_D_eq]
                rfl
              revert h_D_ne
              rw [h_D_eq_concrete]
              decide
          have h_rev_W : reverse_nat W = W := by
            unfold reverse_nat
            rw [h_digits, h_L_rev]
          have h_sum_powers_lt : sum_powers m < 10 ^ (11 * m) := by
            have h_geom := geom_sum m
            have h_pow : 10 ^ (11 * m) ≥ 1 := Nat.one_le_pow _ 10 (by decide)
            omega
          have h_W_lt : W < 10 ^ (11 * m + 11) := by
            rw [hW_eq]
            calc
              68899199886 * sum_powers m < 100000000000 * sum_powers m := by
                apply Nat.mul_lt_mul_of_pos_right _ (sum_powers_pos m hm)
                decide
              _ < 10^11 * 10^(11 * m) := by
                have : 100000000000 = 10^11 := rfl
                rw [this]
                apply Nat.mul_lt_mul_of_pos_left h_sum_powers_lt (by decide)
              _ = 10 ^ (11 * m + 11) := by ring
          have h_lt : 11 * m + 11 < 3 ^ (n' + 3) := by
            have h_3_3 : 3 ^ (n' + 3) = 27 * m := by ring
            rw [h_3_3]
            have h_m_pos : m ≥ 1 := Nat.one_le_pow n' 3 (by decide)
            omega
          have h_final_lt : W < 10 ^ (3 ^ (n' + 3)) - 1 := by
            have h_pow_lt : 10 ^ (11 * m + 11) < 10 ^ (3 ^ (n' + 3)) := Nat.pow_lt_pow_right (by decide) h_lt
            omega
          have h_ex_W : ∃ k, k > 0 ∧ 3 ^ (n' + 5) ∣ reverse_nat (k * 3 ^ (n' + 5)) := by
            rcases h_div_W with ⟨k_wit, hk_wit⟩
            use k_wit
            constructor
            · rcases eq_or_lt_of_le (Nat.zero_le k_wit) with rfl | hk_pos
              · exfalso
                rw [mul_zero] at hk_wit
                omega
              · exact hk_pos
            · rw [mul_comm, ← hk_wit, h_rev_W]
              exact ⟨k_wit, hk_wit⟩
          have h_a_le_W : a (3 ^ (n' + 5)) ≤ W := by
            unfold a
            have h_not_zero : ¬ 3 ^ (n' + 5) = 0 := by
              intro h_zero
              have : 3 ^ (n' + 5) > 0 := Nat.pow_pos (by decide)
              omega
            rw [if_neg h_not_zero]
            rw [dif_pos h_ex_W]
            dsimp
            have h_min : Nat.find h_ex_W * 3 ^ (n' + 5) ≤ W := by
              rcases h_div_W with ⟨k_wit, hk_wit⟩
              have h_spec : (fun k => k > 0 ∧ 3 ^ (n' + 5) ∣ reverse_nat (k * 3 ^ (n' + 5))) k_wit := by
                constructor
                · rcases eq_or_lt_of_le (Nat.zero_le k_wit) with rfl | hk_pos
                  · exfalso
                    rw [mul_zero] at hk_wit
                    omega
                  · exact hk_pos
                · rw [mul_comm, ← hk_wit, h_rev_W]
                  exact ⟨k_wit, hk_wit⟩
              have h_find_le := Nat.find_min' h_ex_W h_spec
              rw [hk_wit, mul_comm (3 ^ (n' + 5))]
              exact Nat.mul_le_mul_right (3 ^ (n' + 5)) h_find_le
            exact h_min
          clear h_eq
          omega
