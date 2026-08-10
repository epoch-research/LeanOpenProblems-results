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

lemma a_def_of_ne_zero_of_exists {n : ℕ} (hn : n ≠ 0) (h_ex : ∃ k, k > 0 ∧ n ∣ reverse_nat (k * n)) :
    a n = Nat.find h_ex * n := by
  unfold a
  rw [if_neg hn]
  rw [dif_pos h_ex]

lemma find_eq_of_spec_and_min {P : ℕ → Prop} [DecidablePred P] (h_ex : ∃ k, P k) (K : ℕ)
    (h_spec : P K) (h_min : ∀ m < K, ¬ P m) : Nat.find h_ex = K := by
  have h_le : Nat.find h_ex ≤ K := Nat.find_le h_spec
  have h_ge : K ≤ Nat.find h_ex := by
    by_contra h_contr
    push_neg at h_contr
    have h_not := h_min (Nat.find h_ex) h_contr
    have h_yes := Nat.find_spec h_ex
    contradiction
  omega

theorem a_9 : a 9 = 9 := by
  have h_ne : 9 ≠ 0 := by decide
  have h_spec : 1 > 0 ∧ 9 ∣ reverse_nat (1 * 9) := by
    constructor
    · decide
    · simp [reverse_nat]
  have h_ex : ∃ k, k > 0 ∧ 9 ∣ reverse_nat (k * 9) := ⟨1, h_spec⟩
  have h_min : ∀ m < 1, ¬ (m > 0 ∧ 9 ∣ reverse_nat (m * 9)) := by
    intro m hm
    interval_cases m
    · rintro ⟨h_pos, _⟩
      contradiction
  have h_find : Nat.find h_ex = 1 := find_eq_of_spec_and_min h_ex 1 h_spec h_min
  rw [a_def_of_ne_zero_of_exists h_ne h_ex]
  rw [h_find]

theorem a_27 : a 27 = 999 := by
  have h_ne : 27 ≠ 0 := by decide
  have h_spec : 37 > 0 ∧ 27 ∣ reverse_nat (37 * 27) := by
    constructor
    · decide
    · simp [reverse_nat]
      decide
  have h_ex : ∃ k, k > 0 ∧ 27 ∣ reverse_nat (k * 27) := ⟨37, h_spec⟩
  have h_min : ∀ m < 37, ¬ (m > 0 ∧ 27 ∣ reverse_nat (m * 27)) := by
    intro m hm
    interval_cases m
    · rintro ⟨h_pos, _⟩
      contradiction
    all_goals
      rintro ⟨_, h_dvd⟩
      simp [reverse_nat] at h_dvd
      revert h_dvd
      decide
  have h_find : Nat.find h_ex = 37 := find_eq_of_spec_and_min h_ex 37 h_spec h_min
  rw [a_def_of_ne_zero_of_exists h_ne h_ex]
  rw [h_find]


def weighted_sum : List ℕ → ℕ → ℕ
  | [], _ => 0
  | a :: l, i => i * a + weighted_sum l (i + 1)

lemma ofDigits_mod_9 (L : List ℕ) : ofDigits 10 L ≡ L.sum [MOD 9] := by
  induction L with
  | nil => rfl
  | cons a l ih =>
    change (a + 10 * ofDigits 10 l) ≡ a + l.sum [MOD 9]
    have h1 : 10 * ofDigits 10 l ≡ 1 * ofDigits 10 l [MOD 9] := by
      apply Nat.ModEq.mul_right
      decide
    have h2 : a + 10 * ofDigits 10 l ≡ a + 1 * ofDigits 10 l [MOD 9] := by
      apply Nat.ModEq.add_left
      exact h1
    rw [Nat.one_mul] at h2
    apply Nat.ModEq.trans h2
    apply Nat.ModEq.add_left
    exact ih

lemma mul_9_modEq_mul_9 {x y : ℕ} (h : x ≡ y [MOD 9]) : 9 * x ≡ 9 * y [MOD 81] := by
  unfold ModEq at *
  omega

lemma ofDigits_mod_81_helper (L : List ℕ) (start : ℕ) :
    ofDigits 10 L + 9 * (start * L.sum) ≡ L.sum + 9 * weighted_sum L start [MOD 81] := by
  induction L generalizing start with
  | nil => rfl
  | cons a l ih =>
    change a + 10 * ofDigits 10 l + 9 * (start * (a + l.sum)) ≡ (a + l.sum) + 9 * (start * a + weighted_sum l (start + 1)) [MOD 81]
    have h_lhs : a + 10 * ofDigits 10 l + 9 * (start * (a + l.sum)) =
                 (a + 9 * start * a) + (10 * ofDigits 10 l + 9 * start * l.sum) := by ring
    have h_rhs : (a + l.sum) + 9 * (start * a + weighted_sum l (start + 1)) =
                 (a + 9 * start * a) + (l.sum + 9 * weighted_sum l (start + 1)) := by ring
    rw [h_lhs, h_rhs]
    apply Nat.ModEq.add_left
    have h_ten : 10 * ofDigits 10 l = ofDigits 10 l + 9 * ofDigits 10 l := by omega
    have h_lhs2 : 10 * ofDigits 10 l + 9 * start * l.sum = ofDigits 10 l + 9 * ofDigits 10 l + 9 * start * l.sum := by rw [h_ten]
    rw [h_lhs2]
    have h_mod9 : ofDigits 10 l ≡ l.sum [MOD 9] := ofDigits_mod_9 l
    have h_mod81 : 9 * ofDigits 10 l ≡ 9 * l.sum [MOD 81] := mul_9_modEq_mul_9 h_mod9
    have h_step1 : ofDigits 10 l + 9 * ofDigits 10 l + 9 * start * l.sum ≡
                   ofDigits 10 l + 9 * l.sum + 9 * start * l.sum [MOD 81] := by
      have : ofDigits 10 l + 9 * ofDigits 10 l + 9 * start * l.sum =
             (ofDigits 10 l + 9 * start * l.sum) + 9 * ofDigits 10 l := by omega
      rw [this]
      have : ofDigits 10 l + 9 * l.sum + 9 * start * l.sum =
             (ofDigits 10 l + 9 * start * l.sum) + 9 * l.sum := by omega
      rw [this]
      apply Nat.ModEq.add_left
      exact h_mod81
    apply Nat.ModEq.trans h_step1
    have h_assoc : ofDigits 10 l + 9 * l.sum + 9 * start * l.sum = ofDigits 10 l + 9 * ((start + 1) * l.sum) := by ring
    rw [h_assoc]
    exact ih (start + 1)

lemma weighted_sum_append (l1 l2 : List ℕ) (start : ℕ) :
    weighted_sum (l1 ++ l2) start = weighted_sum l1 start + weighted_sum l2 (start + l1.length) := by
  induction l1 generalizing start with
  | nil => unfold weighted_sum; simp
  | cons a l ih =>
    change start * a + weighted_sum (l ++ l2) (start + 1) =
           (start * a + weighted_sum l (start + 1)) + weighted_sum l2 (start + (l.length + 1))
    rw [ih (start + 1)]
    ring

lemma weighted_sum_shift (L : List ℕ) (k : ℕ) : weighted_sum L (k + 1) = weighted_sum L k + L.sum := by
  induction L generalizing k with
  | nil => unfold weighted_sum; simp
  | cons a l ih =>
    change (k + 1) * a + weighted_sum l (k + 1 + 1) = (k * a + weighted_sum l (k + 1)) + (a + l.sum)
    rw [ih (k + 1)]
    ring

lemma weighted_sum_add (L : List ℕ) (k s : ℕ) : weighted_sum L (k + s) = weighted_sum L k + s * L.sum := by
  induction s with
  | zero => ring
  | succ s ih =>
    have h1 : k + (s + 1) = (k + s) + 1 := by ring
    rw [h1, weighted_sum_shift, ih]
    ring

lemma weighted_sum_eq_zero_add (L : List ℕ) (k : ℕ) : weighted_sum L k = weighted_sum L 0 + k * L.sum := by
  have h : k = 0 + k := by ring
  nth_rw 1 [h]
  rw [weighted_sum_add]

lemma weighted_sum_singleton (a : ℕ) (k : ℕ) : weighted_sum [a] k = k * a := by
  unfold weighted_sum
  rfl

lemma weighted_sum_cons (a : ℕ) (l : List ℕ) (start : ℕ) :
    weighted_sum (a :: l) start = start * a + weighted_sum l (start + 1) := rfl

lemma weighted_sum_reverse_add (L : List ℕ) :
    weighted_sum L.reverse 0 + weighted_sum L 0 = (L.length - 1) * L.sum := by
  induction L with
  | nil =>
    unfold weighted_sum; simp
  | cons a l ih =>
    rw [List.reverse_cons, weighted_sum_append, weighted_sum_singleton, List.length_reverse]
    rw [weighted_sum_cons a l 0]
    rw [weighted_sum_shift]
    cases l with
    | nil =>
      unfold weighted_sum; simp
    | cons b l' =>
      simp only [List.length_cons, List.sum_cons, Nat.zero_add, Nat.zero_mul]
      have h_lhs : weighted_sum (b :: l').reverse 0 + (l'.length + 1) * a + (weighted_sum (b :: l') 0 + (b + l'.sum)) =
                   (weighted_sum (b :: l').reverse 0 + weighted_sum (b :: l') 0) + (l'.length + 1) * a + (b + l'.sum) := by ring
      rw [h_lhs]
      have ih_simp : weighted_sum (b :: l').reverse 0 + weighted_sum (b :: l') 0 = l'.length * (b + l'.sum) := by
        have := ih
        simp only [List.length_cons, List.sum_cons] at this
        have h_sub : l'.length + 1 - 1 = l'.length := by omega
        rw [h_sub] at this
        exact this
      rw [ih_simp]
      have h_sub2 : l'.length + 1 + 1 - 1 = l'.length + 1 := by omega
      rw [h_sub2]
      ring

lemma ofDigits_reverse_add_ofDigits (L : List ℕ) :
    ofDigits 10 L.reverse + ofDigits 10 L ≡ (2 + 9 * (L.length - 1)) * L.sum [MOD 81] := by
  have h1 : ofDigits 10 L ≡ L.sum + 9 * weighted_sum L 0 [MOD 81] := by
    have h := ofDigits_mod_81_helper L 0
    simp only [Nat.mul_zero, Nat.zero_mul, Nat.add_zero] at h
    exact h
  have h2 : ofDigits 10 L.reverse ≡ L.sum + 9 * weighted_sum L.reverse 0 [MOD 81] := by
    have h := ofDigits_mod_81_helper L.reverse 0
    simp only [Nat.mul_zero, Nat.zero_mul, Nat.add_zero] at h
    rw [List.sum_reverse] at h
    exact h
  have h3 : ofDigits 10 L.reverse + ofDigits 10 L ≡
            (L.sum + 9 * weighted_sum L.reverse 0) + (L.sum + 9 * weighted_sum L 0) [MOD 81] := by
    apply Nat.ModEq.add h2 h1
  apply Nat.ModEq.trans h3
  have h4 : (L.sum + 9 * weighted_sum L.reverse 0) + (L.sum + 9 * weighted_sum L 0) =
            2 * L.sum + 9 * (weighted_sum L.reverse 0 + weighted_sum L 0) := by ring
  rw [h4, weighted_sum_reverse_add]
  have h5 : 2 * L.sum + 9 * ((L.length - 1) * L.sum) = (2 + 9 * (L.length - 1)) * L.sum := by ring
  rw [h5]

lemma mod_81_cancel {C S : ℕ} (D : ℕ) (h_inv : C * D ≡ 1 [MOD 81]) (h_mod : C * S ≡ 0 [MOD 81]) : 81 ∣ S := by
  have h1 : (C * S * D) % 81 = 0 := by
    rw [Nat.mul_mod, h_mod]
    simp
  have h2 : C * S * D = (C * D) * S := by ring
  rw [h2] at h1
  have h3 : (C * D) * S ≡ 1 * S [MOD 81] := by
    apply Nat.ModEq.mul_right
    exact h_inv
  rw [Nat.one_mul] at h3
  unfold ModEq at h3
  rw [h3] at h1
  exact Nat.dvd_of_mod_eq_zero h1

lemma sum_digits_le_9_mul_length (L : List ℕ) (h : ∀ x ∈ L, x ≤ 9) : L.sum ≤ 9 * L.length := by
  induction L with
  | nil => simp
  | cons a l ih =>
    simp only [List.sum_cons, List.length_cons]
    have ha : a ≤ 9 := h a (by simp)
    have hl : ∀ x ∈ l, x ≤ 9 := fun x hx => h x (by simp [hx])
    have ih' := ih hl
    omega

lemma le_sum_of_mem {x : ℕ} {L : List ℕ} (h : x ∈ L) : x ≤ L.sum := by
  induction L with
  | nil => contradiction
  | cons a l ih =>
    simp only [List.sum_cons]
    cases h with
    | head => omega
    | tail _ h_mem =>
      have := ih h_mem
      omega

lemma digits_all_nine_of_sum_eq_9_mul_length (L : List ℕ) (h : ∀ x ∈ L, x ≤ 9) (h_sum : L.sum = 9 * L.length) :
    L = List.replicate L.length 9 := by
  induction L with
  | nil => rfl
  | cons a l ih =>
    simp only [List.sum_cons, List.length_cons] at h_sum
    have ha : a ≤ 9 := h a (by simp)
    have hl : ∀ x ∈ l, x ≤ 9 := fun x hx => h x (by simp [hx])
    have h_le := sum_digits_le_9_mul_length l hl
    have ha9 : a = 9 := by omega
    have h_sum9 : l.sum = 9 * l.length := by omega
    subst ha9
    rw [ih hl h_sum9]
    simp only [List.length_cons, List.length_replicate]
    rfl

theorem a_81_eq : a 81 = 999999999 := by
  have h_ne : 81 ≠ 0 := by decide
  have h_spec : 12345679 > 0 ∧ 81 ∣ reverse_nat (12345679 * 81) := by
    constructor
    · decide
    · simp [reverse_nat]
      decide
  have h_ex : ∃ k, k > 0 ∧ 81 ∣ reverse_nat (k * 81) := ⟨12345679, h_spec⟩
  have h_min : ∀ m < 12345679, ¬ (m > 0 ∧ 81 ∣ reverse_nat (m * 81)) := by
    intro m hm ⟨h_pos, h_dvd⟩
    let N := m * 81
    have h_N_pos : N ≠ 0 := by
      apply Nat.ne_of_gt
      exact Nat.mul_pos h_pos (by decide)
    let L := digits 10 N
    have h_L_digits : ∀ x ∈ L, x ≤ 9 := by
      intro x hx
      have := Nat.digits_lt_base (by decide : 1 < 10) hx
      omega
    have h_dvd_N : 81 ∣ ofDigits 10 L := by
      rw [ofDigits_digits]
      exact Nat.dvd_mul_left 81 m
    have h_dvd_rev : 81 ∣ ofDigits 10 L.reverse := by
      rw [← reverse_nat]
      exact h_dvd
    have h_add : 81 ∣ ofDigits 10 L.reverse + ofDigits 10 L := Nat.dvd_add h_dvd_rev h_dvd_N
    have h_mod81 := ofDigits_reverse_add_ofDigits L
    unfold ModEq at h_mod81
    have h_mod_zero : (ofDigits 10 L.reverse + ofDigits 10 L) % 81 = 0 := Nat.mod_eq_zero_of_dvd h_add
    rw [h_mod_zero] at h_mod81
    have h_mod_zero2 : (2 + 9 * (L.length - 1)) * L.sum % 81 = 0 := h_mod81.symm
    have h_dvd_mul : 81 ∣ (2 + 9 * (L.length - 1)) * L.sum := Nat.dvd_of_mod_eq_zero h_mod_zero2
    have h_L_ne : L ≠ [] := digits_ne_nil_iff_ne_zero.mpr h_N_pos
    have h_L_len_pos : L.length > 0 := List.length_pos_of_ne_nil h_L_ne
    have h_lt_10_9 : N < 10^9 := by
      have h_m_lt : m ≤ 12345678 := by omega
      have h_N_lt : m * 81 ≤ 12345678 * 81 := Nat.mul_le_mul_right 81 h_m_lt
      omega
    have h_L_len_le_9 : L.length ≤ 9 := by
      by_contra h_contr
      push_neg at h_contr
      have h_pow_le : 10^10 ≤ 10^L.length := Nat.pow_le_pow_right (by decide) h_contr
      have h_le_N : 10^L.length ≤ 10 * N := base_pow_length_digits_le 10 N (by decide) h_N_pos
      have h_le_N3 : 10^9 ≤ N := by omega
      omega
    have h_len_cases : L.length = 1 ∨ L.length = 2 ∨ L.length = 3 ∨ L.length = 4 ∨
                       L.length = 5 ∨ L.length = 6 ∨ L.length = 7 ∨ L.length = 8 ∨ L.length = 9 := by omega
    rcases h_len_cases with h_len | h_len | h_len | h_len | h_len | h_len | h_len | h_len | h_len9
    · have h_inv : 2 * 41 ≡ 1 [MOD 81] := by decide
      have h_dvd_S : 81 ∣ L.sum := by
        have h_mod_zero3 : (2 + 9 * (L.length - 1)) * L.sum % 81 = 0 := h_mod_zero2
        rw [h_len] at h_mod_zero3
        have h_term : 2 + 9 * (1 - 1) = 2 := by decide
        rw [h_term] at h_mod_zero3
        exact mod_81_cancel 41 h_inv h_mod_zero3
      have h_le_9 : L.sum ≤ 9 := by
        have := sum_digits_le_9_mul_length L h_L_digits
        omega
      have h_S_pos : L.sum > 0 := by
        by_contra h_sz
        have : L.sum = 0 := by omega
        have h_nil : L ≠ [] := digits_ne_nil_iff_ne_zero.mpr h_N_pos
        have h_last : L.getLast h_nil ≠ 0 := getLast_digit_ne_zero 10 h_N_pos
        have h_mem := List.getLast_mem h_nil
        have h_le := le_sum_of_mem h_mem
        omega
      have : L.sum ≥ 81 := Nat.le_of_dvd h_S_pos h_dvd_S
      omega
    · have h_inv : 11 * 59 ≡ 1 [MOD 81] := by decide
      have h_dvd_S : 81 ∣ L.sum := by
        have h_mod_zero3 : (2 + 9 * (L.length - 1)) * L.sum % 81 = 0 := h_mod_zero2
        rw [h_len] at h_mod_zero3
        have h_term : 2 + 9 * (2 - 1) = 11 := by decide
        rw [h_term] at h_mod_zero3
        exact mod_81_cancel 59 h_inv h_mod_zero3
      have h_le_18 : L.sum ≤ 18 := by
        have := sum_digits_le_9_mul_length L h_L_digits
        omega
      have h_S_pos : L.sum > 0 := by
        by_contra h_sz
        have : L.sum = 0 := by omega
        have h_nil : L ≠ [] := digits_ne_nil_iff_ne_zero.mpr h_N_pos
        have h_last : L.getLast h_nil ≠ 0 := getLast_digit_ne_zero 10 h_N_pos
        have h_mem := List.getLast_mem h_nil
        have h_le := le_sum_of_mem h_mem
        omega
      have : L.sum ≥ 81 := Nat.le_of_dvd h_S_pos h_dvd_S
      omega
    · have h_inv : 20 * 77 ≡ 1 [MOD 81] := by decide
      have h_dvd_S : 81 ∣ L.sum := by
        have h_mod_zero3 : (2 + 9 * (L.length - 1)) * L.sum % 81 = 0 := h_mod_zero2
        rw [h_len] at h_mod_zero3
        have h_term : 2 + 9 * (3 - 1) = 20 := by decide
        rw [h_term] at h_mod_zero3
        exact mod_81_cancel 77 h_inv h_mod_zero3
      have h_le_27 : L.sum ≤ 27 := by
        have := sum_digits_le_9_mul_length L h_L_digits
        omega
      have h_S_pos : L.sum > 0 := by
        by_contra h_sz
        have : L.sum = 0 := by omega
        have h_nil : L ≠ [] := digits_ne_nil_iff_ne_zero.mpr h_N_pos
        have h_last : L.getLast h_nil ≠ 0 := getLast_digit_ne_zero 10 h_N_pos
        have h_mem := List.getLast_mem h_nil
        have h_le := le_sum_of_mem h_mem
        omega
      have : L.sum ≥ 81 := Nat.le_of_dvd h_S_pos h_dvd_S
      omega
    · have h_inv : 29 * 14 ≡ 1 [MOD 81] := by decide
      have h_dvd_S : 81 ∣ L.sum := by
        have h_mod_zero3 : (2 + 9 * (L.length - 1)) * L.sum % 81 = 0 := h_mod_zero2
        rw [h_len] at h_mod_zero3
        have h_term : 2 + 9 * (4 - 1) = 29 := by decide
        rw [h_term] at h_mod_zero3
        exact mod_81_cancel 14 h_inv h_mod_zero3
      have h_le_36 : L.sum ≤ 36 := by
        have := sum_digits_le_9_mul_length L h_L_digits
        omega
      have h_S_pos : L.sum > 0 := by
        by_contra h_sz
        have : L.sum = 0 := by omega
        have h_nil : L ≠ [] := digits_ne_nil_iff_ne_zero.mpr h_N_pos
        have h_last : L.getLast h_nil ≠ 0 := getLast_digit_ne_zero 10 h_N_pos
        have h_mem := List.getLast_mem h_nil
        have h_le := le_sum_of_mem h_mem
        omega
      have : L.sum ≥ 81 := Nat.le_of_dvd h_S_pos h_dvd_S
      omega
    · have h_inv : 38 * 32 ≡ 1 [MOD 81] := by decide
      have h_dvd_S : 81 ∣ L.sum := by
        have h_mod_zero3 : (2 + 9 * (L.length - 1)) * L.sum % 81 = 0 := h_mod_zero2
        rw [h_len] at h_mod_zero3
        have h_term : 2 + 9 * (5 - 1) = 38 := by decide
        rw [h_term] at h_mod_zero3
        exact mod_81_cancel 32 h_inv h_mod_zero3
      have h_le_45 : L.sum ≤ 45 := by
        have := sum_digits_le_9_mul_length L h_L_digits
        omega
      have h_S_pos : L.sum > 0 := by
        by_contra h_sz
        have : L.sum = 0 := by omega
        have h_nil : L ≠ [] := digits_ne_nil_iff_ne_zero.mpr h_N_pos
        have h_last : L.getLast h_nil ≠ 0 := getLast_digit_ne_zero 10 h_N_pos
        have h_mem := List.getLast_mem h_nil
        have h_le := le_sum_of_mem h_mem
        omega
      have : L.sum ≥ 81 := Nat.le_of_dvd h_S_pos h_dvd_S
      omega
    · have h_inv : 47 * 50 ≡ 1 [MOD 81] := by decide
      have h_dvd_S : 81 ∣ L.sum := by
        have h_mod_zero3 : (2 + 9 * (L.length - 1)) * L.sum % 81 = 0 := h_mod_zero2
        rw [h_len] at h_mod_zero3
        have h_term : 2 + 9 * (6 - 1) = 47 := by decide
        rw [h_term] at h_mod_zero3
        exact mod_81_cancel 50 h_inv h_mod_zero3
      have h_le_54 : L.sum ≤ 54 := by
        have := sum_digits_le_9_mul_length L h_L_digits
        omega
      have h_S_pos : L.sum > 0 := by
        by_contra h_sz
        have : L.sum = 0 := by omega
        have h_nil : L ≠ [] := digits_ne_nil_iff_ne_zero.mpr h_N_pos
        have h_last : L.getLast h_nil ≠ 0 := getLast_digit_ne_zero 10 h_N_pos
        have h_mem := List.getLast_mem h_nil
        have h_le := le_sum_of_mem h_mem
        omega
      have : L.sum ≥ 81 := Nat.le_of_dvd h_S_pos h_dvd_S
      omega
    · have h_inv : 56 * 68 ≡ 1 [MOD 81] := by decide
      have h_dvd_S : 81 ∣ L.sum := by
        have h_mod_zero3 : (2 + 9 * (L.length - 1)) * L.sum % 81 = 0 := h_mod_zero2
        rw [h_len] at h_mod_zero3
        have h_term : 2 + 9 * (7 - 1) = 56 := by decide
        rw [h_term] at h_mod_zero3
        exact mod_81_cancel 68 h_inv h_mod_zero3
      have h_le_63 : L.sum ≤ 63 := by
        have := sum_digits_le_9_mul_length L h_L_digits
        omega
      have h_S_pos : L.sum > 0 := by
        by_contra h_sz
        have : L.sum = 0 := by omega
        have h_nil : L ≠ [] := digits_ne_nil_iff_ne_zero.mpr h_N_pos
        have h_last : L.getLast h_nil ≠ 0 := getLast_digit_ne_zero 10 h_N_pos
        have h_mem := List.getLast_mem h_nil
        have h_le := le_sum_of_mem h_mem
        omega
      have : L.sum ≥ 81 := Nat.le_of_dvd h_S_pos h_dvd_S
      omega
    · have h_inv : 65 * 5 ≡ 1 [MOD 81] := by decide
      have h_dvd_S : 81 ∣ L.sum := by
        have h_mod_zero3 : (2 + 9 * (L.length - 1)) * L.sum % 81 = 0 := h_mod_zero2
        rw [h_len] at h_mod_zero3
        have h_term : 2 + 9 * (8 - 1) = 65 := by decide
        rw [h_term] at h_mod_zero3
        exact mod_81_cancel 5 h_inv h_mod_zero3
      have h_le_72 : L.sum ≤ 72 := by
        have := sum_digits_le_9_mul_length L h_L_digits
        omega
      have h_S_pos : L.sum > 0 := by
        by_contra h_sz
        have : L.sum = 0 := by omega
        have h_nil : L ≠ [] := digits_ne_nil_iff_ne_zero.mpr h_N_pos
        have h_last : L.getLast h_nil ≠ 0 := getLast_digit_ne_zero 10 h_N_pos
        have h_mem := List.getLast_mem h_nil
        have h_le := le_sum_of_mem h_mem
        omega
      have : L.sum ≥ 81 := Nat.le_of_dvd h_S_pos h_dvd_S
      omega
    · have h_inv : 74 * 23 ≡ 1 [MOD 81] := by decide
      have h_dvd_S : 81 ∣ L.sum := by
        have h_mod_zero3 : (2 + 9 * (L.length - 1)) * L.sum % 81 = 0 := h_mod_zero2
        rw [h_len9] at h_mod_zero3
        have h_term : 2 + 9 * (9 - 1) = 74 := by decide
        rw [h_term] at h_mod_zero3
        exact mod_81_cancel 23 h_inv h_mod_zero3
      have h_le_81 : L.sum ≤ 81 := by
        have := sum_digits_le_9_mul_length L h_L_digits
        rw [h_len9] at this
        exact this
      have h_S_pos : L.sum > 0 := by
        by_contra h_sz
        have : L.sum = 0 := by omega
        have h_nil : L ≠ [] := digits_ne_nil_iff_ne_zero.mpr h_N_pos
        have h_last : L.getLast h_nil ≠ 0 := getLast_digit_ne_zero 10 h_N_pos
        have h_mem := List.getLast_mem h_nil
        have h_le := le_sum_of_mem h_mem
        omega
      have h_S_81 : L.sum = 81 := by
        have : L.sum ≥ 81 := Nat.le_of_dvd h_S_pos h_dvd_S
        omega
      have h_all_9 : L = List.replicate 9 9 := by
        have := digits_all_nine_of_sum_eq_9_mul_length L h_L_digits
        rw [h_len9] at this
        exact this h_S_81
      have h_N_digits : N = ofDigits 10 (List.replicate 9 9) := by
        rw [← h_all_9]
        exact (ofDigits_digits 10 N).symm
      have h_of_digits_9 : ofDigits 10 (List.replicate 9 9) = 999999999 := by decide
      rw [h_of_digits_9] at h_N_digits
      omega
  have h_find : Nat.find h_ex = 12345679 := find_eq_of_spec_and_min h_ex 12345679 h_spec h_min
  rw [a_def_of_ne_zero_of_exists h_ne h_ex, h_find]


lemma ofDigits_triple (L : List ℕ) :
    ofDigits 10 (L ++ L ++ L) = ofDigits 10 L * (10^(2 * L.length) + 10^(L.length) + 1) := by
  rw [Nat.ofDigits_append, Nat.ofDigits_append]
  simp [List.length_append]
  ring

def D (n : ℕ) : List ℕ :=
  if n < 5 then []
  else if n = 5 then [1, 0, 0, 0, 0, 8, 9, 9, 9, 9, 9, 9, 9, 8, 0, 0, 0, 0, 1]
  else D (n - 1) ++ D (n - 1) ++ D (n - 1)
termination_by n

lemma D_length (n : ℕ) : n ≥ 5 → (D n).length = 19 * 3^(n - 5) := by
  intro hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h5 : n = 5
    · subst h5
      unfold D
      rfl
    · have h_gt : n > 5 := by omega
      unfold D
      have h1 : ¬ n < 5 := by omega
      have h2 : ¬ n = 5 := by omega
      rw [if_neg h1, if_neg h2]
      have ih_step := ih (n - 1) (by omega) (by omega)
      simp [List.length_append, ih_step]
      have h_pow : 3^(n - 1 - 5) + 3^(n - 1 - 5) + 3^(n - 1 - 5) = 3^(n - 5) := by
        have h_eq : n - 5 = (n - 1 - 5) + 1 := by omega
        rw [h_eq, pow_succ]
        ring
      omega

lemma D_reverse (n : ℕ) : n ≥ 5 → (D n).reverse = D n := by
  intro hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h5 : n = 5
    · subst h5
      unfold D
      rfl
    · have h_gt : n > 5 := by omega
      unfold D
      have h1 : ¬ n < 5 := by omega
      have h2 : ¬ n = 5 := by omega
      rw [if_neg h1, if_neg h2]
      have ih_step := ih (n - 1) (by omega) (by omega)
      simp [ih_step]

lemma ten_pow_mod_three (k : ℕ) : 10^k % 3 = 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ]
    have h1 : 10 % 3 = 1 := by rfl
    rw [Nat.mul_mod, h1, ih]

lemma three_dvd_ten_pow_triple (k : ℕ) : 3 ∣ 10^(2 * k) + 10^k + 1 := by
  have h : (10^(2 * k) + 10^k + 1) % 3 = 0 := by
    rw [Nat.add_mod, Nat.add_mod (10^(2*k))]
    rw [ten_pow_mod_three, ten_pow_mod_three]
  exact Nat.dvd_of_mod_eq_zero h

lemma ofDigits_lt_ten_pow (L : List ℕ) (h_digits : ∀ x ∈ L, x < 10) : ofDigits 10 L < 10^L.length := by
  induction L with
  | nil => decide
  | cons d ds ih =>
    simp [ofDigits_eq_foldr] at *
    have h_d : d < 10 := h_digits.1
    have h_ds : ∀ x ∈ ds, x < 10 := h_digits.2
    have ih_val := ih h_ds
    have h_mul : 10 * List.foldr (fun x y => x + 10 * y) 0 ds < 10 * 10^ds.length := Nat.mul_lt_mul_of_pos_left ih_val (by decide)
    omega

lemma D_digits_lt_ten (n : ℕ) : ∀ x ∈ D n, x < 10 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h_lt : n < 5
    · unfold D
      rw [if_pos h_lt]
      simp
    · by_cases h5 : n = 5
      · subst h5
        unfold D
        decide
      · have h_gt : n > 5 := by omega
        unfold D
        have h1 : ¬ n < 5 := by omega
        have h2 : ¬ n = 5 := by omega
        rw [if_neg h1, if_neg h2]
        have ih_step := ih (n - 1) (by omega)
        intro x hx
        simp [List.mem_append] at hx
        aesop

lemma D_ne_nil (n : ℕ) (hn : n ≥ 5) : D n ≠ [] := by
  have h_len : (D n).length > 0 := by
    rw [D_length n hn]
    have h_pow : 3^(n-5) > 0 := Nat.pow_pos (by decide)
    omega
  exact List.ne_nil_of_length_pos h_len

lemma getLast_triple {α : Type _} (A : List α) (h : A ≠ []) :
    (A ++ A ++ A).getLast (by simp [h]) = A.getLast h := by
  have h_ne : A ++ A ≠ [] := by simp [h]
  have h_last1 : (A ++ A ++ A).getLast (by simp [h]) = (A ++ A).getLast h_ne := by
    rw [List.getLast_append]
    simp [h]
  have h_last2 : (A ++ A).getLast h_ne = A.getLast h := by
    rw [List.getLast_append]
    simp [h]
  rw [h_last1, h_last2]

lemma D_getLast (n : ℕ) (hn : n ≥ 5) (h : D n ≠ []) : (D n).getLast h = 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h5 : n = 5
    · subst h5
      unfold D
      rfl
    · have h_gt : n > 5 := by omega
      have h1 : ¬ n < 5 := by omega
      have h2 : ¬ n = 5 := by omega
      have h_eq : D n = D (n - 1) ++ D (n - 1) ++ D (n - 1) := by
        rw [D]; rw [if_neg h1, if_neg h2]
      have h_last : (D n).getLast h = (D (n - 1) ++ D (n - 1) ++ D (n - 1)).getLast (by rw [← h_eq]; exact h) := by
        congr 1
      rw [h_last]
      rw [getLast_triple (D (n - 1)) (D_ne_nil (n - 1) (by omega))]
      exact ih (n - 1) (by omega) (by omega) (D_ne_nil (n - 1) (by omega))

lemma D_div (n : ℕ) : n ≥ 5 → 3^n ∣ ofDigits 10 (D n) := by
  intro hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h5 : n = 5
    · subst h5
      unfold D
      decide
    · have h_gt : n > 5 := by omega
      unfold D
      have h1 : ¬ n < 5 := by omega
      have h2 : ¬ n = 5 := by omega
      rw [if_neg h1, if_neg h2]
      have ih_step := ih (n - 1) (by omega) (by omega)
      rw [ofDigits_triple]
      have h_dvd1 : 3^(n-1) ∣ ofDigits 10 (D (n-1)) := ih_step
      have h_dvd2 : 3 ∣ 10^(2 * (D (n-1)).length) + 10^((D (n-1)).length) + 1 := three_dvd_ten_pow_triple _
      have h_eq : 3^n = 3^(n-1) * 3 := by
        have h_eq2 : n = (n-1) + 1 := by omega
        nth_rw 1 [h_eq2]
        rw [pow_succ]
      rw [h_eq]
      exact mul_dvd_mul h_dvd1 h_dvd2

lemma D_pos (n : ℕ) : n ≥ 5 → ofDigits 10 (D n) > 0 := by
  intro hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h5 : n = 5
    · subst h5
      unfold D
      decide
    · have h_gt : n > 5 := by omega
      unfold D
      have h1 : ¬ n < 5 := by omega
      have h2 : ¬ n = 5 := by omega
      rw [if_neg h1, if_neg h2]
      rw [ofDigits_triple]
      have ih_step := ih (n - 1) (by omega) (by omega)
      have h_pos : 10^(2 * (D (n-1)).length) + 10^((D (n-1)).length) + 1 > 0 := Nat.zero_lt_succ _
      exact mul_pos ih_step h_pos

lemma ten_pow_sub_one_lt (k : ℕ) (hk : k > 0) : 10^(k - 1) < 10^k - 1 := by
  have h_eq : k = (k - 1) + 1 := by omega
  nth_rw 2 [h_eq]
  rw [pow_succ]
  have h_y : 10^(k - 1) ≥ 1 := Nat.one_le_pow _ 10 (by decide)
  omega

lemma D_lt_bound (n : ℕ) (hn : n ≥ 5) : ofDigits 10 (D n) < 10^(3^(n - 2)) - 1 := by
  have h1 : ofDigits 10 (D n) < 10^(D n).length := ofDigits_lt_ten_pow (D n) (D_digits_lt_ten n)
  rw [D_length n hn] at h1
  have h2 : 19 * 3^(n - 5) < 3^(n - 2) := by
    have h_eq : n - 2 = (n - 5) + 3 := by omega
    rw [h_eq, pow_add]
    have h_pow : 3^3 = 27 := by decide
    rw [h_pow]
    have h_pos : 3^(n - 5) > 0 := Nat.pow_pos (by decide)
    omega
  have h3 : 10^(19 * 3^(n - 5)) < 10^(3^(n - 2)) - 1 := by
    have h_le : 10^(19 * 3^(n-5)) ≤ 10^(3^(n-2) - 1) := by
      have h_sub : 19 * 3^(n-5) ≤ 3^(n-2) - 1 := by omega
      exact Nat.pow_le_pow_right (by decide) h_sub
    have h_sub2 : 10^(3^(n-2) - 1) < 10^(3^(n-2)) - 1 := by
      apply ten_pow_sub_one_lt
      exact Nat.pow_pos (by decide)
    exact Nat.lt_of_le_of_lt h_le h_sub2
  exact Nat.lt_trans h1 h3

lemma D_reverse_nat (n : ℕ) (hn : n ≥ 5) : reverse_nat (ofDigits 10 (D n)) = ofDigits 10 (D n) := by
  have h_ne : D n ≠ [] := D_ne_nil n hn
  have h_last : (D n).getLast h_ne ≠ 0 := by
    rw [D_getLast n hn h_ne]
    decide
  have h_digits : ∀ x ∈ D n, x < 10 := D_digits_lt_ten n
  have h_digits_of_digits : digits 10 (ofDigits 10 (D n)) = D n :=
    digits_ofDigits 10 (by decide) (D n) h_digits (fun _ => h_last)
  unfold reverse_nat
  rw [h_digits_of_digits, D_reverse n hn]

theorem a_gt_4_ne (n : ℕ) : n ≥ 5 → a (3^n) ≠ 10 ^ (3 ^ (n - 2)) - 1 := by
  intro hn
  have h_ne : 3^n ≠ 0 := by
    apply Nat.ne_of_gt
    apply Nat.pow_pos
    decide
  have h_div : 3^n ∣ ofDigits 10 (D n) := D_div n hn
  rcases h_div with ⟨K, h_K⟩
  have h_K2 : ofDigits 10 (D n) = K * 3^n := by
    rw [h_K, Nat.mul_comm]
  have h_pos : ofDigits 10 (D n) > 0 := D_pos n hn
  have h_K_pos : K > 0 := by
    by_contra h_zero
    push_neg at h_zero
    have : K = 0 := by omega
    subst this
    simp at h_K2
    omega
  have h_rev_div : 3^n ∣ reverse_nat (K * 3^n) := by
    rw [← h_K2]
    rw [D_reverse_nat n hn]
    exact D_div n hn
  have h_spec : K > 0 ∧ 3^n ∣ reverse_nat (K * 3^n) := ⟨h_K_pos, h_rev_div⟩
  have h_ex : ∃ k, k > 0 ∧ 3^n ∣ reverse_nat (k * 3^n) := ⟨K, h_spec⟩
  have h_find : Nat.find h_ex ≤ K := Nat.find_le h_spec
  have h_a_le : a (3^n) ≤ ofDigits 10 (D n) := by
    rw [a_def_of_ne_zero_of_exists h_ne h_ex]
    rw [h_K2]
    exact Nat.mul_le_mul_right (3^n) h_find
  have h_lt : ofDigits 10 (D n) < 10 ^ (3 ^ (n - 2)) - 1 := D_lt_bound n hn
  have h_a_lt : a (3^n) < 10 ^ (3 ^ (n - 2)) - 1 := Nat.lt_of_le_of_lt h_a_le h_lt
  apply Nat.ne_of_lt h_a_lt

/--
Conjecture A062567: It seems that only for n=2,3 & 4 we have a($3^n$) = $10^{3^{n-2}} - 1$.
(Formalized for $n \ge 2$ so that $n-2$ is a natural number exponent.)
-/
theorem oeis_62567_conjecture_0 (n : ℕ) :
  2 ≤ n → (a (3^n) = 10 ^ (3 ^ (n - 2)) - 1 ↔ n = 2 ∨ n = 3 ∨ n = 4) := by
  intro hn
  constructor
  · intro h_eq
    have h_cases : n = 2 ∨ n = 3 ∨ n = 4 ∨ n ≥ 5 := by omega
    rcases h_cases with rfl | rfl | rfl | h_ge
    · left; rfl
    · right; left; rfl
    · right; right; rfl
    · have h_ne := a_gt_4_ne n h_ge
      contradiction
  · rintro (rfl | rfl | rfl)
    · -- n = 2
      have h_a9 := a_9
      have h_rhs : 10 ^ (3 ^ (2 - 2)) - 1 = 9 := by decide
      rw [h_rhs]
      exact h_a9
    · -- n = 3
      have h_a27 := a_27
      have h_rhs : 10 ^ (3 ^ (3 - 2)) - 1 = 999 := by decide
      rw [h_rhs]
      exact h_a27
    · -- n = 4
      have h_a81 := a_81_eq
      have h_rhs : 10 ^ (3 ^ (4 - 2)) - 1 = 999999999 := by decide
      rw [h_rhs]
      exact h_a81
