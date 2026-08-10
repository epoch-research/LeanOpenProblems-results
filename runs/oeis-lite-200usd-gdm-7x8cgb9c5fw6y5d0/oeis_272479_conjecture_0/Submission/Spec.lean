import FormalConjectures.Util.ProblemImports

open Nat
open Classical

/--
A272479: $a(n)$ is the smallest $k$ different from $n$ such that $(n, k)$ is a Harshad amicable pair.
Let $D(n)$ be the sum of digits of $n$.
$m$ and $k$ are Harshad amicable if they are distinct integers such that $D(m) \mid k$ and $D(k) \mid m$.
For any $n$ with no Harshad amicable partner, $a(n)=0$ (Conjecture: the sequence contains no zeros.)
-/
noncomputable def a (n : ℕ) : ℕ :=
  let dsum (m : ℕ) : ℕ := (digits 10 m).sum

  let partners : Set ℕ := {k | k > 0 ∧ k ≠ n ∧ dsum n ∣ k ∧ dsum k ∣ n}

  -- The set of partners is bounded below by 1. If it is non-empty, `sInf`
  -- correctly returns the smallest element. If empty, we return 0 as per the OEIS comment.
  if h : partners.Nonempty then
    sInf partners
  else
    0

def D (m : ℕ) : ℕ := (digits 10 m).sum

theorem D_zero : D 0 = 0 := by
  unfold D
  rw [digits_zero]
  rfl

theorem D_single_digit (x : ℕ) (hx : x < 10) : D x = x := by
  unfold D
  by_cases hx0 : x = 0
  · rw [hx0, digits_zero]; rfl
  · have h1 : digits 10 x = [x] := Nat.digits_of_lt 10 x hx0 hx
    rw [h1]
    simp

theorem D_shift_add (A B a : ℕ) (hB : B < 10^a) (hA : 0 < A) :
    D (B + 10^a * A) = D B + D A := by
  unfold D
  have h_len : (digits 10 B).length ≤ a := (Nat.digits_length_le_iff (b := 10) (k := a) (by decide) B).mpr hB
  let k := a - (digits 10 B).length
  have h_eq : (digits 10 B).length + k = a := Nat.add_sub_of_le h_len
  have h_append := Nat.digits_append_zeroes_append_digits (b := 10) (k := k) (m := A) (n := B) (by decide) hA
  rw [h_eq] at h_append
  rw [← h_append]
  simp only [List.sum_append, List.sum_replicate, nsmul_zero, add_zero]

theorem D_nine : D 9 = 9 := D_single_digit 9 (by decide)

theorem D_pow_ten_sub_one (a : ℕ) : D (10^a - 1) = 9 * a := by
  induction' a with a ih
  · simp [D]
  · have h1 : 10^(a+1) - 1 = (10^a - 1) + 10^a * 9 := by
      have : 10^(a+1) = 10^a * 9 + 10^a := by ring
      rw [this]
      omega
    rw [h1]
    have h_pos : 10^a > 0 := by positivity
    have h2 : D ((10^a - 1) + 10^a * 9) = D (10^a - 1) + D 9 := by
      apply D_shift_add
      · omega
      · decide
    rw [h2, D_nine, ih]
    ring

theorem d_split (a d : ℕ) (hd : 10^a ≤ d) (hda : d < 10^(a+1)) :
    ∃ h r : ℕ, d = h * 10^a + r ∧ 1 ≤ h ∧ h ≤ 9 ∧ r < 10^a := by
  use d / 10^a, d % 10^a
  have h_div_add_mod := Nat.div_add_mod d (10^a)
  have h_mod_lt := Nat.mod_lt d (by positivity : 10^a > 0)
  have h_eq : d = d / 10^a * 10^a + d % 10^a := by
    rw [mul_comm]
    exact h_div_add_mod.symm
  refine ⟨h_eq, ?_, ?_, h_mod_lt⟩
  · by_contra h_zero
    have h_zero' : d / 10^a = 0 := by
      cases h : d / 10^a with
      | zero => rfl
      | succ k => omega
    rw [h_zero', zero_mul, zero_add] at h_eq
    omega
  · have h_lt : d < 10 * 10^a := by
      have : 10^(a+1) = 10 * 10^a := by
        rw [pow_succ]
        ring
      omega
    by_contra h_ge
    have : d / 10^a ≥ 10 := by omega
    have : d ≥ 10 * 10^a := by
      calc
        d = d / 10^a * 10^a + d % 10^a := h_eq
        _ ≥ 10 * 10^a + d % 10^a := Nat.add_le_add_right (Nat.mul_le_mul_right (10^a) this) (d % 10^a)
        _ ≥ 10 * 10^a := Nat.le_add_right _ _
    omega

theorem D_complement (a d : ℕ) (hd1 : 1 < d) (hda : d < 10^a) :
    D (10^a - d) + D (d - 1) = 9 * a := by
  induction' a with a ih generalizing d
  · simp only [pow_zero] at hda
    omega
  · by_cases h_lt : d < 10^a
    · have ih_d := ih d hd1 h_lt
      have h1 : 10^(a+1) - d = (10^a - d) + 10^a * 9 := by
        have : 10^(a+1) = 10^a * 9 + 10^a := by ring
        rw [this]
        omega
      rw [h1]
      have h2 : D ((10^a - d) + 10^a * 9) = D (10^a - d) + D 9 := by
        apply D_shift_add
        · omega
        · decide
      rw [h2, D_nine]
      omega
    · have hd_ge : 10^a ≤ d := by omega
      have ⟨h, r, h_eq, h_h1, h_h9, h_r⟩ := d_split a d hd_ge hda
      have h_pos : 10^a > 0 := by positivity
      by_cases hr0 : r = 0
      · rw [hr0, add_zero] at h_eq
        have hd_dec : d - 1 = (h - 1) * 10^a + (10^a - 1) := by
          have : h * 10^a = (h - 1) * 10^a + 10^a := by
            have h_eq2 : h * 10^a = ((h - 1) + 1) * 10^a := by
              congr 1
              omega
            rw [h_eq2, add_mul, one_mul]
          rw [← h_eq] at this
          omega
        by_cases hh1 : h = 1
        · have hd_sub1 : d - 1 = 10^a - 1 := by
            rw [hd_dec, hh1, Nat.sub_self, zero_mul, zero_add]
          have h_comp : 10^(a+1) - d = 10^a * 9 := by
            have h_pow : 10^(a+1) = 10 * 10^a := by rw [pow_succ]; ring
            rw [h_pow, h_eq, hh1, one_mul]
            rw [mul_comm 10 (10^a)]
            omega
          rw [hd_sub1, h_comp]
          have h_d_comp : D (10^a * 9) = D 9 := by
            have : D (10^a * 9) = D (0 + 10^a * 9) := by rw [zero_add]
            rw [this, D_shift_add 9 0 a (by positivity) (by decide)]
            rw [D_zero, zero_add]
          rw [h_d_comp, D_nine, D_pow_ten_sub_one]
          ring
        · have hh1_gt : 1 < h := by omega
          have h_d1 : D (d - 1) = (h - 1) + 9 * a := by
            have h_comm : (h - 1) * 10^a + (10^a - 1) = (10^a - 1) + 10^a * (h - 1) := by
              rw [add_comm, mul_comm]
            rw [hd_dec, h_comm]
            have h_sa := D_shift_add (h - 1) (10^a - 1) a (by omega) (by omega)
            rw [h_sa, D_pow_ten_sub_one]
            have : D (h - 1) = h - 1 := by
              apply D_single_digit
              omega
            rw [this]
            omega
          have h_comp : 10^(a+1) - d = (10 - h) * 10^a := by
            have h_pow : 10^(a+1) = 10 * 10^a := by rw [pow_succ]; ring
            rw [h_pow, h_eq, Nat.sub_mul]
          have h_d_comp : D ((10 - h) * 10^a) = 10 - h := by
            have : (10 - h) * 10^a = 10^a * (10 - h) := mul_comm _ _
            have : D ((10 - h) * 10^a) = D (0 + 10^a * (10 - h)) := by rw [zero_add, mul_comm]
            rw [this, D_shift_add (10 - h) 0 a (by positivity) (by omega)]
            have : D (10 - h) = 10 - h := by
              apply D_single_digit
              omega
            rw [this, D_zero, zero_add]
          rw [h_d1, h_comp, h_d_comp]
          omega
      · have hr0_gt : 0 < r := by omega
        have h_d1 : D (d - 1) = h + D (r - 1) := by
          have hd_dec : d - 1 = (r - 1) + 10^a * h := by
            rw [h_eq, mul_comm h (10^a)]
            omega
          rw [hd_dec, D_shift_add h (r - 1) a (by omega) (by omega)]
          have : D h = h := D_single_digit h (by omega)
          rw [this, add_comm]
        have h_comp_eq : 10^(a+1) - d = (10^a - r) + 10^a * (9 - h) := by
          have h_pow : 10^(a+1) = 10 * 10^a := by rw [pow_succ]; ring
          rw [h_pow, h_eq, mul_comm h (10^a)]
          clear ih hd1 hda h_lt hd_ge h_pos h_d1 h_pow h_eq h_h1
          generalize hX : 10^a = X at h_r ⊢
          have h_sub : X * (9 - h) = 9 * X - X * h := by
            calc
              X * (9 - h) = (9 - h) * X := mul_comm _ _
              _ = 9 * X - h * X := by rw [Nat.sub_mul]
              _ = 9 * X - X * h := by rw [mul_comm h X]
          have h_le1 : X * h + r < 10 * X := by
            calc
              X * h + r ≤ X * 9 + r := Nat.add_le_add_right (Nat.mul_le_mul_left X h_h9) _
              _ < X * 9 + X := Nat.add_lt_add_left h_r _
              _ = X * 10 := by ring
              _ = 10 * X := mul_comm _ _
          have h_le2 : X * h ≤ 9 * X := by
            calc
              X * h ≤ X * 9 := Nat.mul_le_mul_left X h_h9
              _ = 9 * X := mul_comm _ _
          have h_le3 : r ≤ X := Nat.le_of_lt h_r
          rw [h_sub]
          omega
        have h_d_comp : D (10^(a+1) - d) = 9 - h + D (10^a - r) := by
          rw [h_comp_eq]
          by_cases hh9 : h = 9
          · rw [hh9, Nat.sub_self, mul_zero, add_zero]
            omega
          · have hh9_lt : 9 - h > 0 := by omega
            rw [D_shift_add (9 - h) (10^a - r) a (by omega) hh9_lt]
            have : D (9 - h) = 9 - h := D_single_digit (9 - h) (by omega)
            rw [this, add_comm]
        rw [h_d1, h_d_comp]
        by_cases hr1 : r = 1
        · rw [hr1, Nat.sub_self]
          rw [D_zero, add_zero, D_pow_ten_sub_one]
          omega
        · have hr1_gt : 1 < r := by omega
          have ih_r := ih r hr1_gt h_r
          omega

theorem D_pos (n : ℕ) (hn : n > 0) : D n > 0 := by
  by_contra h0
  have h_sum : D n = 0 := by omega
  unfold D at h_sum
  have h_ne : digits 10 n ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr (by omega)
  have h_last : List.getLast (digits 10 n) h_ne ≠ 0 := Nat.getLast_digit_ne_zero 10 (by omega)
  have h_mem : List.getLast (digits 10 n) h_ne ∈ digits 10 n := List.getLast_mem h_ne
  have h_zero : ∀ x ∈ digits 10 n, x = 0 := List.sum_eq_zero_iff.mp h_sum
  have : List.getLast (digits 10 n) h_ne = 0 := h_zero _ h_mem
  contradiction

theorem D_le_self (n : ℕ) : D n ≤ n := by
  unfold D
  have h1 : (digits 10 n).sum ≤ ofDigits 10 (digits 10 n) := Nat.sum_le_ofDigits (digits 10 n) (by decide)
  have h2 : ofDigits 10 (digits 10 n) = n := Nat.ofDigits_digits 10 n
  rw [h2] at h1
  exact h1


theorem ofDigits_ge_two_mul_sum (L : List ℕ) (h_all : ∀ x ∈ L, x < 10) (h_val : ofDigits 10 L ≥ 36) :
    2 * L.sum ≤ ofDigits 10 L := by
  cases L with
  | nil =>
    simp at h_val
  | cons d t =>
    simp only [ofDigits, List.sum_cons]
    have h_sum_le : t.sum ≤ ofDigits 10 t := Nat.sum_le_ofDigits t (by decide)
    have hd : d < 10 := h_all d (by simp)
    have ht_val : ofDigits 10 t ≥ 2 := by
      by_contra h_lt
      have h_lt' : ofDigits 10 t ≤ 1 := by omega
      dsimp [ofDigits] at h_val
      omega
    have : 2 * t.sum + d ≤ 10 * ofDigits 10 t := by
      have : t.sum ≤ ofDigits 10 t := h_sum_le
      omega
    dsimp [ofDigits]
    omega

theorem D_two_mul_le (n : ℕ) (hn : n ≥ 36) : 2 * D n ≤ n := by
  unfold D
  have h_all : ∀ x ∈ digits 10 n, x < 10 := fun x hx => Nat.digits_lt_base (by decide) hx
  have h_val : ofDigits 10 (digits 10 n) ≥ 36 := by
    rw [Nat.ofDigits_digits 10 n]
    exact hn
  have h_le := ofDigits_ge_two_mul_sum (digits 10 n) h_all h_val
  rw [Nat.ofDigits_digits 10 n] at h_le
  exact h_le

theorem nine_mul_lt_pow_ten (a : ℕ) : 9 * a < 10^a := by
  induction' a with a ih
  · simp
  · by_cases ha0 : a = 0
    · rw [ha0]; decide
    · have : 10^(a+1) = 10^a * 10 := by ring
      rw [this]
      have : 9 * (a + 1) = 9 * a + 9 := by ring
      rw [this]
      have : 9 * a + 9 < 10^a * 10 := by
        calc
          9 * a + 9 < 10^a + 9 := by omega
          _ < 10^a * 10 := by
            have : 10^a ≥ 10 := by
              cases a with
              | zero => omega
              | succ a' =>
                have : 10^(a'+1) = 10^a' * 10 := by ring
                rw [this]
                have : 10^a' ≥ 1 := by
                  have : 10^a' > 0 := by positivity
                  omega
                omega
            omega
      exact this


theorem pow_ten_sub_one_pos (a : ℕ) (ha : a > 0) : 10^a - 1 > 0 := by
  have : 10^a ≥ 10 := by
    cases a with
    | zero => omega
    | succ a' =>
      have : 10^(a'+1) = 10^a' * 10 := by ring
      rw [this]
      have : 10^a' ≥ 1 := by
        have : 10^a' > 0 := by positivity
        omega
      omega
  omega


theorem D_of_lt_100 (n : ℕ) (hn : n < 100) : D n = n / 10 + n % 10 := by
  by_cases hn0 : n = 0
  · rw [hn0, D_zero]
  · by_cases hn10 : n < 10
    · have : n / 10 = 0 := Nat.div_eq_of_lt hn10
      have : n % 10 = n := Nat.mod_eq_of_lt hn10
      rw [D_single_digit n hn10]
      omega
    · have hn10' : 10 ≤ n := by omega
      have h_eq : n = (n % 10) + 10^1 * (n / 10) := by
        have : n = 10 * (n / 10) + n % 10 := (Nat.div_add_mod n 10).symm
        omega
      rw [h_eq]
      rw [D_shift_add (n / 10) (n % 10) 1]
      · have : n % 10 < 10 := Nat.mod_lt n (by decide)
        have : n / 10 < 10 := by
          have : n < 10 * 10 := hn
          exact Nat.div_lt_of_lt_mul hn
        rw [D_single_digit (n % 10) (by omega), D_single_digit (n / 10) (by omega)]
        omega
      · simp only [pow_one]
        exact Nat.mod_lt n (by decide)
      · have : n ≥ 10 := hn10'
        omega

theorem d_lt_pow_a_small (n : ℕ) (hn10 : n ≥ 10) (hn36 : n < 36) :
    let d := (digits 10 n).sum
    let a := (n - (digits 10 d).sum) / 9
    d < 10^a := by
  intro d a
  have hd_eq : (digits 10 n).sum = n / 10 + n % 10 := D_of_lt_100 n (by omega)
  have hd_lt_100 : (digits 10 n).sum < 100 := by omega
  have hdd_eq : (digits 10 (digits 10 n).sum).sum = (digits 10 n).sum / 10 + (digits 10 n).sum % 10 := D_of_lt_100 ((digits 10 n).sum) hd_lt_100
  change (digits 10 n).sum < 10^((n - (digits 10 (digits 10 n).sum).sum) / 9)
  rw [hdd_eq, hd_eq]
  interval_cases n <;> decide

theorem test_prod (a d : ℕ) (hd1 : 1 < d) (hda : d < 10^a) :
    d * (10^a - 1) = (d - 1) * 10^a + (10^a - d) := by
  have h1 : d * (10^a - 1) + d = d * 10^a := by
    rw [Nat.mul_sub_left_distrib, mul_one]
    have : d ≤ d * 10^a := by
      calc
        d = d * 1 := by ring
        _ ≤ d * 10^a := Nat.mul_le_mul_left d (Nat.one_le_pow a 10 (by decide))
    omega
  have h2 : (d - 1) * 10^a + (10^a - d) + d = d * 10^a := by
    rw [add_assoc, Nat.sub_add_cancel (by omega)]
    rw [Nat.sub_mul, one_mul]
    have : 10^a ≤ d * 10^a := by
      calc
        10^a = 1 * 10^a := by ring
        _ ≤ d * 10^a := Nat.mul_le_mul_right (10^a) (by omega)
    omega
  omega

/-- A272479 Conjecture: the sequence contains no zeros. -/
theorem oeis_272479_conjecture_0 : ∀ n : ℕ, n > 0 → a n ≠ 0 := by
  intro n hn
  unfold a
  dsimp
  split_ifs with h
  · have h_mem : sInf {k | k > 0 ∧ k ≠ n ∧ (digits 10 n).sum ∣ k ∧ (digits 10 k).sum ∣ n} ∈ {k | k > 0 ∧ k ≠ n ∧ (digits 10 n).sum ∣ k ∧ (digits 10 k).sum ∣ n} := Nat.sInf_mem h
    rcases h_mem with ⟨h_pos, _, _, _⟩
    exact _root_.ne_of_gt h_pos
  · exfalso
    apply h
    by_cases hn9 : n ≤ 9
    · interval_cases n
      · -- n = 1
        use 10
        have h1 : digits 10 1 = [1] := Nat.digits_of_lt 10 1 (by decide) (by decide)
        have h2 : (digits 10 1).sum = 1 := by rw [h1]; rfl
        have h3 : digits 10 10 = 0 :: digits 10 1 := Nat.digits_add 10 (by decide) 0 1 (by decide) (Or.inr (by decide))
        have h4 : (digits 10 10).sum = 1 := by rw [h3, List.sum_cons, h2]
        refine ⟨by decide, by decide, by rw [h2]; decide, by rw [h4]⟩
      · -- n = 2
        use 20
        have h1 : digits 10 2 = [2] := Nat.digits_of_lt 10 2 (by decide) (by decide)
        have h2 : (digits 10 2).sum = 2 := by rw [h1]; rfl
        have h3 : digits 10 20 = 0 :: digits 10 2 := Nat.digits_add 10 (by decide) 0 2 (by decide) (Or.inr (by decide))
        have h4 : (digits 10 20).sum = 2 := by rw [h3, List.sum_cons, h2]
        refine ⟨by decide, by decide, by rw [h2]; decide, by rw [h4]⟩
      · -- n = 3
        use 30
        have h1 : digits 10 3 = [3] := Nat.digits_of_lt 10 3 (by decide) (by decide)
        have h2 : (digits 10 3).sum = 3 := by rw [h1]; rfl
        have h3 : digits 10 30 = 0 :: digits 10 3 := Nat.digits_add 10 (by decide) 0 3 (by decide) (Or.inr (by decide))
        have h4 : (digits 10 30).sum = 3 := by rw [h3, List.sum_cons, h2]
        refine ⟨by decide, by decide, by rw [h2]; decide, by rw [h4]⟩
      · -- n = 4
        use 40
        have h1 : digits 10 4 = [4] := Nat.digits_of_lt 10 4 (by decide) (by decide)
        have h2 : (digits 10 4).sum = 4 := by rw [h1]; rfl
        have h3 : digits 10 40 = 0 :: digits 10 4 := Nat.digits_add 10 (by decide) 0 4 (by decide) (Or.inr (by decide))
        have h4 : (digits 10 40).sum = 4 := by rw [h3, List.sum_cons, h2]
        refine ⟨by decide, by decide, by rw [h2]; decide, by rw [h4]⟩
      · -- n = 5
        use 50
        have h1 : digits 10 5 = [5] := Nat.digits_of_lt 10 5 (by decide) (by decide)
        have h2 : (digits 10 5).sum = 5 := by rw [h1]; rfl
        have h3 : digits 10 50 = 0 :: digits 10 5 := Nat.digits_add 10 (by decide) 0 5 (by decide) (Or.inr (by decide))
        have h4 : (digits 10 50).sum = 5 := by rw [h3, List.sum_cons, h2]
        refine ⟨by decide, by decide, by rw [h2]; decide, by rw [h4]⟩
      · -- n = 6
        use 60
        have h1 : digits 10 6 = [6] := Nat.digits_of_lt 10 6 (by decide) (by decide)
        have h2 : (digits 10 6).sum = 6 := by rw [h1]; rfl
        have h3 : digits 10 60 = 0 :: digits 10 6 := Nat.digits_add 10 (by decide) 0 6 (by decide) (Or.inr (by decide))
        have h4 : (digits 10 60).sum = 6 := by rw [h3, List.sum_cons, h2]
        refine ⟨by decide, by decide, by rw [h2]; decide, by rw [h4]⟩
      · -- n = 7
        use 70
        have h1 : digits 10 7 = [7] := Nat.digits_of_lt 10 7 (by decide) (by decide)
        have h2 : (digits 10 7).sum = 7 := by rw [h1]; rfl
        have h3 : digits 10 70 = 0 :: digits 10 7 := Nat.digits_add 10 (by decide) 0 7 (by decide) (Or.inr (by decide))
        have h4 : (digits 10 70).sum = 7 := by rw [h3, List.sum_cons, h2]
        refine ⟨by decide, by decide, by rw [h2]; decide, by rw [h4]⟩
      · -- n = 8
        use 80
        have h1 : digits 10 8 = [8] := Nat.digits_of_lt 10 8 (by decide) (by decide)
        have h2 : (digits 10 8).sum = 8 := by rw [h1]; rfl
        have h3 : digits 10 80 = 0 :: digits 10 8 := Nat.digits_add 10 (by decide) 0 8 (by decide) (Or.inr (by decide))
        have h4 : (digits 10 80).sum = 8 := by rw [h3, List.sum_cons, h2]
        refine ⟨by decide, by decide, by rw [h2]; decide, by rw [h4]⟩
      · -- n = 9
        use 90
        have h1 : digits 10 9 = [9] := Nat.digits_of_lt 10 9 (by decide) (by decide)
        have h2 : (digits 10 9).sum = 9 := by rw [h1]; rfl
        have h3 : digits 10 90 = 0 :: digits 10 9 := Nat.digits_add 10 (by decide) 0 9 (by decide) (Or.inr (by decide))
        have h4 : (digits 10 90).sum = 9 := by rw [h3, List.sum_cons, h2]
        refine ⟨by decide, by decide, by rw [h2]; decide, by rw [h4]⟩

    · by_cases h_harshad : (digits 10 n).sum ∣ n
      · use 10 * n
        have h1' : digits 10 (0 + 10 * n) = 0 :: digits 10 n := Nat.digits_add 10 (by decide) 0 n (by omega) (Or.inr (by omega))
        have h1 : digits 10 (10 * n) = 0 :: digits 10 n := by rw [zero_add] at h1'; exact h1'
        have h2 : (digits 10 (10 * n)).sum = (digits 10 n).sum := by rw [h1, List.sum_cons, zero_add]
        refine ⟨by omega, by omega, ?_, ?_⟩
        · exact dvd_mul_of_dvd_right h_harshad 10
        · rw [h2]; exact h_harshad
      · -- Non-Harshad case for n >= 10
        let d := (digits 10 n).sum
        have hd1 : 1 < d := by
          by_contra hd_le
          have hd_cases : d = 0 ∨ d = 1 := by omega
          rcases hd_cases with hd0 | hd1'
          · have hn_pos : D n > 0 := D_pos n (by omega)
            have : d > 0 := hn_pos
            omega
          · have h_div : d ∣ n := by rw [hd1']; exact one_dvd n
            contradiction
        have h_mod : n ≡ d [MOD 9] := Nat.modEq_digits_sum 9 10 (by decide) n
        have h_mod_d : d ≡ (digits 10 d).sum [MOD 9] := Nat.modEq_digits_sum 9 10 (by decide) d
        have h_mod_trans : n ≡ (digits 10 d).sum [MOD 9] := Nat.ModEq.trans h_mod h_mod_d
        have h_lt_d : (digits 10 d).sum < n := by
          have hd_le_n : d ≤ n := D_le_self n
          have hdd_le_d : (digits 10 d).sum ≤ d := D_le_self d
          have h_ne : d ≠ n := by
            intro h_eq
            change ¬ d ∣ n at h_harshad
            rw [h_eq] at h_harshad
            have : n ∣ n := dvd_refl n
            contradiction
          omega
        have h_sub_mod : 9 ∣ n - (digits 10 d).sum := (Nat.modEq_iff_dvd' (Nat.le_of_lt h_lt_d)).mp h_mod_trans.symm
        let a := (n - (digits 10 d).sum) / 9
        have ha_eq : 9 * a = n - (digits 10 d).sum := Nat.mul_div_cancel' h_sub_mod
        have hda : d < 10^a := by
          by_cases hn36 : n < 36
          · have hn10 : n ≥ 10 := by omega
            exact d_lt_pow_a_small n hn10 hn36
          · have hn36' : n ≥ 36 := by omega
            have h_two_mul := D_two_mul_le n hn36'
            have h_dd_le : D d ≤ d := D_le_self d
            have h_sum_le : d + D d ≤ n := by
              calc
                d + D d ≤ d + d := Nat.add_le_add_left h_dd_le d
                _ = 2 * d := by ring
                _ ≤ n := h_two_mul
            have h_sub_le : d ≤ n - D d := by omega
            have h_9a_eq : n - D d = 9 * a := ha_eq.symm
            have h_d_le_9a : d ≤ 9 * a := by omega
            have h_9a_lt : 9 * a < 10^a := nine_mul_lt_pow_ten a
            omega
        let c := a + (digits 10 d).length
        let k := d * (10^a - 1) * 10^c + d
        use k
        have hk_eq : k = d * ((10^a - 1) * 10^c + 1) := by
          calc
            k = d * (10^a - 1) * 10^c + d := rfl
            _ = d * ((10^a - 1) * 10^c) + d := by ring
            _ = d * ((10^a - 1) * 10^c + 1) := by ring
        have h_dk : d ∣ k := ⟨(10^a - 1) * 10^c + 1, hk_eq⟩
        have hk_pos : k > 0 := by
          have : d > 0 := by omega
          have : a > 0 := by
            have : n - (digits 10 d).sum > 0 := by omega
            omega
          have : 10^a - 1 > 0 := pow_ten_sub_one_pos a this
          omega
        have h_k_ne : k ≠ n := by
          intro hk_n
          rw [hk_n] at h_dk
          contradiction
        have hd_lt_pow_len : d < 10^(digits 10 d).length := (Nat.digits_length_le_iff (by decide) d).mp (Nat.le_refl _)
        have hd_lt_pow_c : d < 10^c := by
          calc
            d < 10^(digits 10 d).length := hd_lt_pow_len
            _ ≤ 10^c := by
              have : (digits 10 d).length ≤ c := by omega
              exact Nat.pow_le_pow_right (by decide) this
        have h_sum_k : D k = n := by
          have hk_rew : k = d + 10^c * (d * (10^a - 1)) := by ring
          rw [hk_rew]
          have h_sa : D (d + 10^c * (d * (10^a - 1))) = D d + D (d * (10^a - 1)) := by
            apply D_shift_add
            · exact hd_lt_pow_c
            · have h_pos1 : d > 0 := by omega
              have ha_pos : a > 0 := by
                have : n - (digits 10 d).sum > 0 := by omega
                omega
              have h_pos2 : 10^a - 1 > 0 := pow_ten_sub_one_pos a ha_pos
              positivity
          rw [h_sa]
          have h_prod : d * (10^a - 1) = (d - 1) * 10^a + (10^a - d) := test_prod a d hd1 hda
          have h_prod_comm : (d - 1) * 10^a + (10^a - d) = (10^a - d) + 10^a * (d - 1) := by ring
          rw [h_prod, h_prod_comm]
          have h_sa2 : D ((10^a - d) + 10^a * (d - 1)) = D (10^a - d) + D (d - 1) := by
            apply D_shift_add
            · omega
            · omega
          rw [h_sa2]
          have h_comp := D_complement a d hd1 hda
          rw [h_comp, ha_eq]
          have hd_le_n : d ≤ n := D_le_self n
          have hdd_le_d : D d ≤ d := D_le_self d
          have hdd_le_n : D d ≤ n := by omega
          exact Nat.add_sub_of_le hdd_le_n
        refine ⟨hk_pos, h_k_ne, h_dk, ?_⟩
        change D k ∣ n
        rw [h_sum_k]
