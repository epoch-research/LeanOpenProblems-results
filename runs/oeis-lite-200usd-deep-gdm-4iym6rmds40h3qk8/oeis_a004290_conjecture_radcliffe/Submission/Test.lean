import FormalConjectures.Util.ProblemImports

open Nat Set

lemma sInf_eq_of_mem_of_le {S : Set ℕ} {y : ℕ} (h1 : y ∈ S) (h2 : ∀ x ∈ S, y ≤ x) : sInf S = y := by
  have h_nonempty : S.Nonempty := ⟨y, h1⟩
  have h_mem := Nat.sInf_mem h_nonempty
  exact le_antisymm (Nat.sInf_le h1) (h2 (sInf S) h_mem)

lemma nine_dvd_ten_pow_minus_one (m : ℕ) : 9 ∣ 10 ^ m - 1 := by
  induction m with
  | zero =>
    simp
  | succ m ih =>
    have h_pow : 10 ^ (m + 1) - 1 = 9 * 10 ^ m + (10 ^ m - 1) := by omega
    rw [h_pow]
    exact dvd_add (dvd_mul_right 9 (10 ^ m)) ih

lemma Y_succ (m : ℕ) : (10 ^ (m + 1) - 1) / 9 = 10 * ((10 ^ m - 1) / 9) + 1 := by
  have h_dvd : 9 * ((10 ^ m - 1) / 9) = 10 ^ m - 1 := Nat.mul_div_cancel' (nine_dvd_ten_pow_minus_one m)
  have h_pow : 10 ^ (m + 1) = 10 ^ m * 10 := pow_succ 10 m
  have h_eq : 10 ^ (m + 1) - 1 = 9 * (10 * ((10 ^ m - 1) / 9) + 1) := by
    rw [h_pow]
    have h_pos : 0 < 10 ^ m := by positivity
    have h_Y : 10 ^ m ≥ 1 := h_pos
    generalize ((10 ^ m - 1) / 9) = X at h_dvd ⊢
    generalize 10 ^ m = Y at h_dvd h_Y ⊢
    omega
  have h_div : (10 ^ (m + 1) - 1) / 9 = (9 * (10 * ((10 ^ m - 1) / 9) + 1)) / 9 := by rw [h_eq]
  rw [h_div]
  exact Nat.mul_div_cancel_left (10 * ((10 ^ m - 1) / 9) + 1) (by decide)

lemma digits_rep_one (n : ℕ) : ∀ d ∈ Nat.digits 10 ((10 ^ n - 1) / 9), d = 1 := by
  induction n with
  | zero =>
    intro d hd
    have h : (10 ^ 0 - 1) / 9 = 0 := by decide
    rw [h, Nat.digits_zero] at hd
    cases hd
  | succ n ih =>
    intro d hd
    rw [Y_succ] at hd
    have h_pos : 0 < 10 * ((10 ^ n - 1) / 9) + 1 := by omega
    have h_le : 2 ≤ 10 := by decide
    have h_digits : Nat.digits 10 (10 * ((10 ^ n - 1) / 9) + 1) =
        (10 * ((10 ^ n - 1) / 9) + 1) % 10 :: Nat.digits 10 ((10 * ((10 ^ n - 1) / 9) + 1) / 10) :=
      Nat.digits_of_two_le_of_pos h_le h_pos
    have h_mod : (10 * ((10 ^ n - 1) / 9) + 1) % 10 = 1 := by omega
    have h_div : (10 * ((10 ^ n - 1) / 9) + 1) / 10 = (10 ^ n - 1) / 9 := by omega
    rw [h_mod, h_div] at h_digits
    rw [h_digits] at hd
    simp only [List.mem_cons] at hd
    cases hd with
    | inl h1 =>
      exact h1
    | inr h_rest =>
      exact ih d h_rest

lemma digits_rep_one_subset (n : ℕ) : ∀ d ∈ Nat.digits 10 ((10 ^ n - 1) / 9), d = 0 ∨ d = 1 :=
  fun d hd => Or.inr (digits_rep_one n d hd)

lemma rep_one_pos (n : ℕ) (hn : n > 0) : 0 < (10 ^ n - 1) / 9 := by
  cases n with
  | zero => omega
  | succ m =>
    have h_pow : 10 ^ (m + 1) = 10 ^ m * 10 := pow_succ 10 m
    have h_pos : 0 < 10 ^ m := by positivity
    have h_Y : 10 ^ m ≥ 1 := h_pos
    rw [h_pow]
    omega

lemma geom_sum_nine (x : ℕ) (hx : x ≥ 1) :
    (x - 1) * (x ^ 8 + x ^ 7 + x ^ 6 + x ^ 5 + x ^ 4 + x ^ 3 + x ^ 2 + x + 1) = x ^ 9 - 1 := by
  have h_ring : x * (x ^ 8 + x ^ 7 + x ^ 6 + x ^ 5 + x ^ 4 + x ^ 3 + x ^ 2 + x + 1) + 1 =
                x ^ 9 + (x ^ 8 + x ^ 7 + x ^ 6 + x ^ 5 + x ^ 4 + x ^ 3 + x ^ 2 + x + 1) := by ring
  generalize (x ^ 8 + x ^ 7 + x ^ 6 + x ^ 5 + x ^ 4 + x ^ 3 + x ^ 2 + x + 1) = S at h_ring ⊢
  have h_le : S ≤ x * S := by
    have h := Nat.mul_le_mul_right S hx
    rwa [one_mul] at h
  have h_sub : (x - 1) * S = x * S - S := by
    have h := Nat.sub_mul x 1 S
    rwa [one_mul] at h
  rw [h_sub]
  omega

lemma ten_pow_mod_nine (k : ℕ) : 10 ^ k % 9 = 1 := by
  induction k with
  | zero => decide
  | succ k ih =>
    have h_pow : 10 ^ (k + 1) = 10 ^ k * 10 := pow_succ 10 k
    rw [h_pow, Nat.mul_mod, ih]

lemma nine_dvd_geom_sum (k : ℕ) :
    9 ∣ (10 ^ k) ^ 8 + (10 ^ k) ^ 7 + (10 ^ k) ^ 6 + (10 ^ k) ^ 5 + (10 ^ k) ^ 4 + (10 ^ k) ^ 3 + (10 ^ k) ^ 2 + 10 ^ k + 1 := by
  have h_eq (j : ℕ) : (10 ^ k) ^ j = 9 * ((10 ^ k) ^ j / 9) + 1 := by
    have h1 : (10 ^ k) ^ j = 10 ^ (j * k) := by rw [mul_comm j k, ← pow_mul]
    have h2 : 10 ^ (j * k) % 9 = 1 := ten_pow_mod_nine (j * k)
    have h3 : (10 ^ k) ^ j % 9 = 1 := by rw [h1, h2]
    have h4 := Nat.div_add_mod ((10 ^ k) ^ j) 9
    rw [h3] at h4
    omega
  have h0 : 10 ^ k = (10 ^ k) ^ 1 := (pow_one _).symm
  have h_sum : (10 ^ k) ^ 8 + (10 ^ k) ^ 7 + (10 ^ k) ^ 6 + (10 ^ k) ^ 5 + (10 ^ k) ^ 4 + (10 ^ k) ^ 3 + (10 ^ k) ^ 2 + 10 ^ k + 1 =
               9 * ((10 ^ k) ^ 8 / 9 + (10 ^ k) ^ 7 / 9 + (10 ^ k) ^ 6 / 9 + (10 ^ k) ^ 5 / 9 + (10 ^ k) ^ 4 / 9 + (10 ^ k) ^ 3 / 9 + (10 ^ k) ^ 2 / 9 + 10 ^ k / 9) + 9 := by
    rw [h_eq 8, h_eq 7, h_eq 6, h_eq 5, h_eq 4, h_eq 3, h_eq 2, h0, h_eq 1]
    omega
  rw [h_sum]
  exact dvd_add (dvd_mul_right 9 _) (by decide)

lemma ten_pow_nine_minus_one (k : ℕ) : (10 ^ k - 1) ∣ ((10 ^ (9 * k) - 1) / 9) := by
  have h_pos : 0 < 10 ^ k := by positivity
  have h_x_ge1 : 10 ^ k ≥ 1 := h_pos
  have h_geom := geom_sum_nine (10 ^ k) h_x_ge1
  have h_pow9 : (10 ^ k) ^ 9 = 10 ^ (9 * k) := by rw [mul_comm 9 k, ← pow_mul]
  rw [h_pow9] at h_geom
  rcases nine_dvd_geom_sum k with ⟨M, hM⟩
  have h_eq : 10 ^ (9 * k) - 1 = 9 * ((10 ^ k - 1) * M) := by
    rw [← h_geom, hM]
    ring
  have h_div : (10 ^ (9 * k) - 1) / 9 = (9 * ((10 ^ k - 1) * M)) / 9 := by rw [h_eq]
  rw [h_div]
  rw [Nat.mul_div_cancel_left]
  · exact dvd_mul_right (10 ^ k - 1) M
  · decide

noncomputable def A004290 (n : ℕ) : ℕ :=
  let S := { m : ℕ | 0 < m ∧ n ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 }
  sInf S

lemma radcliffe_part2_y_mem (k : ℕ) (hk : k > 0) :
    ((10 ^ (9 * k) - 1) / 9) ∈ { m : ℕ | 0 < m ∧ (10 ^ k - 1) ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
  simp only [Set.mem_setOf_eq]
  refine ⟨?_, ?_, ?_⟩
  · apply rep_one_pos
    omega
  · exact ten_pow_nine_minus_one k
  · exact digits_rep_one_subset (9 * k)

lemma radcliffe_part2 (k : ℕ) : A004290 (10 ^ k - 1) = (10 ^ (9 * k) - 1) / 9 := by
  by_cases hk : k = 0
  · rw [hk]
    unfold A004290
    have h_empty : {m : ℕ | 0 < m ∧ (10 ^ 0 - 1) ∣ m ∧ ∀ d ∈ digits 10 m, d = 0 ∨ d = 1} = ∅ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      rcases h with ⟨h1, h2, _⟩
      have h2_eq : 10 ^ 0 - 1 = 0 := by decide
      rw [h2_eq] at h2
      have h_zero := Nat.eq_zero_of_zero_dvd h2
      omega
    rw [h_empty]
    simp
  · have hk_pos : k > 0 := Nat.pos_of_ne_zero hk
    unfold A004290
    apply sInf_eq_of_mem_of_le
    · exact radcliffe_part2_y_mem k hk_pos
    · intro x hx
      simp only [Set.mem_setOf_eq] at hx
      rcases hx with ⟨hx_pos, hdvd, h_digits⟩
      have h_sum_ge_nine : (Nat.digits 10 x).sum ≥ 9 * k := sorry
      have h_le := le_of_digits_sum x h_digits
      have h_mono : (10 ^ (Nat.digits 10 x).sum - 1) / 9 ≥ (10 ^ (9 * k) - 1) / 9 := by
        apply Nat.div_le_div_right
        have h1 : 10 ^ (Nat.digits 10 x).sum ≥ 10 ^ (9 * k) := Nat.pow_le_pow_right (by decide) h_sum_ge_nine
        omega
      omega



lemma le_of_digits_sum (x : ℕ) :
    (∀ d ∈ Nat.digits 10 x, d = 0 ∨ d = 1) →
    x ≥ (10 ^ (Nat.digits 10 x).sum - 1) / 9 := by
  induction x using Nat.strong_induction_on with
  | h x ih =>
    intro h_digits
    by_cases hx : x = 0
    · rw [hx]
      have h_zero : Nat.digits 10 0 = [] := Nat.digits_zero 10
      rw [h_zero]
      simp
    · have h_pos : 0 < x := Nat.pos_of_ne_zero hx
      have h_le : 2 ≤ 10 := by decide
      have h_digits_eq : Nat.digits 10 x = x % 10 :: Nat.digits 10 (x / 10) :=
        Nat.digits_of_two_le_of_pos h_le h_pos
      have h_div_lt : x / 10 < x := Nat.div_lt_self h_pos (by decide)
      have h_digits_sub : ∀ d ∈ Nat.digits 10 (x / 10), d = 0 ∨ d = 1 := by
        intro d hd
        apply h_digits d
        rw [h_digits_eq]
        exact List.mem_cons_of_mem (x % 10) hd
      have ih_div := ih (x / 10) h_div_lt h_digits_sub
      have h_sum : (Nat.digits 10 x).sum = x % 10 + (Nat.digits 10 (x / 10)).sum := by
        rw [h_digits_eq]
        exact List.sum_cons
      have h_mod_digits : x % 10 ∈ Nat.digits 10 x := by
        rw [h_digits_eq]
        simp
      have h_mod_val : x % 10 = 0 ∨ x % 10 = 1 := h_digits (x % 10) h_mod_digits
      generalize hn : x / 10 = n at ih_div h_sum h_digits_sub h_digits_eq h_mod_digits h_mod_val ⊢
      cases h_mod_val with
      | inl h0 =>
        have h_sum_eq : (Nat.digits 10 x).sum = (Nat.digits 10 n).sum := by
          rw [h_sum, h0, zero_add]
        rw [h_sum_eq]
        have h_eq_div : x = 10 * n := by
          have h_div_add := Nat.div_add_mod x 10
          omega
        rw [h_eq_div]
        have h_ge : 10 * n ≥ 10 * ((10 ^ (Nat.digits 10 n).sum - 1) / 9) := Nat.mul_le_mul_left 10 ih_div
        have h_ge2 : 10 * ((10 ^ (Nat.digits 10 n).sum - 1) / 9) ≥ (10 ^ (Nat.digits 10 n).sum - 1) / 9 := by
          have h_ten : 10 ≥ 1 := by decide
          have h_mul := Nat.mul_le_mul_right ((10 ^ (Nat.digits 10 n).sum - 1) / 9) h_ten
          rwa [one_mul] at h_mul
        omega
      | inr h1 =>
        have h_sum_eq : (Nat.digits 10 x).sum = (Nat.digits 10 n).sum + 1 := by
          rw [h_sum, h1, add_comm]
        rw [h_sum_eq]
        have h_eq_div : x = 10 * n + 1 := by
          have h_div_add := Nat.div_add_mod x 10
          omega
        rw [h_eq_div]
        have h_succ_Y : (10 ^ ((Nat.digits 10 n).sum + 1) - 1) / 9 = 10 * ((10 ^ (Nat.digits 10 n).sum - 1) / 9) + 1 := Y_succ (Nat.digits 10 n).sum
        rw [h_succ_Y]
        omega


lemma pigeonhole_helper (n : ℕ) (hn : n > 0) :
    ∃ a b : Fin (n+1), a ≠ b ∧ ((10 ^ a.val - 1) / 9) % n = ((10 ^ b.val - 1) / 9) % n := by
  have h_card : Fintype.card (Fin n) < Fintype.card (Fin (n+1)) := by simp
  let f : Fin (n+1) → Fin n := fun i => ⟨ ((10 ^ i.val - 1) / 9) % n, Nat.mod_lt _ hn ⟩
  obtain ⟨x, y, hne, hf⟩ := Fintype.exists_ne_map_eq_of_card_lt f h_card
  use x, y
  refine ⟨hne, ?_⟩
  have hf_eq : (f x).val = (f y).val := by rw [hf]
  dsimp [f] at hf_eq
  exact hf_eq

lemma test_mathlib_lemma (n : ℕ) :
    9 * (∑ i ∈ Finset.range (Nat.log 10 n).succ, n / 10 ^ i.succ) = n - (Nat.digits 10 n).sum := by
  have h := @sub_one_mul_sum_log_div_pow_eq_sub_sum_digits 10 n
  exact h


lemma dvd_sub_of_mod_eq {A B n : ℕ} (h_eq : A % n = B % n) (h_le : B ≤ A) : n ∣ A - B := by
  have h1 := Nat.div_add_mod A n
  have h2 := Nat.div_add_mod B n
  rw [h_eq] at h1
  have h3 : A - B = n * (A / n) - n * (B / n) := by omega
  have h4 : n * (A / n) - n * (B / n) = n * (A / n - B / n) := by
    rw [Nat.mul_sub_left_distrib]
  rw [h3, h4]
  exact dvd_mul_right n (A / n - B / n)


lemma Nat.dvd_of_dvd_add_left {a b c : ℕ} (h1 : a ∣ a * b + c) : a ∣ c := by
  rcases h1 with ⟨q, hq⟩
  by_cases h_ge : q ≥ b
  · use q - b
    have h2 : a * (q - b) = a * q - a * b := Nat.mul_sub_left_distrib a q b
    rw [h2]
    omega
  · by_cases ha : a = 0
    · rw [ha] at hq
      simp at hq
      rw [hq]
      exact dvd_zero a
    · have ha_pos : a > 0 := Nat.pos_of_ne_zero ha
      have h2 : a * q < a * b := Nat.mul_lt_mul_of_pos_left (by omega) ha_pos
      have h3 : a * b ≤ a * q := by omega
      omega




def S (n : ℕ) : ℕ := (Nat.digits 10 n).sum

lemma S_zero : S 0 = 0 := by
  unfold S
  rw [Nat.digits_zero]
  rfl

lemma S_pos (n : ℕ) (hn : n > 0) : S n = n % 10 + S (n / 10) := by
  unfold S
  have h_le : 2 ≤ 10 := by decide
  rw [Nat.digits_of_two_le_of_pos h_le hn, List.sum_cons]

lemma S_le_self (n : ℕ) : S n ≤ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · rw [hn, S_zero]
    · have hn_pos : n > 0 := Nat.pos_of_ne_zero hn
      rw [S_pos n hn_pos]
      have h_div : n / 10 < n := Nat.div_lt_self hn_pos (by decide)
      have ih_div := ih (n / 10) h_div
      have h_div_add : n = 10 * (n / 10) + n % 10 := (Nat.div_add_mod n 10).symm
      omega


lemma S_add_le (A B : ℕ) : S (A + B) ≤ S A + S B := by
  induction h_ab : A + B using Nat.strong_induction_on generalizing A B with
  | h sum_val ih =>
    rw [← h_ab]
    by_cases hA : A = 0
    · rw [hA, zero_add, S_zero, zero_add]
    by_cases hB : B = 0
    · rw [hB, add_zero, S_zero, add_zero]
    -- Both A > 0 and B > 0
    have hA_pos : A > 0 := Nat.pos_of_ne_zero hA
    have hB_pos : B > 0 := Nat.pos_of_ne_zero hB
    have h_sum_pos : A + B > 0 := by omega
    rw [S_pos (A + B) h_sum_pos, S_pos A hA_pos, S_pos B hB_pos]
    have h_sum_div_mod : (A + B) / 10 = A / 10 + B / 10 + (A % 10 + B % 10) / 10 := by omega
    have h_sum_mod_eq : (A + B) % 10 = (A % 10 + B % 10) % 10 := by omega
    rw [h_sum_div_mod, h_sum_mod_eq]
    have h_sum_lt : A / 10 + B / 10 + (A % 10 + B % 10) / 10 < sum_val := by
      rw [← h_ab]
      have h_lt : (A + B) / 10 < A + B := Nat.div_lt_self h_sum_pos (by decide)
      rwa [h_sum_div_mod] at h_lt
    have ih1 := ih (A / 10 + B / 10 + (A % 10 + B % 10) / 10) h_sum_lt (A / 10 + B / 10) ((A % 10 + B % 10) / 10) (by rfl)
    have h_a1_b1_lt : A / 10 + B / 10 < sum_val := by
      rw [← h_ab]
      have h_lt_A : A / 10 < A := Nat.div_lt_self hA_pos (by decide)
      have h_lt_B : B / 10 < B := Nat.div_lt_self hB_pos (by decide)
      omega
    have ih2 := ih (A / 10 + B / 10) h_a1_b1_lt (A / 10) (B / 10) (by rfl)
    have h_S_sum_le : S (A / 10 + B / 10 + (A % 10 + B % 10) / 10) ≤ S (A / 10) + S (B / 10) + S ((A % 10 + B % 10) / 10) := by omega
    have h_S_ab0 : S (A % 10 + B % 10) = (A % 10 + B % 10) % 10 + S ((A % 10 + B % 10) / 10) := by
      by_cases hab0 : A % 10 + B % 10 = 0
      · rw [hab0, S_zero]
      · have hab0_pos : A % 10 + B % 10 > 0 := Nat.pos_of_ne_zero hab0
        exact S_pos (A % 10 + B % 10) hab0_pos
    have h_le_ab0 := S_le_self (A % 10 + B % 10)
    have h_goal_le : (A % 10 + B % 10) % 10 + S (A / 10 + B / 10 + (A % 10 + B % 10) / 10) ≤ S (A / 10) + S (B / 10) + S (A % 10 + B % 10) := by
      rw [h_S_ab0]
      omega
    omega




lemma S_ten_pow_minus_one (k : ℕ) : S (10 ^ k - 1) = 9 * k := by
  induction k with
  | zero =>
    have h_zero : 10 ^ 0 - 1 = 0 := by decide
    rw [h_zero, S_zero]
  | succ k ih =>
    have h_pow_succ : 10 ^ (k + 1) = 10 * 10 ^ k := by ring
    have h_pow_pos' : 10 ^ k > 0 := by positivity
    have h_pow_pos : 10 ^ k ≥ 1 := by omega
    have h_pow : 10 ^ (k + 1) - 1 = 10 * (10 ^ k - 1) + 9 := by
      rw [h_pow_succ]
      omega
    rw [h_pow]
    have h_pos : 10 * (10 ^ k - 1) + 9 > 0 := by omega
    rw [S_pos (10 * (10 ^ k - 1) + 9) h_pos]
    have h_mod : (10 * (10 ^ k - 1) + 9) % 10 = 9 := by omega
    have h_div : (10 * (10 ^ k - 1) + 9) / 10 = 10 ^ k - 1 := by omega
    rw [h_mod, h_div, ih]

lemma S_shift_add (k : ℕ) (A B : ℕ) (hB : B < 10 ^ k) : S (10 ^ k * A + B) = S A + S B := by
  induction k generalizing B with
  | zero =>
    have hB0 : B = 0 := by omega
    rw [hB0, S_zero, add_zero]
    have h_pow0 : 10 ^ 0 = 1 := rfl
    rw [h_pow0, one_mul]
  | succ k ih =>
    have h_pow_succ : 10 ^ (k + 1) = 10 ^ k * 10 := by ring
    have h_pow_succ' : 10 ^ (k + 1) = 10 * 10 ^ k := by ring
    have h_eq : 10 ^ (k + 1) * A + B = 10 * (10 ^ k * A + B / 10) + B % 10 := by
      rw [h_pow_succ']
      omega
    have h_pos : 10 * (10 ^ k * A + B / 10) + B % 10 > 0 := by omega
    rw [h_eq, S_pos _ h_pos]
    have h_mod : (10 * (10 ^ k * A + B / 10) + B % 10) % 10 = B % 10 := by omega
    have h_div : (10 * (10 ^ k * A + B / 10) + B % 10) / 10 = 10 ^ k * A + B / 10 := by omega
    rw [h_mod, h_div]
    have hB1 : B / 10 < 10 ^ k := by
      rw [h_pow_succ] at hB
      exact Nat.div_lt_of_lt_mul hB
    rw [ih (B / 10) hB1]
    have h_SB : S B = B % 10 + S (B / 10) := by
      by_cases hB0 : B = 0
      · rw [hB0, S_zero]
        rfl
      · exact S_pos B (Nat.pos_of_ne_zero hB0)
    rw [h_SB]
    omega

    omega


lemma not_coprime_ten {n : ℕ} (h : ¬ Nat.Coprime n 10) : 2 ∣ n ∨ 5 ∣ n := by
  have h_gcd_dvd : Nat.gcd n 10 ∣ n := Nat.gcd_dvd_left n 10
  have h_gcd_dvd_10 : Nat.gcd n 10 ∣ 10 := Nat.gcd_dvd_right n 10
  have h_gcd_ne_one : Nat.gcd n 10 ≠ 1 := h
  have h_gcd_pos : Nat.gcd n 10 > 0 := Nat.gcd_pos_of_pos_right n (by decide : 0 < 10)
  have h_gcd_le : Nat.gcd n 10 ≤ 10 := Nat.le_of_dvd (by decide) h_gcd_dvd_10
  have h_cases : Nat.gcd n 10 = 1 ∨ Nat.gcd n 10 = 2 ∨ Nat.gcd n 10 = 3 ∨ Nat.gcd n 10 = 4 ∨ Nat.gcd n 10 = 5 ∨ Nat.gcd n 10 = 6 ∨ Nat.gcd n 10 = 7 ∨ Nat.gcd n 10 = 8 ∨ Nat.gcd n 10 = 9 ∨ Nat.gcd n 10 = 10 := by omega
  rcases h_cases with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10
  · contradiction
  · left; rw [← h2]; exact h_gcd_dvd
  · have h3' : ¬ 3 ∣ 10 := by decide
    have h3_dvd : 3 ∣ 10 := by rw [← h3]; exact h_gcd_dvd_10
    exact (h3' h3_dvd).elim
  · have h4' : ¬ 4 ∣ 10 := by decide
    have h4_dvd : 4 ∣ 10 := by rw [← h4]; exact h_gcd_dvd_10
    exact (h4' h4_dvd).elim
  · right; rw [← h5]; exact h_gcd_dvd
  · have h6' : ¬ 6 ∣ 10 := by decide
    have h6_dvd : 6 ∣ 10 := by rw [← h6]; exact h_gcd_dvd_10
    exact (h6' h6_dvd).elim
  · have h7' : ¬ 7 ∣ 10 := by decide
    have h7_dvd : 7 ∣ 10 := by rw [← h7]; exact h_gcd_dvd_10
    exact (h7' h7_dvd).elim
  · have h8' : ¬ 8 ∣ 10 := by decide
    have h8_dvd : 8 ∣ 10 := by rw [← h8]; exact h_gcd_dvd_10
    exact (h8' h8_dvd).elim
  · have h9' : ¬ 9 ∣ 10 := by decide
    have h9_dvd : 9 ∣ 10 := by rw [← h9]; exact h_gcd_dvd_10
    exact (h9' h9_dvd).elim
  · left
    have h_dvd : 2 ∣ 10 := by decide
    rw [h10] at h_gcd_dvd
    exact dvd_trans h_dvd h_gcd_dvd


lemma radcliffe_coprime_reduction (n : ℕ) (hn_pos : n > 0) :
    ∃ (s : ℕ) (d : ℕ), d > 0 ∧ d * 2^s ≤ n ∧ Nat.Coprime d 10 ∧ A004290 n ≤ 10^s * A004290 d := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h_coprime : Nat.Coprime n 10
    · use 0, n
      refine ⟨hn_pos, ?_, h_coprime, ?_⟩
      · omega
      · simp
    · have h_divis : 2 ∣ n ∨ 5 ∣ n := not_coprime_ten h_coprime
      cases h_divis with
      | inl h2 =>
        rcases h2 with ⟨m, hm_eq⟩
        have hm_pos : m > 0 := by
          by_contra hc
          have : m = 0 := by omega
          subst this; rw [mul_zero] at hm_eq; omega
        have hm_lt : m < n := by rw [hm_eq]; omega
        obtain ⟨s, d, hd_pos, hd_le, hd_cop, hd_le_A⟩ := ih m hm_lt hm_pos
        use s + 1, d
        refine ⟨hd_pos, ?_, hd_cop, ?_⟩
        · rw [pow_succ, ← mul_assoc]
          have : d * 2^s * 2 ≤ m * 2 := Nat.mul_le_mul_right 2 hd_le
          rw [hm_eq]
          omega
        · have h_dvd_10 : n ∣ 10 * m := by
            rw [hm_eq]
            use 5
            ring
          have h_le_10m : A004290 n ≤ A004290 (10 * m) := by
            apply A004290_le_of_dvd hn_pos (by positivity) h_dvd_10
          have h_pow1_mul : A004290 (10 * m) ≤ 10 * A004290 m := by
            have h_eq : 10 * m = 10^1 * m := by ring
            rw [h_eq]
            exact A004290_pow_ten_mul 1 m hm_pos
          have h_trans : A004290 n ≤ 10 * A004290 m := le_trans h_le_10m h_pow1_mul
          have h_le_A' : 10 * A004290 m ≤ 10 ^ (s + 1) * A004290 d := by
            have h_alg : 10 ^ (s + 1) * A004290 d = 10 * (10 ^ s * A004290 d) := by
              rw [pow_succ']
              ring
            rw [h_alg]
            exact Nat.mul_le_mul_left 10 hd_le_A
          exact le_trans h_trans h_le_A'
      | inr h5 =>
        rcases h5 with ⟨m, hm_eq⟩
        have hm_pos : m > 0 := by
          by_contra hc
          have : m = 0 := by omega
          subst this; rw [mul_zero] at hm_eq; omega
        have hm_lt : m < n := by rw [hm_eq]; omega
        obtain ⟨s, d, hd_pos, hd_le, hd_cop, hd_le_A⟩ := ih m hm_lt hm_pos
        use s + 1, d
        refine ⟨hd_pos, ?_, hd_cop, ?_⟩
        · rw [pow_succ, ← mul_assoc]
          have : d * 2^s * 2 ≤ m * 2 := Nat.mul_le_mul_right 2 hd_le
          have : m * 2 ≤ m * 5 := Nat.mul_le_mul_left m (by decide)
          rw [hm_eq]
          omega
        · have h_dvd_10 : n ∣ 10 * m := by
            rw [hm_eq]
            use 2
            ring
          have h_le_10m : A004290 n ≤ A004290 (10 * m) := by
            apply A004290_le_of_dvd hn_pos (by positivity) h_dvd_10
          have h_pow1_mul : A004290 (10 * m) ≤ 10 * A004290 m := by
            have h_eq : 10 * m = 10^1 * m := by ring
            rw [h_eq]
            exact A004290_pow_ten_mul 1 m hm_pos
          have h_trans : A004290 n ≤ 10 * A004290 m := le_trans h_le_10m h_pow1_mul
          have h_le_A' : 10 * A004290 m ≤ 10 ^ (s + 1) * A004290 d := by
            have h_alg : 10 ^ (s + 1) * A004290 d = 10 * (10 ^ s * A004290 d) := by
              rw [pow_succ']
              ring
            rw [h_alg]
            exact Nat.mul_le_mul_left 10 hd_le_A
          exact le_trans h_trans h_le_A'
