import FormalConjectures.Util.ProblemImports

open Nat Set

-- We copy the needed theorems from Spec.lean for testing
theorem test_digits_pow (k : ℕ) : Nat.digits 10 (10 ^ k) = List.replicate k 0 ++ [1] := by
  have h1 : 10 ^ k = 10 ^ k * 1 := by rw [mul_one]
  rw [h1]
  have h_base : 1 < 10 := by decide
  have h_m : 0 < 1 := by decide
  rw [Nat.digits_base_pow_mul h_base h_m]
  have h_one : Nat.digits 10 1 = [1] := by
    apply Nat.digits_of_lt 10 1
    · decide
    · decide
  rw [h_one]

theorem part1_digits (k : ℕ) : ∀ d ∈ Nat.digits 10 (10 ^ k), d = 0 ∨ d = 1 := by
  intro d hd
  rw [test_digits_pow] at hd
  rw [List.mem_append] at hd
  rcases hd with h_rep | h_sing
  · left
    exact List.eq_of_mem_replicate h_rep
  · right
    exact List.mem_singleton.mp h_sing

theorem ofDigits_replicate_one (L : ℕ) : 9 * ofDigits 10 (List.replicate L 1) = 10 ^ L - 1 := by
  induction L with
  | zero =>
    rfl
  | succ L ih =>
    rw [List.replicate_succ, ofDigits_cons]
    have h_pos' : 0 < 10 ^ L := by positivity
    have h_pos : 1 ≤ 10 ^ L := h_pos'
    omega

theorem ofDigits_replicate_one_eq (L : ℕ) : ofDigits 10 (List.replicate L 1) = (10 ^ L - 1) / 9 := by
  have h9 : 9 * ofDigits 10 (List.replicate L 1) = 10 ^ L - 1 := ofDigits_replicate_one L
  have h_div : (9 * ofDigits 10 (List.replicate L 1)) / 9 = ofDigits 10 (List.replicate L 1) := by
    apply Nat.mul_div_cancel_left
    decide
  rw [h9] at h_div
  exact h_div.symm

theorem digits_replicate_one_eq (L : ℕ) : Nat.digits 10 ((10 ^ L - 1) / 9) = List.replicate L 1 := by
  have h_base : 1 < 10 := by decide
  have h_eq : (10 ^ L - 1) / 9 = ofDigits 10 (List.replicate L 1) := (ofDigits_replicate_one_eq L).symm
  rw [h_eq]
  apply Nat.digits_ofDigits 10 h_base
  · intro l hl
    have hl_eq : l = 1 := List.eq_of_mem_replicate hl
    omega
  · intro h_nil
    have h_mem : (List.replicate L 1).getLast h_nil ∈ List.replicate L 1 := List.getLast_mem h_nil
    have h_last : (List.replicate L 1).getLast h_nil = 1 := List.eq_of_mem_replicate h_mem
    rw [h_last]
    decide

theorem test_ring_nat (X : ℕ) (hX : 1 ≤ X) : (X - 1) * (X^8 + X^7 + X^6 + X^5 + X^4 + X^3 + X^2 + X + 1) = X^9 - 1 := by
  apply Int.ofNat_inj.mp
  have h_sub : ((X - 1 : ℕ) : ℤ) = (X : ℤ) - 1 := Nat.cast_sub hX
  have h_sub9 : ((X^9 - 1 : ℕ) : ℤ) = (X : ℤ)^9 - 1 := by
    have hX_pos' : 0 < X := by omega
    have h_pow_pos : 0 < X^9 := by positivity
    have hX9 : 1 ≤ X^9 := h_pow_pos
    exact Nat.cast_sub hX9
  push_cast
  rw [h_sub, h_sub9]
  ring

theorem pow_ten_zmod_nine (k : ℕ) : ((10 ^ k : ℕ) : ZMod 9) = 1 := by
  push_cast
  have h10 : (10 : ZMod 9) = 1 := by decide
  rw [h10, one_pow]

theorem Y_mod_nine (X : ℕ) (hX : (X : ZMod 9) = 1) : ((X^8 + X^7 + X^6 + X^5 + X^4 + X^3 + X^2 + X + 1 : ℕ) : ZMod 9) = 0 := by
  push_cast
  rw [hX]
  decide

theorem Y_dvd_nine (X : ℕ) (hX : (X : ZMod 9) = 1) : 9 ∣ (X^8 + X^7 + X^6 + X^5 + X^4 + X^3 + X^2 + X + 1) := by
  have h0 : ((X^8 + X^7 + X^6 + X^5 + X^4 + X^3 + X^2 + X + 1 : ℕ) : ZMod 9) = 0 := Y_mod_nine X hX
  rwa [CharP.cast_eq_zero_iff (ZMod 9) 9] at h0

theorem part2_divisibility (k : ℕ) : (10 ^ k - 1) ∣ (10 ^ (9 * k) - 1) / 9 := by
  have h_X' : 0 < 10 ^ k := by positivity
  have h_X : 10 ^ k ≥ 1 := h_X'
  have h_id : (10 ^ k - 1) * ((10^k)^8 + (10^k)^7 + (10^k)^6 + (10^k)^5 + (10^k)^4 + (10^k)^3 + (10^k)^2 + (10^k) + 1) = 10 ^ (9 * k) - 1 := by
    have h_pow : (10^k)^9 = 10^(9*k) := by ring
    rw [← h_pow]
    exact test_ring_nat (10^k) h_X
  have h_dvd : 9 ∣ ((10^k)^8 + (10^k)^7 + (10^k)^6 + (10^k)^5 + (10^k)^4 + (10^k)^3 + (10^k)^2 + (10^k) + 1) := by
    exact Y_dvd_nine (10^k) (pow_ten_zmod_nine k)
  rcases h_dvd with ⟨Q, hQ⟩
  rw [hQ] at h_id
  have h_id2 : 9 * ((10 ^ k - 1) * Q) = 10 ^ (9 * k) - 1 := by
    rw [← h_id]
    ring
  have h_id3 : ((10 ^ k - 1) * Q) = (10 ^ (9 * k) - 1) / 9 := by
    have h_div : (9 * ((10 ^ k - 1) * Q)) / 9 = (10 ^ (9 * k) - 1) / 9 := by rw [h_id2]
    rwa [Nat.mul_div_cancel_left] at h_div
    decide
  use Q
  exact h_id3.symm

theorem part2_mem (k : ℕ) (hk : k > 0) :
  (10 ^ (9 * k) - 1) / 9 ∈ { m : ℕ | 0 < m ∧ (10 ^ k - 1) ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
  refine ⟨?_, part2_divisibility k, ?_⟩
  · have h_9k : 9 * k > 0 := by omega
    have h_pow : 10 ≤ 10 ^ (9 * k) := by
      have : 10 ^ 1 ≤ 10 ^ (9 * k) := Nat.pow_le_pow_right (n := 10) (by decide) h_9k
      exact this
    have h_sub : 9 ≤ 10 ^ (9 * k) - 1 := by omega
    exact Nat.div_pos h_sub (by decide)
  · intro d hd
    rw [digits_replicate_one_eq (9 * k)] at hd
    have hd_eq : d = 1 := List.eq_of_mem_replicate hd
    right
    exact hd_eq


theorem ofDigits_ge (l : List ℕ) (hl : ∀ d ∈ l, d = 0 ∨ d = 1) :
  ∀ L, l.sum ≥ L → ofDigits 10 l ≥ ofDigits 10 (List.replicate L 1) := by
  induction l with
  | nil =>
    intro L hsum
    rw [List.sum_nil] at hsum
    have hL : L = 0 := by omega
    subst hL
    rfl
  | cons d t ih =>
    intro L hsum
    rw [List.sum_cons] at hsum
    have hd_mem : d ∈ d :: t := List.mem_cons_self
    have hd_val : d = 0 ∨ d = 1 := hl d hd_mem
    have ht_val : ∀ x ∈ t, x = 0 ∨ x = 1 := by
      intro x hx
      exact hl x (List.mem_cons_of_mem d hx)
    rcases hd_val with rfl | rfl
    · -- d = 0
      rw [ofDigits_cons, zero_add]
      have ht_sum : t.sum ≥ L := by omega
      have ih_t := ih ht_val L ht_sum
      omega
    · -- d = 1
      rw [ofDigits_cons]
      rcases L with _ | L'
      · change 1 + 10 * ofDigits 10 t ≥ 0
        omega
      · rw [List.replicate_succ, ofDigits_cons]
        have ht_sum : t.sum ≥ L' := by omega
        have ih_t := ih ht_val L' ht_sum
        omega


theorem sum_le_of_ofDigits_le (M : ℕ) (X : ℕ) (hXM : X > M) (t : List ℕ) (ht : ∀ x ∈ t, x ≤ M) :
  ∀ L', ofDigits X t ≤ ofDigits X (List.replicate L' M) → t.sum ≤ L' * M := by
  induction t with
  | nil =>
    intro L' h
    rw [List.sum_nil]
    omega
  | cons c s ih =>
    intro L' h
    rw [List.sum_cons]
    have hc_mem : c ∈ c :: s := List.mem_cons_self
    have hc_le : c ≤ M := ht c hc_mem
    have hs_val : ∀ x ∈ s, x ≤ M := by
      intro x hx
      exact ht x (List.mem_cons_of_mem c hx)
    rcases L' with _ | L''
    · -- L' = 0
      rw [ofDigits_cons] at h
      change c + X * ofDigits X s ≤ 0 at h
      have hc_eq : c = 0 := by omega
      have h_mul : X * ofDigits X s = 0 := by omega
      have hX_ne : X ≠ 0 := by omega
      have hs_eq : ofDigits X s = 0 := by
        cases Nat.mul_eq_zero.mp h_mul with
        | inl h1 => contradiction
        | inr h2 => exact h2
      have h_le : ofDigits X s ≤ ofDigits X (List.replicate 0 M) := by
        rw [hs_eq]
        rfl
      have ih_s := ih hs_val 0 h_le
      omega
    · -- L' = L'' + 1
      rw [List.replicate_succ, ofDigits_cons] at h
      rw [ofDigits_cons] at h
      have hs_le : ofDigits X s ≤ ofDigits X (List.replicate L'' M) := by
        by_contra h_gt
        push_neg at h_gt
        have hs_ge : ofDigits X s ≥ ofDigits X (List.replicate L'' M) + 1 := h_gt
        have h_lhs : c + X * ofDigits X s ≥ X * (ofDigits X (List.replicate L'' M) + 1) := by
          calc c + X * ofDigits X s
            _ ≥ X * ofDigits X s := by omega
            _ ≥ X * (ofDigits X (List.replicate L'' M) + 1) := Nat.mul_le_mul_left X hs_ge
        have h_distrib : X * (ofDigits X (List.replicate L'' M) + 1) = X * ofDigits X (List.replicate L'' M) + X := by ring
        rw [h_distrib] at h_lhs
        omega
      have ih_s := ih hs_val L'' hs_le
      have h_mul_distrib : (L'' + 1) * M = L'' * M + M := by ring
      rw [h_mul_distrib]
      omega

theorem ofDigits_replicate_zero_general (X : ℕ) (L : ℕ) : ofDigits X (List.replicate L 0) = 0 := by
  induction L with
  | zero => rfl
  | succ L' ih =>
    rw [List.replicate_succ, ofDigits_cons, ih, mul_zero, add_zero]

theorem ofDigits_ge_general (X : ℕ) (hX : X ≥ 1) (M : ℕ) (b : List ℕ) (hb : ∀ x ∈ b, x ≤ M) (L : ℕ) (hsum : b.sum ≥ L * M) (hXM : X > M) :
  ofDigits X b ≥ ofDigits X (List.replicate L M) := by
  induction b generalizing L with
  | nil =>
    have h_sum : 0 ≥ L * M := hsum
    rcases L with _ | L'
    · rfl
    · rw [succ_mul] at h_sum
      have : L' * M + M = 0 := by omega
      have hM : M = 0 := by omega
      subst hM
      rw [ofDigits_replicate_zero_general X (L' + 1)]
      rfl
  | cons d t ih =>
    have hd_mem : d ∈ d :: t := List.mem_cons_self
    have hd_val : d ≤ M := hb d hd_mem
    have ht_val : ∀ x ∈ t, x ≤ M := by
      intro x hx
      exact hb x (List.mem_cons_of_mem d hx)
    rcases L with _ | L'
    · change ofDigits X (d :: t) ≥ 0
      omega
    · rw [List.replicate_succ, ofDigits_cons]
      rw [ofDigits_cons]
      rw [List.sum_cons] at hsum
      rw [succ_mul] at hsum
      have ht_sum : t.sum ≥ L' * M := by omega
      have ih_t := ih ht_val L' ht_sum
      by_cases h_eq : ofDigits X t = ofDigits X (List.replicate L' M)
      · have h_le_eq : ofDigits X t ≤ ofDigits X (List.replicate L' M) := by omega
        have ht_sum_le : t.sum ≤ L' * M := sum_le_of_ofDigits_le M X hXM t ht_val L' h_le_eq
        have hd_ge : d ≥ M := by omega
        have hd_eq : d = M := by omega
        rw [hd_eq, h_eq]
      · have h_gt : ofDigits X t > ofDigits X (List.replicate L' M) := by omega
        have h_ge_succ : ofDigits X t ≥ ofDigits X (List.replicate L' M) + 1 := h_gt
        have h_lhs : d + X * ofDigits X t ≥ d + X * (ofDigits X (List.replicate L' M) + 1) := by
          have : X * ofDigits X t ≥ X * (ofDigits X (List.replicate L' M) + 1) := Nat.mul_le_mul_left X h_ge_succ
          omega
        have h_distrib : d + X * (ofDigits X (List.replicate L' M) + 1) = d + X * ofDigits X (List.replicate L' M) + X := by ring
        rw [h_distrib] at h_lhs
        omega


theorem ofDigits_replicate_mul (X : ℕ) (M : ℕ) (L : ℕ) :
  ofDigits X (List.replicate L M) = M * ofDigits X (List.replicate L 1) := by
  induction L with
  | zero => rfl
  | succ L' ih =>
    rw [List.replicate_succ, ofDigits_cons, List.replicate_succ, ofDigits_cons]
    rw [ih]
    ring


theorem ofDigits_replicate_one_general (X : ℕ) (hX : X ≥ 1) (L : ℕ) :
  (X - 1) * ofDigits X (List.replicate L 1) = X ^ L - 1 := by
  induction L with
  | zero => rfl
  | succ L' ih =>
    rw [List.replicate_succ, ofDigits_cons]
    have h_mul : (X - 1) * (1 + X * ofDigits X (List.replicate L' 1)) = (X - 1) + X * ((X - 1) * ofDigits X (List.replicate L' 1)) := by
      ring
    rw [h_mul, ih, pow_succ, mul_comm (X ^ L') X]
    have h_pow_pos : 0 < X ^ L' := by positivity
    have h_pow_pos' : 1 ≤ X ^ L' := h_pow_pos
    have h_dist : X * (X ^ L' - 1) = X * X ^ L' - X := by
      rw [Nat.mul_sub_left_distrib, mul_one]
    rw [h_dist]
    have h_ge : X * X ^ L' ≥ X := by
      calc X * X ^ L'
        _ ≥ X * 1 := Nat.mul_le_mul_left X h_pow_pos'
        _ = X := by ring
    omega


theorem ofDigits_replicate_nine_eq (k : ℕ) (hk : k > 0) :
  ofDigits (10^k) (List.replicate 9 ((10^k - 1) / 9)) = (10 ^ (9 * k) - 1) / 9 := by
  have hX : 10 ^ k ≥ 1 := by
    have : 10 ^ k > 0 := by positivity
    omega
  have h_id := ofDigits_replicate_one_general (10^k) hX 9
  have h_pow : (10^k)^9 = 10^(9*k) := by ring
  rw [h_pow] at h_id
  have h_mul := ofDigits_replicate_mul (10^k) ((10^k - 1) / 9) 9
  have h_9mul : 9 * ((10^k - 1) / 9) = 10^k - 1 := by
    have h_dvd : 9 ∣ 10^k - 1 := by
      have h0 : (((10^k - 1 : ℕ) : ZMod 9)) = 0 := by
        rw [Nat.cast_sub hX]
        rw [pow_ten_zmod_nine k]
        rfl
      rwa [CharP.cast_eq_zero_iff (ZMod 9) 9] at h0
    exact Nat.mul_div_cancel' h_dvd
  have h_eq : 9 * ofDigits (10^k) (List.replicate 9 ((10^k - 1) / 9)) = 10 ^ (9 * k) - 1 := by
    calc 9 * ofDigits (10^k) (List.replicate 9 ((10^k - 1) / 9))
      _ = 9 * (((10^k - 1) / 9) * ofDigits (10^k) (List.replicate 9 1)) := by rw [h_mul]
      _ = (9 * ((10^k - 1) / 9)) * ofDigits (10^k) (List.replicate 9 1) := by ring
      _ = (10^k - 1) * ofDigits (10^k) (List.replicate 9 1) := by rw [h_9mul]
      _ = 10 ^ (9 * k) - 1 := h_id
  have h_div : (9 * ofDigits (10^k) (List.replicate 9 ((10^k - 1) / 9))) / 9 = (10 ^ (9 * k) - 1) / 9 := by
    rw [h_eq]
  rwa [Nat.mul_div_cancel_left] at h_div
  decide


theorem digits_len_le (x : ℕ) (k : ℕ) (hx : x < 10^k) : (Nat.digits 10 x).length ≤ k := by
  have h_base : 1 < 10 := by decide
  rwa [Nat.digits_length_le_iff h_base]


theorem ofDigits_le_replicate_one (l : List ℕ) (hl : ∀ d ∈ l, d ≤ 1) (k : ℕ) (hk : l.length ≤ k) :
  ofDigits 10 l ≤ ofDigits 10 (List.replicate k 1) := by
  induction l generalizing k with
  | nil =>
    change 0 ≤ ofDigits 10 (List.replicate k 1)
    omega
  | cons d t ih =>
    rcases k with _ | k'
    · rw [List.length_cons] at hk
      omega
    · rw [List.replicate_succ, ofDigits_cons, ofDigits_cons]
      have hd_mem : d ∈ d :: t := List.mem_cons_self
      have hd_le : d ≤ 1 := hl d hd_mem
      have ht_val : ∀ x ∈ t, x ≤ 1 := by
        intro x hx
        exact hl x (List.mem_cons_of_mem d hx)
      have ht_len : t.length ≤ k' := by
        rw [List.length_cons] at hk
        omega
      have ih_t := ih ht_val k' ht_len
      omega


theorem le_replicate_one (x : ℕ) (k : ℕ) (hx : x < 10^k) (h_01 : ∀ d ∈ Nat.digits 10 x, d = 0 ∨ d = 1) :
  x ≤ (10^k - 1) / 9 := by
  have h_eq : x = ofDigits 10 (Nat.digits 10 x) := (Nat.ofDigits_digits 10 x).symm
  rw [h_eq]
  rw [← ofDigits_replicate_one_eq k]
  have h_le : ∀ d ∈ Nat.digits 10 x, d ≤ 1 := by
    intro d hd
    rcases h_01 d hd with rfl | rfl <;> omega
  have h_len := digits_len_le x k hx
  exact ofDigits_le_replicate_one (Nat.digits 10 x) h_le k h_len


theorem ofDigits_modEq (X : ℕ) (hX : X ≥ 2) (b : List ℕ) :
  ofDigits X b ≡ b.sum [MOD X - 1] := by
  induction b with
  | nil => rfl
  | cons d t ih =>
    rw [ofDigits_cons, List.sum_cons]
    have h1 : X ≡ 1 [MOD X - 1] := by
      have h_dvd : ((X - 1 : ℕ) : ℤ) ∣ (1 : ℤ) - (X : ℤ) := by
        have h_sub : ((X - 1 : ℕ) : ℤ) = (X : ℤ) - 1 := Nat.cast_sub (by omega)
        rw [h_sub]
        have h_eq : (1 : ℤ) - (X : ℤ) = -((X : ℤ) - 1) := by ring
        rw [h_eq]
        exact dvd_neg.mpr (dvd_refl _)
      exact Nat.modEq_iff_dvd.mpr h_dvd
    have h2 : X * ofDigits X t ≡ 1 * ofDigits X t [MOD X - 1] := Nat.ModEq.mul h1 (Nat.ModEq.refl _)
    rw [one_mul] at h2
    have h3 : d + X * ofDigits X t ≡ d + ofDigits X t [MOD X - 1] := Nat.ModEq.add (Nat.ModEq.refl d) h2
    exact Nat.ModEq.trans h3 (Nat.ModEq.add (Nat.ModEq.refl d) ih)


theorem sum_pos_of_ofDigits_pos (X : ℕ) (b : List ℕ) (h : ofDigits X b > 0) : b.sum > 0 := by
  by_contra hc
  have h_sum : b.sum = 0 := by omega
  have hb_eq_zero : ∀ (l : List ℕ), l.sum = 0 → ofDigits X l = 0 := by
    intro l
    induction l with
    | nil => intro _; rfl
    | cons d t ih =>
      intro h_sum'
      rw [List.sum_cons] at h_sum'
      have hd : d = 0 := by omega
      have ht : t.sum = 0 := by omega
      rw [ofDigits_cons, hd, ih ht, mul_zero, add_zero]
  have h_of_zero : ofDigits X b = 0 := hb_eq_zero b h_sum
  omega




theorem modEq_mul_left_mod (a b n c : ℕ) (h : a ≡ b [MOD n]) : c * a ≡ c * b [MOD c * n] := by
  change c * a % (c * n) = c * b % (c * n)
  rw [Nat.mul_mod_mul_left, Nat.mul_mod_mul_left]
  congr 1

theorem digits_div_base (y : ℕ) : Nat.digits 10 (y / 10) = (Nat.digits 10 y).drop 1 := by
  have h_base : 1 < 10 := by decide
  rcases y with _ | y'
  · rw [Nat.digits_zero, List.drop_nil]
  · have hy : y' + 1 > 0 := by omega
    rw [Nat.digits_def' h_base hy]
    rfl

theorem test_digits_div_pow (m s : ℕ) : Nat.digits 10 (m / 10^s) = (Nat.digits 10 m).drop s := by
  induction s with
  | zero =>
    rw [pow_zero, Nat.div_one, List.drop_zero]
  | succ s' ih =>
    have h_pow : 10 ^ (s' + 1) = 10 ^ s' * 10 := by ring
    rw [h_pow, ← Nat.div_div_eq_div_mul]
    rw [digits_div_base]
    rw [ih]
    rw [List.drop_drop, add_comm]

theorem ofDigits_take_eq_mod (y : ℕ) (k : ℕ) :
  ofDigits 10 ((Nat.digits 10 y).take k) = y % 10 ^ k := by
  induction k generalizing y with
  | zero =>
    rw [pow_zero, Nat.mod_one, List.take_zero, ofDigits_nil]
  | succ k' ih =>
    by_cases hy : y = 0
    · subst hy
      rw [Nat.digits_zero, List.take_nil, ofDigits_nil, zero_mod]
    · have h_base : 1 < 10 := by decide
      rw [Nat.digits_def' h_base (Nat.pos_of_ne_zero hy), List.take_succ_cons, ofDigits_cons, ih]
      have h_mod_pow : (y % 10 + 10 * (y / 10 % 10 ^ k')) % 10 ^ (k' + 1) = y % 10 + 10 * (y / 10 % 10 ^ k') := by
        have h_pow : 10 ^ (k' + 1) = 10 * 10 ^ k' := by ring
        rw [h_pow]
        apply Nat.mod_eq_of_lt
        have h_lt' : y / 10 % 10 ^ k' < 10 ^ k' := Nat.mod_lt (y / 10) (by positivity)
        have h_mod10 : y % 10 < 10 := Nat.mod_lt y (by decide)
        omega
      rw [← h_mod_pow]
      have h_div2 : y = y % 10 + 10 * (y / 10) := by omega
      nth_rw 3 [h_div2]
      have h_me' : y / 10 % 10 ^ k' ≡ y / 10 [MOD 10 ^ k'] := by
        change (y / 10 % 10 ^ k') % 10 ^ k' = (y / 10) % 10 ^ k'
        rw [Nat.mod_mod]
      have h_mul : 10 * (y / 10 % 10 ^ k') ≡ 10 * (y / 10) [MOD 10 * 10 ^ k'] := modEq_mul_left_mod _ _ _ 10 h_me'
      have h_add : y % 10 + 10 * (y / 10 % 10 ^ k') ≡ y % 10 + 10 * (y / 10) [MOD 10 * 10 ^ k'] := Nat.ModEq.add (Nat.ModEq.refl _) h_mul
      have h_pow2 : 10 ^ (k' + 1) = 10 * 10 ^ k' := by ring
      rw [← h_pow2] at h_add
      exact h_add


theorem mod_le_replicate_one (y : ℕ) (k : ℕ) (h_01 : ∀ d ∈ Nat.digits 10 y, d = 0 ∨ d = 1) :
  y % 10 ^ k ≤ (10 ^ k - 1) / 9 := by
  rw [← ofDigits_take_eq_mod]
  rw [← ofDigits_replicate_one_eq k]
  have h_le : ∀ d ∈ (Nat.digits 10 y).take k, d ≤ 1 := by
    intro d hd
    have hd_mem : d ∈ Nat.digits 10 y := List.mem_of_mem_take hd
    rcases h_01 d hd_mem with rfl | rfl <;> omega
  have h_len : ((Nat.digits 10 y).take k).length ≤ k := List.length_take_le k (Nat.digits 10 y)
  exact ofDigits_le_replicate_one ((Nat.digits 10 y).take k) h_le k h_len


theorem digits_member_eq_div_mod (B : ℕ) (hB : B ≥ 2) (y : ℕ) (x : ℕ) (hx : x ∈ Nat.digits B y) :
  ∃ i : ℕ, x = (y / B ^ i) % B := by
  induction y using Nat.strong_induction_on generalizing x with
  | h y' ih =>
    by_cases hy0 : y' = 0
    · subst hy0
      rw [Nat.digits_zero] at hx
      cases hx
    · have hy : y' > 0 := by omega
      rw [Nat.digits_def' hB hy] at hx
      cases hx with
      | head =>
        use 0
        rw [pow_zero, Nat.div_one]
      | tail _ h_mem =>
        have h_div_lt : y' / B < y' := Nat.div_lt_self hy hB
        have ih_x := ih (y' / B) h_div_lt x h_mem
        rcases ih_x with ⟨j, hj⟩
        use j + 1
        rw [hj]
        have h_pow : B ^ (j + 1) = B * B ^ j := by
          rw [pow_succ', mul_comm]
        rw [h_pow, Nat.div_div_eq_div_mul]


theorem digits_pow_ten_le_replicate_one (y : ℕ) (k : ℕ) (hk : k > 0) (h_01 : ∀ d ∈ Nat.digits 10 y, d = 0 ∨ d = 1) (x : ℕ) (hx : x ∈ Nat.digits (10^k) y) :
  x ≤ (10^k - 1) / 9 := by
  have hB : 10 ^ k ≥ 2 := by
    have : 10 ^ 1 ≤ 10 ^ k := Nat.pow_le_pow_right (by decide) hk
    omega
  have h_eq' := digits_member_eq_div_mod (10^k) hB y x hx
  rcases h_eq' with ⟨i, rfl⟩
  have h_pow : (10^k)^i = 10^(k*i) := by ring
  have h_div : y / (10^k)^i = y / 10^(k*i) := by rw [h_pow]
  rw [h_div]
  apply mod_le_replicate_one
  intro d hd
  rw [test_digits_div_pow] at hd
  have hd_mem : d ∈ Nat.digits 10 y := List.mem_of_mem_drop hd
  exact h_01 d hd_mem


theorem part2_lower_bound (k : ℕ) (hk : k > 0) (m : ℕ)
  (h_mem : m ∈ { m : ℕ | 0 < m ∧ (10 ^ k - 1) ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 }) :
  (10 ^ (9 * k) - 1) / 9 ≤ m := by
  have hpos : 0 < m := h_mem.1
  have hdvd : (10 ^ k - 1) ∣ m := h_mem.2.1
  have h_01 : ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 := h_mem.2.2
  have hB : 10 ^ k ≥ 2 := by
    have : 10 ^ 1 ≤ 10 ^ k := Nat.pow_le_pow_right (by decide) hk
    omega
  let b := Nat.digits (10 ^ k) m
  have h_eq : m = ofDigits (10 ^ k) b := (Nat.ofDigits_digits (10 ^ k) m).symm
  have hb_le : ∀ x ∈ b, x ≤ (10 ^ k - 1) / 9 := by
    intro x hx
    exact digits_pow_ten_le_replicate_one m k hk h_01 x hx
  have h_modeq : m ≡ b.sum [MOD 10 ^ k - 1] := by
    rw [h_eq]
    exact ofDigits_modEq (10 ^ k) hB b
  have h_mod0 : m ≡ 0 [MOD 10 ^ k - 1] := Nat.modEq_zero_iff_dvd.mpr hdvd
  have h_sum_mod0 : b.sum ≡ 0 [MOD 10 ^ k - 1] := Nat.ModEq.trans h_modeq.symm h_mod0
  have h_sum_pos : b.sum > 0 := by
    apply sum_pos_of_ofDigits_pos (10 ^ k) b
    omega
  have h_sum_ge : b.sum ≥ 10 ^ k - 1 := by
    have hdvd_sum : (10 ^ k - 1) ∣ b.sum := Nat.modEq_zero_iff_dvd.mp h_sum_mod0
    exact Nat.le_of_dvd h_sum_pos hdvd_sum
  have h_div_lt : (10^k - 1) / 9 < 10^k := by
    apply Nat.div_lt_of_lt_mul
    have : 10^k - 1 < 9 * 10^k := by
      calc 10^k - 1
        _ < 10^k := by omega
        _ ≤ 9 * 10^k := by omega
    exact this
  have h_9mul : 9 * ((10^k - 1) / 9) = 10^k - 1 := by
    have h_dvd : 9 ∣ 10^k - 1 := by
      have h10 : ((10^k : ℕ) : ZMod 9) = 1 := pow_ten_zmod_nine k
      have h0 : ((10^k - 1 : ℕ) : ZMod 9) = 0 := by
        have h_pos : 10 ^ k > 0 := by positivity
        have h_ge : 10 ^ k ≥ 1 := h_pos
        rw [Nat.cast_sub h_ge]
        rw [pow_ten_zmod_nine k]
        rfl
      rwa [CharP.cast_eq_zero_iff (ZMod 9) 9] at h0
    exact Nat.mul_div_cancel' h_dvd
  have h_ge_sum : b.sum ≥ 9 * ((10 ^ k - 1) / 9) := by
    rw [h_9mul]
    exact h_sum_ge
  have h_ge := ofDigits_ge_general (10 ^ k) (by omega) ((10 ^ k - 1) / 9) b hb_le 9 h_ge_sum h_div_lt
  rw [ofDigits_replicate_nine_eq k hk] at h_ge
  rw [h_eq]
  exact h_ge


noncomputable def A004290 (n : ℕ) : ℕ :=
  let S := { m : ℕ | 0 < m ∧ n ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 }
  sInf S

theorem a004290_zero : A004290 0 = 0 := by
  unfold A004290
  have h_empty : { m : ℕ | 0 < m ∧ 0 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } = ∅ := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro h
    have : x = 0 := Nat.eq_zero_of_zero_dvd h.2.1
    omega
  rw [h_empty]
  exact Nat.sInf_empty


theorem Nat.sInf_eq {s : Set ℕ} {a : ℕ} (ha : a ∈ s) (hb : ∀ b ∈ s, a ≤ b) : sInf s = a :=
  le_antisymm (Nat.sInf_le ha) (hb (sInf s) (Nat.sInf_mem ⟨a, ha⟩))


theorem part1 (k : ℕ) (hk : k > 0) : A004290 (10 ^ k) = 10 ^ k := by
  have h_mem : 10 ^ k ∈ { m : ℕ | 0 < m ∧ 10 ^ k ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
    refine ⟨?_, dvd_refl _, part1_digits k⟩
    positivity
  apply Nat.sInf_eq h_mem
  intro b hb
  have hdvd : 10 ^ k ∣ b := hb.2.1
  have hpos : 0 < b := hb.1
  exact Nat.le_of_dvd hpos hdvd

theorem part2 (k : ℕ) (hk : k > 0) : A004290 (10 ^ k - 1) = (10 ^ (9 * k) - 1) / 9 := by
  have h_mem := part2_mem k hk
  apply Nat.sInf_eq h_mem
  intro b hb
  exact part2_lower_bound k hk b hb


theorem fin_pigeonhole {n m : ℕ} (h : n > m) (f : Fin n → Fin m) :
  ∃ i j : Fin n, i ≠ j ∧ f i = f j := by
  by_contra h_inj
  push_neg at h_inj
  have h_injective : Function.Injective f := by
    intro i j hij
    by_contra h_ne
    exact h_inj i j h_ne hij
  have h_le := Fin.le_of_injective f h_injective
  omega


theorem ofDigits_append_replicate_zero (L_zeros L_ones : ℕ) :
  ofDigits 10 (List.replicate L_zeros 0 ++ List.replicate L_ones 1) = 10 ^ L_zeros * ofDigits 10 (List.replicate L_ones 1) := by
  have h_app : ofDigits 10 (List.replicate L_zeros 0 ++ List.replicate L_ones 1) = ofDigits 10 (List.replicate L_zeros 0) + 10 ^ L_zeros * ofDigits 10 (List.replicate L_ones 1) := by
    rw [Nat.ofDigits_append, List.length_replicate]
  rw [Nat.ofDigits_replicate_zero, zero_add] at h_app
  exact h_app


theorem replicate_ne_nil {α : Type*} (n : ℕ) (x : α) (hn : n > 0) : List.replicate n x ≠ [] := by
  intro h
  have : (List.replicate n x).length = 0 := by rw [h, List.length_nil]
  rw [List.length_replicate] at this
  omega

theorem getLast_replicate_one (L : ℕ) (h_nil : List.replicate L 1 ≠ []) :
  (List.replicate L 1).getLast h_nil = 1 := List.getLast_replicate h_nil

theorem append_ne_nil_of_ne_nil {α : Type*} (l1 l2 : List α) (hl2 : l2 ≠ []) : l1 ++ l2 ≠ [] := by
  cases l1 with
  | nil =>
    rw [List.nil_append]
    exact hl2
  | cons x xs =>
    rw [List.cons_append]
    exact List.cons_ne_nil x (xs ++ l2)

theorem getLast_append_replicate_one (L_zeros L_ones : ℕ) (h_ones : L_ones > 0) (h_nil : (List.replicate L_zeros 0 ++ List.replicate L_ones 1) ≠ []) :
  (List.replicate L_zeros 0 ++ List.replicate L_ones 1).getLast h_nil = 1 := by
  have h2 : List.replicate L_ones 1 ≠ [] := replicate_ne_nil L_ones 1 h_ones
  rw [List.getLast_append_of_ne_nil h_nil h2]
  exact List.getLast_replicate h2

theorem mem_replicate_zero_append_replicate_one (L_zeros L_ones : ℕ) (d : ℕ)
  (hd : d ∈ List.replicate L_zeros 0 ++ List.replicate L_ones 1) : d = 0 ∨ d = 1 := by
  rw [List.mem_append] at hd
  rcases hd with h1 | h2
  · left
    exact List.eq_of_mem_replicate h1
  · right
    exact List.eq_of_mem_replicate h2

theorem digits_ofDigits_replicate_zero_append_replicate_one (L_zeros L_ones : ℕ) (h_ones : L_ones > 0) :
  ∀ d ∈ Nat.digits 10 (ofDigits 10 (List.replicate L_zeros 0 ++ List.replicate L_ones 1)), d = 0 ∨ d = 1 := by
  have h_base : 1 < 10 := by decide
  rw [Nat.digits_ofDigits 10 h_base (List.replicate L_zeros 0 ++ List.replicate L_ones 1)]
  · intro d hd
    exact mem_replicate_zero_append_replicate_one L_zeros L_ones d hd
  · intro d hd
    have : d = 0 ∨ d = 1 := mem_replicate_zero_append_replicate_one L_zeros L_ones d hd
    omega
  · intro h
    rw [getLast_append_replicate_one L_zeros L_ones h_ones h]
    decide

theorem dvd_of_add_mod_eq_mod (b k n : ℕ) (h : (b + k) % n = b % n) : n ∣ k := by
  have h_eq : b + k ≡ b [MOD n] := h
  have h_dvd : (n : ℤ) ∣ (b : ℤ) - ((b + k) : ℤ) := Nat.modEq_iff_dvd.mp h_eq
  have h_eq2 : (b : ℤ) - ((b + k) : ℤ) = -k := by ring
  rw [h_eq2] at h_dvd
  have h_dvd2 : (n : ℤ) ∣ (k : ℤ) := dvd_neg.mp h_dvd
  exact Int.ofNat_dvd.mp h_dvd2


theorem a004290_lt_pow_ten (n : ℕ) (hn : n > 0) : A004290 n < 10 ^ n := by
  let f (i : Fin (n + 1)) : Fin n := ⟨ofDigits 10 (List.replicate i.val 1) % n, Nat.mod_lt _ hn⟩
  have h_ph : ∃ i j : Fin (n + 1), i ≠ j ∧ f i = f j := fin_pigeonhole (by omega) f
  have h_ph' : ∃ i j : Fin (n + 1), i.val > j.val ∧ f i = f j := by
    rcases h_ph with ⟨i, j, hij, h_eq⟩
    have h_ne : i.val ≠ j.val := by
      intro h
      apply hij
      ext
      exact h
    rcases lt_or_gt_of_ne h_ne with h_lt | h_gt
    · use j, i
      refine ⟨h_lt, h_eq.symm⟩
    · use i, j
  rcases h_ph' with ⟨i, j, h_gt, h_eq⟩
  let L_zeros := j.val
  let L_ones := i.val - j.val
  have h_ones : L_ones > 0 := by omega
  let M := ofDigits 10 (List.replicate L_zeros 0 ++ List.replicate L_ones 1)
  have h_not_empty : List.replicate L_zeros 0 ++ List.replicate L_ones 1 ≠ [] :=
    append_ne_nil_of_ne_nil (List.replicate L_zeros 0) (List.replicate L_ones 1) (replicate_ne_nil L_ones 1 h_ones)
  have h_M_eq : M = 10 ^ L_zeros * ofDigits 10 (List.replicate L_ones 1) := by
    exact ofDigits_append_replicate_zero L_zeros L_ones
  have h_ones_pos : ofDigits 10 (List.replicate L_ones 1) > 0 := by
    rcases L_ones with _ | L_ones'
    · omega
    · rw [List.replicate_succ, ofDigits_cons]
      omega
  have h_M_pos : M > 0 := by
    rw [h_M_eq]
    have h10 : 10 ^ L_zeros > 0 := by positivity
    exact Nat.mul_pos h10 h_ones_pos
  have h_M_dvd : n ∣ M := by
    rw [h_M_eq]
    have h_proj : (f i).val = (f j).val := by rw [h_eq]
    have h_mod : ofDigits 10 (List.replicate i.val 1) % n = ofDigits 10 (List.replicate j.val 1) % n := h_proj
    let A := ofDigits 10 (List.replicate i.val 1)
    let B := ofDigits 10 (List.replicate j.val 1)
    let C := ofDigits 10 (List.replicate L_ones 1)
    have h_rep : List.replicate i.val 1 = List.replicate j.val 1 ++ List.replicate (i.val - j.val) 1 := by
      rw [← List.replicate_add]
      congr 1
      omega
    have h_app : ofDigits 10 (List.replicate j.val 1 ++ List.replicate (i.val - j.val) 1) = B + 10 ^ j.val * C := by
      rw [Nat.ofDigits_append, List.length_replicate]
    have h_eq2 : A = B + 10 ^ j.val * C := by
      dsimp [A]
      rw [h_rep]
      exact h_app
    have h_mod2 : (B + 10 ^ j.val * C) % n = B % n := by
      rw [← h_eq2]
      exact h_mod
    exact dvd_of_add_mod_eq_mod B (10 ^ j.val * C) n h_mod2
  have h_M_digits : ∀ d ∈ Nat.digits 10 M, d = 0 ∨ d = 1 := by
    exact digits_ofDigits_replicate_zero_append_replicate_one L_zeros L_ones h_ones
  have h_M_mem : M ∈ { m : ℕ | 0 < m ∧ n ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := ⟨h_M_pos, h_M_dvd, h_M_digits⟩
  have h_A004290_le : A004290 n ≤ M := Nat.sInf_le h_M_mem
  have h_M_lt : M < 10 ^ n := by
    have h_len : (List.replicate L_zeros 0 ++ List.replicate L_ones 1).length = L_zeros + L_ones := by
      rw [List.length_append, List.length_replicate, List.length_replicate]
    have h_len_eq : L_zeros + L_ones = i.val := by omega
    have h_i_val : i.val ≤ n := Nat.le_of_lt_succ i.isLt
    have h_lt_10 : ∀ d ∈ (List.replicate L_zeros 0 ++ List.replicate L_ones 1), d < 8 + 2 := by
      intro d hd
      have : d = 0 ∨ d = 1 := mem_replicate_zero_append_replicate_one L_zeros L_ones d hd
      omega
    have h_lt' := Nat.ofDigits_lt_base_pow_length' h_lt_10
    rw [h_len, h_len_eq] at h_lt'
    have h_pow : 10 ^ i.val ≤ 10 ^ n := Nat.pow_le_pow_right (by decide) h_i_val
    exact lt_of_lt_of_le h_lt' h_pow
  exact lt_of_le_of_lt h_A004290_le h_M_lt

theorem pow_ten_sub_one_div_nine_gt (L : ℕ) (hL : L > 0) : 10 ^ L < (10 ^ (L + 1) - 1) / 9 := by
  rw [← ofDigits_replicate_one_eq]
  have h_mul : 9 * 10 ^ L < 9 * ofDigits 10 (List.replicate (L + 1) 1) := by
    rw [ofDigits_replicate_one]
    have h_pow : 10 ^ (L + 1) = 10 * 10 ^ L := by ring
    rw [h_pow]
    have h_pos : 10 ^ L ≥ 10 := by
      have : 10 ^ 1 ≤ 10 ^ L := Nat.pow_le_pow_right (by decide) hL
      exact this
    omega
  exact Nat.lt_of_mul_lt_mul_left h_mul


theorem a004290_S_nonempty (n : ℕ) (hn : n > 0) :
  { m : ℕ | 0 < m ∧ n ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 }.Nonempty := by
  let f (i : Fin (n + 1)) : Fin n := ⟨ofDigits 10 (List.replicate i.val 1) % n, Nat.mod_lt _ hn⟩
  have h_ph : ∃ i j : Fin (n + 1), i ≠ j ∧ f i = f j := fin_pigeonhole (by omega) f
  have h_ph' : ∃ i j : Fin (n + 1), i.val > j.val ∧ f i = f j := by
    rcases h_ph with ⟨i, j, hij, h_eq⟩
    have h_ne : i.val ≠ j.val := by
      intro h
      apply hij
      ext
      exact h
    rcases lt_or_gt_of_ne h_ne with h_lt | h_gt
    · use j, i
      refine ⟨h_lt, h_eq.symm⟩
    · use i, j
  rcases h_ph' with ⟨i, j, h_gt, h_eq⟩
  let L_zeros := j.val
  let L_ones := i.val - j.val
  have h_ones : L_ones > 0 := by omega
  let M := ofDigits 10 (List.replicate L_zeros 0 ++ List.replicate L_ones 1)
  have h_not_empty : List.replicate L_zeros 0 ++ List.replicate L_ones 1 ≠ [] :=
    append_ne_nil_of_ne_nil (List.replicate L_zeros 0) (List.replicate L_ones 1) (replicate_ne_nil L_ones 1 h_ones)
  have h_M_eq : M = 10 ^ L_zeros * ofDigits 10 (List.replicate L_ones 1) := by
    exact ofDigits_append_replicate_zero L_zeros L_ones
  have h_ones_pos : ofDigits 10 (List.replicate L_ones 1) > 0 := by
    rcases L_ones with _ | L_ones'
    · omega
    · rw [List.replicate_succ, ofDigits_cons]
      omega
  have h_M_pos : M > 0 := by
    rw [h_M_eq]
    have h10 : 10 ^ L_zeros > 0 := by positivity
    exact Nat.mul_pos h10 h_ones_pos
  have h_M_dvd : n ∣ M := by
    rw [h_M_eq]
    have h_proj : (f i).val = (f j).val := by rw [h_eq]
    have h_mod : ofDigits 10 (List.replicate i.val 1) % n = ofDigits 10 (List.replicate j.val 1) % n := h_proj
    let A := ofDigits 10 (List.replicate i.val 1)
    let B := ofDigits 10 (List.replicate j.val 1)
    let C := ofDigits 10 (List.replicate L_ones 1)
    have h_rep : List.replicate i.val 1 = List.replicate j.val 1 ++ List.replicate (i.val - j.val) 1 := by
      rw [← List.replicate_add]
      congr 1
      omega
    have h_app : ofDigits 10 (List.replicate j.val 1 ++ List.replicate (i.val - j.val) 1) = B + 10 ^ j.val * C := by
      rw [Nat.ofDigits_append, List.length_replicate]
    have h_eq2 : A = B + 10 ^ j.val * C := by
      dsimp [A]
      rw [h_rep]
      exact h_app
    have h_mod2 : (B + 10 ^ j.val * C) % n = B % n := by
      rw [← h_eq2]
      exact h_mod
    exact dvd_of_add_mod_eq_mod B (10 ^ j.val * C) n h_mod2
  have h_M_digits : ∀ d ∈ Nat.digits 10 M, d = 0 ∨ d = 1 := by
    exact digits_ofDigits_replicate_zero_append_replicate_one L_zeros L_ones h_ones
  use M, h_M_pos, h_M_dvd, h_M_digits

theorem a004290_pos (n : ℕ) (hn : n > 0) : A004290 n > 0 := by
  have h_nonempty := a004290_S_nonempty n hn
  have h_mem := Nat.sInf_mem h_nonempty
  exact h_mem.1

theorem a004290_dvd (n : ℕ) (hn : n > 0) : n ∣ A004290 n := by
  have h_nonempty := a004290_S_nonempty n hn
  have h_mem := Nat.sInf_mem h_nonempty
  exact h_mem.2.1

theorem a004290_digits (n : ℕ) (hn : n > 0) : ∀ d ∈ Nat.digits 10 (A004290 n), d = 0 ∨ d = 1 := by
  have h_nonempty := a004290_S_nonempty n hn
  have h_mem := Nat.sInf_mem h_nonempty
  exact h_mem.2.2

theorem dvd_helper (n : ℕ) (L : ℕ) : n ∣ 10 ^ L * (n / Nat.gcd n (10 ^ L)) := by
  have h_gcd : Nat.gcd n (10 ^ L) ∣ 10 ^ L := Nat.gcd_dvd_right n (10 ^ L)
  have h_dvd_n : Nat.gcd n (10 ^ L) ∣ n := Nat.gcd_dvd_left n (10 ^ L)
  have h_div_mul : Nat.gcd n (10 ^ L) * (n / Nat.gcd n (10 ^ L)) = n := Nat.mul_div_cancel' h_dvd_n
  rcases h_gcd with ⟨q, hq⟩
  have h_eq : 10 ^ L * (n / Nat.gcd n (10 ^ L)) = (Nat.gcd n (10 ^ L) * q) * (n / Nat.gcd n (10 ^ L)) := by
    congr 1
  have h_goal : 10 ^ L * (n / Nat.gcd n (10 ^ L)) = n * q := by
    calc 10 ^ L * (n / Nat.gcd n (10 ^ L))
      _ = (Nat.gcd n (10 ^ L) * q) * (n / Nat.gcd n (10 ^ L)) := h_eq
      _ = (Nat.gcd n (10 ^ L) * (n / Nat.gcd n (10 ^ L))) * q := by ring
      _ = n * q := by rw [h_div_mul]
  rw [h_goal]
  exact dvd_mul_right n q

theorem digits_pow_ten_mul (L : ℕ) (M : ℕ) (hM : M > 0) :
  Nat.digits 10 (10 ^ L * M) = List.replicate L 0 ++ Nat.digits 10 M := by
  have h_base : 1 < 10 := by decide
  exact Nat.digits_base_pow_mul h_base hM

theorem mul_pow_ten_mem_S (n : ℕ) (L : ℕ) (M : ℕ) (hM : M > 0)
  (h_dvd : n ∣ 10 ^ L * M) (h_digits : ∀ d ∈ Nat.digits 10 M, d = 0 ∨ d = 1) :
  10 ^ L * M ∈ { m : ℕ | 0 < m ∧ n ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
  refine ⟨?_, h_dvd, ?_⟩
  · have h1 : 10 ^ L > 0 := by positivity
    exact Nat.mul_pos h1 hM
  · intro d hd
    rw [digits_pow_ten_mul L M hM] at hd
    rw [List.mem_append] at hd
    rcases hd with h1 | h2
    · left
      exact List.eq_of_mem_replicate h1
    · exact h_digits d h2

theorem a004290_le_mul_pow (n : ℕ) (hn : n > 0) (L : ℕ) :
  A004290 n ≤ 10 ^ L * A004290 (n / Nat.gcd n (10 ^ L)) := by
  let d := n / Nat.gcd n (10 ^ L)
  have h_gcd_pos : Nat.gcd n (10 ^ L) > 0 := Nat.gcd_pos_of_pos_left (10 ^ L) hn
  have h_gcd_le : Nat.gcd n (10 ^ L) ≤ n := Nat.le_of_dvd hn (Nat.gcd_dvd_left n (10 ^ L))
  have hd_pos : d > 0 := Nat.div_pos h_gcd_le h_gcd_pos
  have h_Ad_pos : A004290 d > 0 := a004290_pos d hd_pos
  have h_dvd_Ad : d ∣ A004290 d := a004290_dvd d hd_pos
  have h_dvd_n : n ∣ 10 ^ L * d := dvd_helper n L
  have h_dvd_final : n ∣ 10 ^ L * A004290 d := by
    rcases h_dvd_Ad with ⟨q, hq⟩
    rcases h_dvd_n with ⟨p, hp⟩
    use p * q
    calc 10 ^ L * A004290 d
      _ = 10 ^ L * (d * q) := by rw [hq]
      _ = (10 ^ L * d) * q := by ring
      _ = (n * p) * q := by rw [hp]
      _ = n * (p * q) := by ring
  have h_digits : ∀ d_val ∈ Nat.digits 10 (A004290 d), d_val = 0 ∨ d_val = 1 := a004290_digits d hd_pos
  have h_mem := mul_pow_ten_mem_S n L (A004290 d) h_Ad_pos h_dvd_final h_digits
  exact Nat.sInf_le h_mem

theorem dvd_pow_three_of_dvd_pow_nine_of_lt (g : ℕ) (hg : g < 10) (h_dvd : g ∣ 10 ^ 9) : g ∣ 10 ^ 3 := by
  have hg_cases : g = 0 ∨ g = 1 ∨ g = 2 ∨ g = 3 ∨ g = 4 ∨ g = 5 ∨ g = 6 ∨ g = 7 ∨ g = 8 ∨ g = 9 := by omega
  rcases hg_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exfalso
    have : 10 ^ 9 ≠ 0 := by decide
    have : 10 ^ 9 = 0 := Nat.eq_zero_of_zero_dvd h_dvd
    contradiction
  · decide
  · decide
  · exfalso
    revert h_dvd
    decide
  · decide
  · decide
  · exfalso
    revert h_dvd
    decide
  · exfalso
    revert h_dvd
    decide
  · decide
  · exfalso
    revert h_dvd
    decide

theorem a004290_le_of_dvd_pow_three (n : ℕ) (hn : n > 0) (g : ℕ) (hg_n : g ∣ n) (hg_3 : g ∣ 10 ^ 3) :
  A004290 n ≤ 10 ^ 3 * A004290 (n / g) := by
  let d := n / g
  have hg_pos : g > 0 := Nat.pos_of_dvd_of_pos hg_3 (by decide)
  have hd_pos : d > 0 := by
    have h_div_mul : g * d = n := Nat.mul_div_cancel' hg_n
    have h_mul_pos : g * d > 0 := by omega
    exact Nat.pos_of_mul_pos_left h_mul_pos
  have h_Ad_pos : A004290 d > 0 := a004290_pos d hd_pos
  have h_dvd_Ad : d ∣ A004290 d := a004290_dvd d hd_pos
  have h_dvd_n : n ∣ 10 ^ 3 * d := by
    rcases hg_3 with ⟨m, hm⟩
    have h_div_mul : g * d = n := Nat.mul_div_cancel' hg_n
    use m
    calc 10 ^ 3 * d
      _ = (g * m) * d := by rw [hm]
      _ = (g * d) * m := by ring
      _ = n * m := by rw [h_div_mul]
  have h_dvd_final : n ∣ 10 ^ 3 * A004290 d := by
    rcases h_dvd_Ad with ⟨q, hq⟩
    rcases h_dvd_n with ⟨p, hp⟩
    use p * q
    calc 10 ^ 3 * A004290 d
      _ = 10 ^ 3 * (d * q) := by rw [hq]
      _ = (10 ^ 3 * d) * q := by ring
      _ = (n * p) * q := by rw [hp]
      _ = n * (p * q) := by ring
  have h_digits : ∀ d_val ∈ Nat.digits 10 (A004290 d), d_val = 0 ∨ d_val = 1 := a004290_digits d hd_pos
  have h_mem := mul_pow_ten_mem_S n 3 (A004290 d) h_Ad_pos h_dvd_final h_digits
  exact Nat.sInf_le h_mem

theorem coprime_ten_dvd_pow_totient_sub_one (n : ℕ) (hn : n > 1) (h_coprime : Nat.Coprime 10 n) :
  n ∣ 10 ^ Nat.totient n - 1 := by
  have h_modeq := Nat.ModEq.pow_totient h_coprime
  have h_mod : 10 ^ Nat.totient n % n = 1 % n := h_modeq
  have h_one : 1 % n = 1 := Nat.mod_eq_of_lt (by omega)
  rw [h_one] at h_mod
  have h_pow_pos : 10 ^ Nat.totient n ≥ 1 := by
    have h_totient_pos : Nat.totient n > 0 := Nat.totient_pos.mpr (by omega)
    have : 10 ^ 1 ≤ 10 ^ Nat.totient n := Nat.pow_le_pow_right (by decide) h_totient_pos
    omega
  have h_div : 10 ^ Nat.totient n = n * (10 ^ Nat.totient n / n) + 10 ^ Nat.totient n % n := (Nat.div_add_mod _ _).symm
  rw [h_mod] at h_div
  have h_sub : 10 ^ Nat.totient n - 1 = n * (10 ^ Nat.totient n / n) := by omega
  rw [h_sub]
  exact dvd_mul_right n _

theorem coprime_ten_dvd_replicate_one (n : ℕ) (hn : n > 0) (h_coprime : Nat.Coprime 10 n) :
  n ∣ (10 ^ Nat.totient (9 * n) - 1) / 9 := by
  by_cases hn1 : 9 * n ≤ 1
  · omega
  · have h_9n_pos : 9 * n > 1 := by omega
    have h_coprime_9n : Nat.Coprime 10 (9 * n) := by
      have h9 : Nat.Coprime 10 9 := by decide
      exact Nat.Coprime.mul_right h9 h_coprime
    have h_dvd := coprime_ten_dvd_pow_totient_sub_one (9 * n) h_9n_pos h_coprime_9n
    have h_dvd_9 : 9 ∣ 10 ^ Nat.totient (9 * n) - 1 := by
      have h0 : ((10 ^ Nat.totient (9 * n) - 1 : ℕ) : ZMod 9) = 0 := by
        have h_pos : 10 ^ Nat.totient (9 * n) > 0 := by positivity
        have h_ge : 10 ^ Nat.totient (9 * n) ≥ 1 := h_pos
        rw [Nat.cast_sub h_ge]
        rw [pow_ten_zmod_nine (Nat.totient (9 * n))]
        rfl
      rwa [CharP.cast_eq_zero_iff (ZMod 9) 9] at h0
    have h_div_mul : 9 * ((10 ^ Nat.totient (9 * n) - 1) / 9) = 10 ^ Nat.totient (9 * n) - 1 := Nat.mul_div_cancel' h_dvd_9
    rw [← h_div_mul] at h_dvd
    exact Nat.dvd_of_mul_dvd_mul_left (by decide) h_dvd


theorem a004290_lt_pow_nine (k : ℕ) (hk : k > 0) : ∀ n < 10^k - 1, A004290 n < 10^(9*k - 1) := by
  induction k with
  | zero => omega
  | succ k' ih =>
    intro n hn
    by_cases hk' : k' = 0
    · subst hk'
      -- k = 1
      by_cases hn0 : n = 0
      · subst hn0
        rw [a004290_zero]
        decide
      · have hn_pos : n > 0 := by omega
        have h1 : A004290 n < 10 ^ n := a004290_lt_pow_ten n hn_pos
        have h2 : 10 ^ n ≤ 10 ^ 8 := Nat.pow_le_pow_right (by decide) (by omega)
        exact lt_of_lt_of_le h1 h2
    · -- k' > 0, so k' + 1 >= 2
      have hk'_pos : k' > 0 := by omega
      by_cases hn0 : n = 0
      · subst hn0
        rw [a004290_zero]
        positivity
      · have hn_pos : n > 0 := by omega
        by_cases hn_le : n ≤ 9 * k' + 8
        · have h1 : A004290 n < 10 ^ n := a004290_lt_pow_ten n hn_pos
          have h2 : 10 ^ n ≤ 10 ^ (9 * k' + 8) := Nat.pow_le_pow_right (by decide) hn_le
          have h3 : 10 ^ (9 * k' + 8) = 10 ^ (9 * (k' + 1) - 1) := rfl
          rw [← h3]
          exact lt_of_lt_of_le h1 h2
        · -- n > 9 * k' + 8, which is n >= 9 * (k' + 1)
          let g := Nat.gcd n (10 ^ 9)
          by_cases hg_ge : g ≥ 10
          · -- g >= 10
            have h_le := a004290_le_mul_pow n hn_pos 9
            let d := n / g
            have hd_le : d ≤ 10 ^ k' - 1 := by
              have h_n_le : n ≤ 10 ^ (k' + 1) - 2 := by omega
              have h_div_le : n / g ≤ n / 10 := Nat.div_le_div_left hg_ge (by decide)
              have h_div_le2 : n / 10 ≤ (10 ^ (k' + 1) - 2) / 10 := Nat.div_le_div_right h_n_le
              have h_div_val : (10 ^ (k' + 1) - 2) / 10 = 10 ^ k' - 1 := by
                have h_pow_eq : 10 ^ (k' + 1) = 10 * 10 ^ k' := by rw [Nat.pow_succ, Nat.mul_comm]
                rw [h_pow_eq]
                omega
              exact le_trans h_div_le (le_trans h_div_le2 (by rw [h_div_val]))
            by_cases hd_lt : d < 10 ^ k' - 1
            · have h_Ad_lt := ih hk'_pos d hd_lt
              have h_final : 10 ^ 9 * A004290 d < 10 ^ (9 * (k' + 1) - 1) := by
                have h_pow_eq : 10 ^ (9 * (k' + 1) - 1) = 10 ^ 9 * 10 ^ (9 * k' - 1) := by
                  have : 9 * (k' + 1) - 1 = 9 + (9 * k' - 1) := by omega
                  rw [this, Nat.pow_add]
                rw [h_pow_eq]
                exact mul_lt_mul_of_pos_left h_Ad_lt (by decide)
              exact lt_of_le_of_lt h_le h_final
            · have hd_eq : d = 10 ^ k' - 1 := by omega
              have hg_le : g ≤ 10 := by
                by_contra hc
                have hc' : g ≥ 11 := by omega
                have h_mul_ge : g * (10 ^ k' - 1) ≥ 11 * (10 ^ k' - 1) := Nat.mul_le_mul_right (10 ^ k' - 1) hc'
                have h_pow_ge : 10 ^ k' ≥ 10 := Nat.pow_le_pow_right (n := 10) (by decide) hk'_pos
                have h_calc : 11 * (10 ^ k' - 1) ≥ 10 ^ (k' + 1) - 1 := by
                  calc 11 * (10 ^ k' - 1)
                    _ = 10 * (10 ^ k' - 1) + (10 ^ k' - 1) := by ring
                    _ = 10 ^ (k' + 1) - 10 + 10 ^ k' - 1 := by
                      have : 10 * (10 ^ k' - 1) = 10 ^ (k' + 1) - 10 := by
                        rw [Nat.mul_sub_left_distrib]
                        have h_pow_eq : 10 ^ (k' + 1) = 10 * 10 ^ k' := by rw [Nat.pow_succ, Nat.mul_comm]
                        rw [h_pow_eq]
                      omega
                    _ ≥ 10 ^ (k' + 1) - 1 := by omega
                have h_n_eq : n = g * d := (Nat.mul_div_cancel' (Nat.gcd_dvd_left n (10 ^ 9))).symm
                rw [hd_eq] at h_n_eq
                omega
              have hg_eq : g = 10 := by omega
              have h_gcd_10 : Nat.gcd n 10 = 10 := by
                have h_dvd : 10 ∣ n := by
                  rw [← hg_eq]
                  exact Nat.gcd_dvd_left n (10 ^ 9)
                exact Nat.gcd_eq_right h_dvd
              have h_le_10 := a004290_le_mul_pow n hn_pos 1
              have h_le_10' : A004290 n ≤ 10 * A004290 d := by
                have h10 : 10 ^ 1 = 10 := by rfl
                rw [h10] at h_le_10
                rw [h_gcd_10] at h_le_10
                have hd_val : d = n / 10 := by
                  dsimp [d]
                  rw [hg_eq]
                rw [← hd_val] at h_le_10
                exact h_le_10
              have h_Ad_val : A004290 d = (10 ^ (9 * k') - 1) / 9 := by
                rw [hd_eq]
                exact part2 k' hk'_pos
              have h_final : 10 * A004290 d < 10 ^ (9 * (k' + 1) - 1) := by
                rw [h_Ad_val]
                have h_Ad_lt : (10 ^ (9 * k') - 1) / 9 < 10 ^ (9 * k') := by
                  apply Nat.div_lt_of_lt_mul
                  have h_pow : 10 ^ (9 * k') > 0 := by positivity
                  omega
                calc 10 * ((10 ^ (9 * k') - 1) / 9)
                  _ < 10 * 10 ^ (9 * k') := mul_lt_mul_of_pos_left h_Ad_lt (by decide)
                  _ = 10 ^ (9 * k' + 1) := by ring
                  _ ≤ 10 ^ (9 * k' + 8) := Nat.pow_le_pow_right (n := 10) (by decide) (by omega)
                  _ = 10 ^ (9 * (k' + 1) - 1) := rfl
              exact lt_of_le_of_lt h_le_10' h_final
          · -- g < 10
            have hg_lt : g < 10 := by omega
            have hg_dvd_3 : g ∣ 10 ^ 3 := dvd_pow_three_of_dvd_pow_nine_of_lt g hg_lt (Nat.gcd_dvd_right n (10 ^ 9))
            have hg_dvd_n : g ∣ n := Nat.gcd_dvd_left n (10 ^ 9)
            by_cases hg_1 : g = 1
            · -- g = 1
              sorry
            · -- g >= 2
              have h_le := a004290_le_of_dvd_pow_three n hn_pos g hg_dvd_n hg_dvd_3
              let d := n / g
              have hd_lt : d < 10 ^ k' - 1 := by
                -- since g >= 2, d <= n/2.
                -- We want to prove: d < 10^k' - 1
                -- since k' >= 1, 10^k' >= 10.
                -- n <= 10^(k'+1) - 2.
                -- d <= (10^(k'+1) - 2) / 2 = 5 * 10^k' - 1
                -- which is not < 10^k' - 1.
                -- Wait! Is d < 10^k' - 1 true?
                -- No, d can be up to 5 * 10^k' - 1, which is larger than 10^k' - 1.
                -- But wait, we can apply IH if we can show d < 10^(k'+1) - 1?
                -- No, the IH is on k', so it requires d < 10^k' - 1.
                -- Wait, if g >= 2, can we show d < 10^k' - 1?
                -- No, d is only < 10^(k'+1) - 1.
                -- But wait!
                sorry





theorem oeis_a004290_conjecture_radcliffe (k : ℕ) (hk : k > 0) :
  A004290 (10 ^ k) = 10 ^ k ∧
  A004290 (10 ^ k - 1) = (10 ^ (9 * k) - 1) / 9 ∧
  ∀ n < 10 ^ k - 1, A004290 n < A004290 (10 ^ k - 1) := by
  refine ⟨part1 k hk, part2 k hk, ?_⟩
  intro n hn
  rw [part2 k hk]
  by_cases hn0 : n = 0
  · subst hn0
    rw [a004290_zero]
    have h_pos : 0 < (10 ^ (9 * k) - 1) / 9 := by
      have h_9k : 9 * k > 0 := by omega
      have h_pow : 10 ≤ 10 ^ (9 * k) := Nat.pow_le_pow_right (n := 10) (by decide) h_9k
      have h_sub : 9 ≤ 10 ^ (9 * k) - 1 := by omega
      exact Nat.div_pos h_sub (by decide)
    exact h_pos
  · have hn_pos : n > 0 := by omega
    by_cases hn_le : n ≤ 9 * k - 1
    · have h1 : A004290 n < 10 ^ n := a004290_lt_pow_ten n hn_pos
      have h2 : 10 ^ n ≤ 10 ^ (9 * k - 1) := Nat.pow_le_pow_right (by decide) hn_le
      have h3 : 10 ^ (9 * k - 1) < (10 ^ (9 * k) - 1) / 9 := by
        have h_9k_pos : 9 * k - 1 > 0 := by omega
        have h_eq : 9 * k - 1 + 1 = 9 * k := by omega
        have h_gt := pow_ten_sub_one_div_nine_gt (9 * k - 1) h_9k_pos
        rwa [h_eq] at h_gt
      exact lt_of_lt_of_le h1 (le_trans h2 (le_of_lt h3))
    · have h_lt := a004290_lt_pow_nine k hk n hn
      have h_pow_nine : 10 ^ (9 * k - 1) < (10 ^ (9 * k) - 1) / 9 := by
        have h_pos' : 9 * k - 1 > 0 := by omega
        have h_eq : 9 * k - 1 + 1 = 9 * k := by omega
        have h_gt := pow_ten_sub_one_div_nine_gt (9 * k - 1) h_pos'
        rwa [h_eq] at h_gt
      exact lt_of_lt_of_le h_lt (le_of_lt h_pow_nine)




