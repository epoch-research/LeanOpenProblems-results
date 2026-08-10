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
      have : 10 ^ 1 ≤ 10 ^ (9 * k) := Nat.pow_le_pow_right (by decide) h_9k
      exact this
    have h_sub : 9 ≤ 10 ^ (9 * k) - 1 := by omega
    exact Nat.div_pos h_sub (by decide)
  · intro d hd
    rw [digits_replicate_one_eq (9 * k)] at hd
    have hd_eq : d = 1 := List.eq_of_mem_replicate hd
    right
    exact hd_eq


theorem ofDigits_ge (l : List ℕ) (hl : ∀ d ∈ l, d = 0 ∨ d = 1) (L : ℕ) (hsum : l.sum ≥ L) :
  ofDigits 10 l ≥ ofDigits 10 (List.replicate L 1) := by
  induction l generalizing L with
  | nil =>
    have h_sum : 0 ≥ L := by
      simpa using hsum
    have hL : L = 0 := by omega
    subst hL
    rfl
  | cons d t ih =>
    have hd_mem : d ∈ d :: t := List.mem_cons_self d t
    have hd_val : d = 0 ∨ d = 1 := hl d hd_mem
    have ht_val : ∀ x ∈ t, x = 0 ∨ x = 1 := by
      intro x hx
      exact hl x (List.mem_cons_of_mem d hx)
    rcases hd_val with rfl | rfl
    · -- d = 0
      rw [ofDigits_cons, zero_add]
      have ht_sum : t.sum ≥ L := by
        simpa using hsum
      have ih_t := ih ht_val L ht_sum
      have h10 : 10 * ofDigits 10 t ≥ ofDigits 10 (List.replicate L 1) := by
        omega
      exact h10
    · -- d = 1
      rw [ofDigits_cons]
      rcases L with _ | L'
      · rfl
      · rw [List.replicate_succ, ofDigits_cons]
        have ht_sum : t.sum ≥ L' := by
          simpa using hsum
        have ih_t := ih ht_val L' ht_sum
        omega


theorem sum_le_of_ofDigits_le (X : ℕ) (hXM : X > M) (M : ℕ) (t : List ℕ) (ht : ∀ x ∈ t, x ≤ M) (L' : ℕ) (h : ofDigits X t ≤ ofDigits X (List.replicate L' M)) :
  t.sum ≤ L' * M := by
  induction t generalizing L' with
  | nil =>
    omega
  | cons c s ih =>
    have hc_mem : c ∈ c :: s := List.mem_cons_self c s
    have hc_le : c ≤ M := ht c hc_mem
    have hs_val : ∀ x ∈ s, x ≤ M := by
      intro x hx
      exact ht x (List.mem_cons_of_mem c hx)
    rcases L' with _ | L''
    · -- L' = 0
      rw [ofDigits_cons] at h
      have hc_eq : c = 0 := by omega
      have hs_eq : ofDigits X s = 0 := by omega
      have hs_sum_zero : s.sum = 0 := by
        -- Since ofDigits X s = 0, we can use the induction hypothesis
        have h_le : ofDigits X s ≤ ofDigits X (List.replicate 0 M) := by
          rw [hs_eq]
          rfl
        have ih_s := ih hs_val 0 h_le
        exact ih_s
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
        have h_lhs2 : c + X * ofDigits X s ≥ X + X * ofDigits X (List.replicate L'' M) := by
          omega
        have h_contra : c + X * ofDigits X s > M + X * ofDigits X (List.replicate L'' M) := by
          omega
        omega
      have ih_s := ih hs_val L'' hs_le
      omega

theorem ofDigits_ge_general (X : ℕ) (hX : X ≥ 1) (M : ℕ) (b : List ℕ) (hb : ∀ x ∈ b, x ≤ M) (L : ℕ) (hsum : b.sum ≥ L * M) (hXM : X > M) :
  ofDigits X b ≥ ofDigits X (List.replicate L M) := by
  induction b generalizing L with
  | nil =>
    have h_sum : 0 ≥ L * M := by
      simpa using hsum
    rcases L with _ | L'
    · rfl
    · have : L' * M + M = 0 := by omega
      have hM : M = 0 := by omega
      subst hM
      induction L' with
      | zero => rfl
      | succ L'' ih' => rfl
  | cons d t ih =>
    have hd_mem : d ∈ d :: t := List.mem_cons_self d t
    have hd_val : d ≤ M := hb d hd_mem
    have ht_val : ∀ x ∈ t, x ≤ M := by
      intro x hx
      exact hb x (List.mem_cons_of_mem d hx)
    rcases L with _ | L'
    · rfl
    · rw [List.replicate_succ, ofDigits_cons]
      rw [ofDigits_cons]
      have ht_sum : t.sum ≥ L' * M := by
        omega
      have ih_t := ih ht_val L' ht_sum
      -- Now we want to show: d + X * ofDigits X t ≥ M + X * ofDigits X (List.replicate L' M)
      -- We know ih_t : ofDigits X t ≥ ofDigits X (List.replicate L' M)
      by_cases h_eq : ofDigits X t = ofDigits X (List.replicate L' M)
      · have h_le_eq : ofDigits X t ≤ ofDigits X (List.replicate L' M) := by omega
        have ht_sum_le : t.sum ≤ L' * M := sum_le_of_ofDigits_le X hXM M t ht_val L' h_le_eq
        have hd_ge : d ≥ M := by omega
        omega
      · have h_gt : ofDigits X t > ofDigits X (List.replicate L' M) := by omega
        have h_ge_succ : ofDigits X t ≥ ofDigits X (List.replicate L' M) + 1 := h_gt
        calc d + X * ofDigits X t
          _ ≥ d + X * (ofDigits X (List.replicate L' M) + 1) := by omega
          _ = d + X + X * ofDigits X (List.replicate L' M) := by ring
          _ ≥ M + X * ofDigits X (List.replicate L' M) := by omega


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
    rw [h_mul, ih]
    have h_pow_pos : 0 < X ^ L' := by positivity
    have h_pow_pos' : 1 ≤ X ^ L' := h_pow_pos
    omega


theorem ofDigits_replicate_nine_eq (k : ℕ) (hk : k > 0) :
  ofDigits (10^k) (List.replicate 9 ((10^k - 1) / 9)) = (10 ^ (9 * k) - 1) / 9 := by
  have hX : 10 ^ k ≥ 1 := by positivity
  have h_id := ofDigits_replicate_one_general (10^k) hX 9
  have h_pow : (10^k)^9 = 10^(9*k) := by ring
  rw [h_pow] at h_id
  have h_mul := ofDigits_replicate_mul (10^k) ((10^k - 1) / 9) 9
  have h_9mul : 9 * ((10^k - 1) / 9) = 10^k - 1 := by
    have h_dvd : 9 ∣ 10^k - 1 := by
      have h10 : ((10^k : ℕ) : ZMod 9) = 1 := pow_ten_zmod_nine k
      have h0 : (((10^k - 1 : ℕ) : ℕ) : ZMod 9) = 0 := by
        push_cast
        rw [h10]
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
  by_cases hx0 : x = 0
  · subst hx0
    rw [Nat.digits_zero]
    omega
  · have h_base : 10 ≥ 2 := by decide
    have h_len := Nat.length_digits_lt 10 x h_base hx0
    have h_pow : 10 ^ ((Nat.digits 10 x).length - 1) ≤ x := h_len.1
    have h_lt : 10 ^ ((Nat.digits 10 x).length - 1) < 10 ^ k := by
      calc 10 ^ ((Nat.digits 10 x).length - 1)
        _ ≤ x := h_pow
        _ < 10 ^ k := hx
    have h_exp : (Nat.digits 10 x).length - 1 < k := Nat.pow_lt_pow_iff_right (by decide) |>.mp h_lt
    omega


theorem ofDigits_le_replicate_one (l : List ℕ) (hl : ∀ d ∈ l, d ≤ 1) (k : ℕ) (hk : l.length ≤ k) :
  ofDigits 10 l ≤ ofDigits 10 (List.replicate k 1) := by
  induction l generalizing k with
  | nil =>
    rfl
  | cons d t ih =>
    rcases k with _ | k'
    · omega
    · rw [List.replicate_succ, ofDigits_cons, ofDigits_cons]
      have hd_mem : d ∈ d :: t := List.mem_cons_self d t
      have hd_le : d ≤ 1 := hl d hd_mem
      have ht_val : ∀ x ∈ t, x ≤ 1 := by
        intro x hx
        exact hl x (List.mem_cons_of_mem d hx)
      have ht_len : t.length ≤ k' := by omega
      have ih_t := ih ht_val k' ht_len
      omega


theorem le_replicate_one (x : ℕ) (k : ℕ) (hx : x < 10^k) (h_01 : ∀ d ∈ Nat.digits 10 x, d = 0 ∨ d = 1) :
  x ≤ (10^k - 1) / 9 := by
  have h_base : 1 < 10 := by decide
  have h_eq : x = ofDigits 10 (Nat.digits 10 x) := (Nat.ofDigits_digits 10 h_base x).symm
  rw [h_eq]
  rw [ofDigits_replicate_one_eq]
  have h_le : ∀ d ∈ Nat.digits 10 x, d ≤ 1 := by
    intro d hd
    rcases h_01 d hd with rfl | rfl <;> omega
  have h_len := digits_len_le x k hx
  exact ofDigits_le_replicate_one (Nat.digits 10 x) h_le k h_len


theorem ofDigits_modEq (X : ℕ) (b : List ℕ) :
  ofDigits X b ≡ b.sum [MOD X - 1] := by
  induction b with
  | nil => rfl
  | cons d t ih =>
    rw [ofDigits_cons, List.sum_cons]
    -- We want to show: d + X * ofDigits X t ≡ d + t.sum [MOD X - 1]
    have h1 : X ≡ 1 [MOD X - 1] := by
      rcases X with _ | X'
      · rfl
      · rw [Nat.modEq_iff_dvd]
        omega
    have h2 : X * ofDigits X t ≡ 1 * ofDigits X t [MOD X - 1] := Nat.ModEq.mul h1 (Nat.ModEq.refl _)
    rw [one_mul] at h2
    have h3 : d + X * ofDigits X t ≡ d + ofDigits X t [MOD X - 1] := Nat.ModEq.add (Nat.ModEq.refl d) h2
    exact Nat.ModEq.trans h3 (Nat.ModEq.add (Nat.ModEq.refl d) ih)


theorem sum_pos_of_ofDigits_pos (X : ℕ) (b : List ℕ) (h : ofDigits X b > 0) : b.sum > 0 := by
  induction b with
  | nil =>
    omega
  | cons d t ih =>
    rw [List.sum_cons]
    omega




theorem digits_div_base (y : ℕ) : Nat.digits 10 (y / 10) = (Nat.digits 10 y).drop 1 := by
  have h_base : 1 < 10 := by decide
  rcases y with _ | y'
  · rfl
  · -- y' + 1 > 0
    have hy : y' + 1 > 0 := by omega
    rw [Nat.digits_def' h_base hy]
    rfl

theorem test_digits_div_pow (m s : ℕ) : Nat.digits 10 (m / 10^s) = (Nat.digits 10 m).drop s := by
  induction s with
  | zero =>
    rfl
  | succ s' ih =>
    have h_pow : 10 ^ (s' + 1) = 10 ^ s' * 10 := by ring
    rw [h_pow, Nat.div_mul_eq_div_div]
    rw [digits_div_base]
    rw [ih]
    rw [List.drop_drop]
    rfl

theorem ofDigits_take_eq_mod (y : ℕ) (k : ℕ) :
  ofDigits 10 ((Nat.digits 10 y).take k) = y % 10 ^ k := by
  induction k generalizing y with
  | zero =>
    rfl
  | succ k' ih =>
    by_cases hy : y = 0
    · subst hy
      rw [Nat.digits_zero, List.take_nil]
      rfl
    · have h_base : 1 < 10 := by decide
      rw [Nat.digits_def' h_base (Nat.pos_of_ne_zero hy), List.take_succ_cons, ofDigits_cons, ih]
      have h_div : y = 10 * (y / 10) + y % 10 := (Nat.div_add_mod y 10).symm
      have h_div2 : y = y % 10 + 10 * (y / 10) := by omega
      rw [h_div2]
      rw [Nat.add_mul_mod_self_left]
      have h_mod : y % 10 < 10 := Nat.mod_lt y (by decide)
      have h_mod_pow : (y % 10 + 10 * (y / 10 % 10 ^ k')) % 10 ^ (k' + 1) = y % 10 + 10 * (y / 10 % 10 ^ k') := by
        have h_pow : 10 ^ (k' + 1) = 10 * 10 ^ k' := by ring
        rw [h_pow]
        apply Nat.mod_eq_of_lt
        have h_lt' : y / 10 % 10 ^ k' < 10 ^ k' := Nat.mod_lt (y / 10) (by positivity)
        omega
      rw [h_mod_pow]
      ring


theorem mod_le_replicate_one (y : ℕ) (k : ℕ) (h_01 : ∀ d ∈ Nat.digits 10 y, d = 0 ∨ d = 1) :
  y % 10 ^ k ≤ (10 ^ k - 1) / 9 := by
  rw [← ofDigits_take_eq_mod]
  rw [ofDigits_replicate_one_eq]
  have h_le : ∀ d ∈ (Nat.digits 10 y).take k, d ≤ 1 := by
    intro d hd
    have hd_mem : d ∈ Nat.digits 10 y := List.mem_of_mem_take hd
    rcases h_01 d hd_mem with rfl | rfl <;> omega
  have h_len : ((Nat.digits 10 y).take k).length ≤ k := List.length_take_le k (Nat.digits 10 y)
  exact ofDigits_le_replicate_one ((Nat.digits 10 y).take k) h_le k h_len


theorem digits_member_eq_div_mod (B : ℕ) (hB : B ≥ 2) (y : ℕ) (x : ℕ) (hx : x ∈ Nat.digits B y) :
  ∃ i : ℕ, x = (y / B ^ i) % B := by
  induction y generalizing x with
  | zero =>
    rw [Nat.digits_zero] at hx
    cases hx
  | succ y' ih =>
    have hy : y' + 1 > 0 := by omega
    rw [Nat.digits_def' hB hy] at hx
    rcases hx with h_eq | h_mem
    · use 0
      rw [h_eq]
      rfl
    · have ih_x := ih x h_mem
      rcases ih_x with ⟨j, hj⟩
      use j + 1
      rw [hj]
      have h_pow : B ^ (j + 1) = B ^ j * B := by ring
      rw [h_pow, Nat.div_mul_eq_div_div]


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
  have h_eq : m = ofDigits (10 ^ k) b := (Nat.ofDigits_digits (10 ^ k) hB m).symm
  have hb_le : ∀ x ∈ b, x ≤ (10 ^ k - 1) / 9 := by
    intro x hx
    exact digits_pow_ten_le_replicate_one m k hk h_01 x hx
  have h_modeq : m ≡ b.sum [MOD 10 ^ k - 1] := ofDigits_modEq (10 ^ k) b
  have h_mod0 : m ≡ 0 [MOD 10 ^ k - 1] := by
    rw [Nat.modEq_iff_dvd]
    exact hdvd
  have h_sum_mod0 : b.sum ≡ 0 [MOD 10 ^ k - 1] := Nat.ModEq.trans h_modeq.symm h_mod0
  have h_sum_pos : b.sum > 0 := by
    apply sum_pos_of_ofDigits_pos (10 ^ k) b
    omega
  have h_sum_ge : b.sum ≥ 10 ^ k - 1 := by
    have hdvd_sum : (10 ^ k - 1) ∣ b.sum := by
      rwa [← Nat.modEq_iff_dvd]
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
      have h0 : (((10^k - 1 : ℕ) : ℕ) : ZMod 9) = 0 := by
        push_cast
        rw [h10]
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

theorem Nat.sInf_eq {s : Set ℕ} {a : ℕ} (ha : a ∈ s) (hb : ∀ b ∈ s, a ≤ b) : sInf s = a :=
  le_antisymm (Nat.sInf_le ha) (hb (sInf s) (Nat.sInf_mem ⟨a, ha⟩))

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


theorem ofDigits_replicate_zero (L : ℕ) : ofDigits 10 (List.replicate L 0) = 0 := by
  induction L with
  | zero => rfl
  | succ L' ih =>
    rw [List.replicate_succ, ofDigits_cons, ih]
    ring

theorem ofDigits_append_replicate_zero (L_zeros L_ones : ℕ) :
  ofDigits 10 (List.replicate L_zeros 0 ++ List.replicate L_ones 1) = 10 ^ L_zeros * ofDigits 10 (List.replicate L_ones 1) := by
  have h_app := Nat.ofDigits_append 10 (List.replicate L_zeros 0) (List.replicate L_ones 1)
  rw [ofDigits_replicate_zero, List.length_replicate] at h_app
  omega

