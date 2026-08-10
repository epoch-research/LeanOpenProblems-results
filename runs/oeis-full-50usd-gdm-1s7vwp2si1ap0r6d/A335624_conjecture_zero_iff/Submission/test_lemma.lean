import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 1000000

open Nat Finset

def A335624_rep (n : ℕ) : Prop :=
  ∃ x y z w : ℕ, x^2 + y^2 + z^2 + w^2 = n ∧ Nat.sqrt (x + 3 * y + 4 * z) ^ 2 = x + 3 * y + 4 * z

def A335624 (n : ℕ) : ℕ :=
  let B : ℕ := Nat.sqrt n + 1
  let R := range B

  R.sum fun x =>
  R.sum fun y =>
  R.sum fun z =>
  R.sum fun w =>
    if x^2 + y^2 + z^2 + w^2 = n
      ∧ (let m := x + 3 * y + 4 * z; Nat.sqrt m ^ 2 = m)
    then 1 else 0

lemma mod_eight_of_add_eight_mul (q r : ℕ) : (r + 8 * q) ^ 2 % 8 = r ^ 2 % 8 := by
  have h1 : (r + 8 * q) ^ 2 = r ^ 2 + 8 * (2 * q * r + 8 * q ^ 2) := by ring
  rw [h1]
  rw [Nat.add_mul_mod_self_left]

lemma sq_mod_eight (n : ℕ) : n^2 % 8 = 0 ∨ n^2 % 8 = 1 ∨ n^2 % 8 = 4 := by
  have h : n % 8 < 8 := Nat.mod_lt _ (by decide)
  have hn : n = n % 8 + 8 * (n / 8) := by omega
  generalize hq : n / 8 = q at hn
  generalize hr : n % 8 = r at hn h
  rw [hn]
  rw [mod_eight_of_add_eight_mul q r]
  interval_cases r <;> decide


lemma sq_mod_eight_of_odd (x : ℕ) (h : x % 2 = 1) : x^2 % 8 = 1 := by
  have h8 : x % 8 < 8 := Nat.mod_lt _ (by decide)
  have hx : x = x % 8 + 8 * (x / 8) := by omega
  generalize hq : x / 8 = q at hx
  generalize hr : x % 8 = r at hx h8 h
  rw [hx]
  rw [mod_eight_of_add_eight_mul q r]
  have hr2 : r % 2 = 1 := by
    -- since x = r + 8q, x % 2 = (r + 8q) % 2 = r % 2
    have h_eq : (r + 8 * q) % 2 = r % 2 := by
      have h2 : r + 8 * q = r + 2 * (4 * q) := by ring
      rw [h2]
      rw [Nat.add_mul_mod_self_left]
    omega
  interval_cases r <;> revert hr2 <;> decide

lemma even_of_sq_mod_eight_ne_one (x : ℕ) (h : x^2 % 8 ≠ 1) : x % 2 = 0 := by
  have h_cases : x % 2 = 0 ∨ x % 2 = 1 := by omega
  rcases h_cases with h_even | h_odd
  · exact h_even
  · have h1 := sq_mod_eight_of_odd x h_odd
    contradiction

lemma evens_of_sum_sq_mod_eight (x y z w : ℕ) (h : (x^2 + y^2 + z^2 + w^2) % 8 = 0) :
    x % 2 = 0 ∧ y % 2 = 0 ∧ z % 2 = 0 ∧ w % 2 = 0 := by
  have h_sx : x^2 % 8 < 8 := Nat.mod_lt _ (by decide)
  have h_sy : y^2 % 8 < 8 := Nat.mod_lt _ (by decide)
  have h_sz : z^2 % 8 < 8 := Nat.mod_lt _ (by decide)
  have h_sw : w^2 % 8 < 8 := Nat.mod_lt _ (by decide)
  have hx_eq : x^2 = x^2 % 8 + 8 * (x^2 / 8) := (Nat.mod_add_div _ _).symm
  have hy_eq : y^2 = y^2 % 8 + 8 * (y^2 / 8) := (Nat.mod_add_div _ _).symm
  have hz_eq : z^2 = z^2 % 8 + 8 * (z^2 / 8) := (Nat.mod_add_div _ _).symm
  have hw_eq : w^2 = w^2 % 8 + 8 * (w^2 / 8) := (Nat.mod_add_div _ _).symm
  generalize hsx : x^2 % 8 = sx at hx_eq h_sx
  generalize hsy : y^2 % 8 = sy at hy_eq h_sy
  generalize hsz : z^2 % 8 = sz at hz_eq h_sz
  generalize hsw : w^2 % 8 = sw at hw_eq h_sw
  have hx_sq := sq_mod_eight x
  have hy_sq := sq_mod_eight y
  have hz_sq := sq_mod_eight z
  have hw_sq := sq_mod_eight w
  rw [hsx] at hx_sq
  rw [hsy] at hy_sq
  rw [hsz] at hz_sq
  rw [hsw] at hw_sq
  have hsum : (sx + sy + sz + sw) % 8 = 0 := by
    have h_total : x^2 + y^2 + z^2 + w^2 = (sx + sy + sz + sw) + 8 * (x^2 / 8 + y^2 / 8 + z^2 / 8 + w^2 / 8) := by omega
    have h_mod : (x^2 + y^2 + z^2 + w^2) % 8 = (sx + sy + sz + sw) % 8 := by
      rw [h_total]
      rw [Nat.add_mul_mod_self_left]
    omega
  have h_ne_one : sx ≠ 1 ∧ sy ≠ 1 ∧ sz ≠ 1 ∧ sw ≠ 1 := by
    rcases hx_sq with rfl | rfl | rfl <;> rcases hy_sq with rfl | rfl | rfl <;>
    rcases hz_sq with rfl | rfl | rfl <;> rcases hw_sq with rfl | rfl | rfl <;>
    revert hsum <;> decide
  constructor
  · apply even_of_sq_mod_eight_ne_one x
    rw [hsx]
    exact h_ne_one.1
  · constructor
    · apply even_of_sq_mod_eight_ne_one y
      rw [hsy]
      exact h_ne_one.2.1
    · constructor
      · apply even_of_sq_mod_eight_ne_one z
        rw [hsz]
        exact h_ne_one.2.2.1
      · apply even_of_sq_mod_eight_ne_one w
        rw [hsw]
        exact h_ne_one.2.2.2

lemma even_of_mul_even (a : ℕ) (h : 4 * a = s^2) : Even s := by
  have h2 : s^2 % 2 = 0 := by
    rw [← h]
    ring_nf
    omega
  have h3 : s % 2 = 0 := by
    have h4 : s % 2 < 2 := Nat.mod_lt _ (by decide)
    have hs_eq : s = 2 * (s / 2) + s % 2 := (Nat.div_add_mod s 2).symm
    generalize hq : s / 2 = q at hs_eq
    generalize hr : s % 2 = r at hs_eq h4 h2
    rw [hs_eq] at h2
    interval_cases r
    · rfl
    · exfalso
      have h5 : (2 * q + 1) ^ 2 = 1 + (2 * q ^ 2 + 2 * q) * 2 := by ring
      rw [h5] at h2
      rw [Nat.add_mul_mod_self_right] at h2
      contradiction
  exact even_iff_two_dvd.mpr (Nat.dvd_of_mod_eq_zero h3)

lemma rep_of_rep_sixteen_rev (n : ℕ) (hn : n % 2 = 0) (h : A335624_rep (16 * n)) : A335624_rep n := by
  rcases h with ⟨x, y, z, w, hsum, hsq⟩
  -- 16n is a multiple of 8
  have h8 : (x^2 + y^2 + z^2 + w^2) % 8 = 0 := by
    rw [hsum]
    have h_div : 16 * n = 8 * (2 * n) := by ring
    rw [h_div]
    rw [Nat.mul_mod_right]
  have h_evens1 := evens_of_sum_sq_mod_eight x y z w h8
  obtain ⟨x1, rfl⟩ : 2 ∣ x := Nat.dvd_of_mod_eq_zero h_evens1.1
  obtain ⟨y1, rfl⟩ : 2 ∣ y := Nat.dvd_of_mod_eq_zero h_evens1.2.1
  obtain ⟨z1, rfl⟩ : 2 ∣ z := Nat.dvd_of_mod_eq_zero h_evens1.2.2.1
  obtain ⟨w1, rfl⟩ : 2 ∣ w := Nat.dvd_of_mod_eq_zero h_evens1.2.2.2
  -- now (2*x1)^2 + (2*y1)^2 + (2*z1)^2 + (2*w1)^2 = 16n
  -- 4 * (x1^2 + y1^2 + z1^2 + w1^2) = 16n -> x1^2 + y1^2 + z1^2 + w1^2 = 4n
  have hsum1 : x1^2 + y1^2 + z1^2 + w1^2 = 4 * n := by
    have h_sub : (2*x1)^2 + (2*y1)^2 + (2*z1)^2 + (2*w1)^2 = 4 * (x1^2 + y1^2 + z1^2 + w1^2) := by ring
    have h_16 : 16 * n = 4 * (4 * n) := by ring
    rw [h_sub, h_16] at hsum
    exact Nat.eq_of_mul_eq_mul_left (by decide) hsum
  -- 4n is a multiple of 8 because n is even
  have h8_2 : (x1^2 + y1^2 + z1^2 + w1^2) % 8 = 0 := by
    rw [hsum1]
    obtain ⟨n2, rfl⟩ : 2 ∣ n := Nat.dvd_of_mod_eq_zero hn
    have h_div : 4 * (2 * n2) = 8 * n2 := by ring
    rw [h_div]
    rw [Nat.mul_mod_right]
  have h_evens2 := evens_of_sum_sq_mod_eight x1 y1 z1 w1 h8_2
  obtain ⟨x2, rfl⟩ : 2 ∣ x1 := Nat.dvd_of_mod_eq_zero h_evens2.1
  obtain ⟨y2, rfl⟩ : 2 ∣ y1 := Nat.dvd_of_mod_eq_zero h_evens2.2.1
  obtain ⟨z2, rfl⟩ : 2 ∣ z1 := Nat.dvd_of_mod_eq_zero h_evens2.2.2.1
  obtain ⟨w2, rfl⟩ : 2 ∣ w1 := Nat.dvd_of_mod_eq_zero h_evens2.2.2.2
  -- now x = 4*x2, y = 4*y2, z = 4*z2, w = 4*w2
  -- x2^2 + y2^2 + z2^2 + w2^2 = n
  have hsum2 : x2^2 + y2^2 + z2^2 + w2^2 = n := by
    have h_sub : (2*x2)^2 + (2*y2)^2 + (2*z2)^2 + (2*w2)^2 = 4 * (x2^2 + y2^2 + z2^2 + w2^2) := by ring
    rw [h_sub] at hsum1
    exact Nat.eq_of_mul_eq_mul_left (by decide) hsum1
  -- x + 3y + 4z = 4 * (x2 + 3y2 + 4z2) is a perfect square
  have h_linear : 2 * (2 * x2) + 3 * (2 * (2 * y2)) + 4 * (2 * (2 * z2)) = 4 * (x2 + 3 * y2 + 4 * z2) := by ring
  have h_sq_eq : 4 * (x2 + 3 * y2 + 4 * z2) = (2 * (2 * x2) + 3 * (2 * (2 * y2)) + 4 * (2 * (2 * z2))).sqrt ^ 2 := by
    rw [← h_linear, hsq]
  have h_even_s := even_of_mul_even (x2 + 3 * y2 + 4 * z2) h_sq_eq
  obtain ⟨s2, hs2⟩ : 2 ∣ (2 * (2 * x2) + 3 * (2 * (2 * y2)) + 4 * (2 * (2 * z2))).sqrt := even_iff_two_dvd.mp h_even_s
  have h_final_sq : (x2 + 3 * y2 + 4 * z2) = s2 ^ 2 := by
    rw [hs2] at h_sq_eq
    nlinarith
  refine ⟨x2, y2, z2, w2, hsum2, ?_⟩
  rw [h_final_sq, Nat.sqrt_eq' s2]

lemma rep_of_rep_sixteen (n : ℕ) (h : A335624_rep n) : A335624_rep (16 * n) := by
  rcases h with ⟨x, y, z, w, hsum, hsq⟩
  refine ⟨4 * x, 4 * y, 4 * z, 4 * w, ?_, ?_⟩
  · linarith
  · have h1 : 4 * x + 3 * (4 * y) + 4 * (4 * z) = 4 * (x + 3 * y + 4 * z) := by ring
    rw [h1]
    have h2 : (x + 3 * y + 4 * z).sqrt ^ 2 = x + 3 * y + 4 * z := hsq
    rw [← h2]
    have h3 : 4 * (sqrt (x + 3 * y + 4 * z)) ^ 2 = (2 * sqrt (x + 3 * y + 4 * z)) ^ 2 := by ring
    rw [h3]
    rw [Nat.sqrt_eq' (2 * sqrt (x + 3 * y + 4 * z))]

lemma rep_sixteen_iff (n : ℕ) (hn : n % 2 = 0) : A335624_rep (16 * n) ↔ A335624_rep n := by
  constructor
  · exact rep_of_rep_sixteen_rev n hn
  · exact rep_of_rep_sixteen n

lemma A335624_eq_zero_iff_not_rep (n : ℕ) : A335624 n = 0 ↔ ¬ A335624_rep n := by
  dsimp [A335624, A335624_rep]
  simp_rw [sum_eq_zero_iff, mem_range]
  constructor
  · intro h ⟨x, y, z, w, hsum, hsq⟩
    have hx2 : x^2 ≤ n := by omega
    have hy2 : y^2 ≤ n := by omega
    have hz2 : z^2 ≤ n := by omega
    have hw2 : w^2 ≤ n := by omega
    have hx : x < sqrt n + 1 := Nat.lt_succ_of_le (le_sqrt'.2 hx2)
    have hy : y < sqrt n + 1 := Nat.lt_succ_of_le (le_sqrt'.2 hy2)
    have hz : z < sqrt n + 1 := Nat.lt_succ_of_le (le_sqrt'.2 hz2)
    have hw : w < sqrt n + 1 := Nat.lt_succ_of_le (le_sqrt'.2 hw2)
    have hspec := h x hx y hy z hz w hw
    have h_if : (if x^2 + y^2 + z^2 + w^2 = n ∧ (x + 3 * y + 4 * z).sqrt ^ 2 = x + 3 * y + 4 * z then 1 else 0) = 1 := if_pos ⟨hsum, hsq⟩
    rw [h_if] at hspec
    contradiction
  · intro h x hx y hy z hz w hw
    split_ifs with h_cond
    · exfalso
      exact h ⟨x, y, z, w, h_cond.1, h_cond.2⟩
    · rfl

lemma A335624_sixteen_iff (n : ℕ) (hn : n % 2 = 0) : A335624 (16 * n) = 0 ↔ A335624 n = 0 := by
  rw [A335624_eq_zero_iff_not_rep (16 * n)]
  rw [A335624_eq_zero_iff_not_rep n]
  rw [rep_sixteen_iff n hn]

def A335624_rep_bool_bound (n : ℕ) (B : ℕ) : Bool :=
  (List.range B).any fun x =>
  (List.range B).any fun y =>
  (List.range B).any fun z =>
  (List.range B).any fun w =>
    (x^2 + y^2 + z^2 + w^2 == n) &&
    (List.range (x + 3 * y + 4 * z + 1)).any fun s =>
      s^2 == x + 3 * y + 4 * z

lemma not_rep_of_not_rep_bool_bound (n : ℕ) (B : ℕ)
    (hB : ∀ x y z w, x^2 + y^2 + z^2 + w^2 = n → x < B ∧ y < B ∧ z < B ∧ w < B)
    (h_false : A335624_rep_bool_bound n B = false) : ¬ A335624_rep n := by
  intro ⟨x, y, z, w, hsum, hsq⟩
  have h_bound := hB x y z w hsum
  have h_true : A335624_rep_bool_bound n B = true := by
    dsimp [A335624_rep_bool_bound]
    rw [List.any_eq_true]
    refine ⟨x, ?_, ?_⟩
    · rw [List.mem_range]
      exact h_bound.1
    · rw [List.any_eq_true]
      refine ⟨y, ?_, ?_⟩
      · rw [List.mem_range]
        exact h_bound.2.1
      · rw [List.any_eq_true]
        refine ⟨z, ?_, ?_⟩
        · rw [List.mem_range]
          exact h_bound.2.2.1
        · rw [List.any_eq_true]
          refine ⟨w, ?_, ?_⟩
          · rw [List.mem_range]
            exact h_bound.2.2.2
          · rw [Bool.and_eq_true]
            constructor
            · rw [beq_iff_eq]
              exact hsum
            · rw [List.any_eq_true]
              refine ⟨(x + 3 * y + 4 * z).sqrt, ?_, ?_⟩
              · rw [List.mem_range]
                exact Nat.lt_succ_of_le (Nat.sqrt_le_self _)
              · rw [beq_iff_eq]
                exact hsq
  rw [h_true] at h_false
  contradiction

lemma not_rep_8 : ¬ A335624_rep 8 := by
  apply not_rep_of_not_rep_bool_bound 8 3
  · intro x y z w hsum
    have hx : x^2 ≤ 8 := by omega
    have hy : y^2 ≤ 8 := by omega
    have hz : z^2 ≤ 8 := by omega
    have hw : w^2 ≤ 8 := by omega
    have hx3 : x < 3 := by nlinarith
    have hy3 : y < 3 := by nlinarith
    have hz3 : z < 3 := by nlinarith
    have hw3 : w < 3 := by nlinarith
    exact ⟨hx3, hy3, hz3, hw3⟩
  · rfl

lemma not_rep_24 : ¬ A335624_rep 24 := by
  apply not_rep_of_not_rep_bool_bound 24 5
  · intro x y z w hsum
    have hx : x^2 ≤ 24 := by omega
    have hy : y^2 ≤ 24 := by omega
    have hz : z^2 ≤ 24 := by omega
    have hw : w^2 ≤ 24 := by omega
    have hx5 : x < 5 := by nlinarith
    have hy5 : y < 5 := by nlinarith
    have hz5 : z < 5 := by nlinarith
    have hw5 : w < 5 := by nlinarith
    exact ⟨hx5, hy5, hz5, hw5⟩
  · rfl

lemma not_rep_40 : ¬ A335624_rep 40 := by
  apply not_rep_of_not_rep_bool_bound 40 7
  · intro x y z w hsum
    have hx : x^2 ≤ 40 := by omega
    have hy : y^2 ≤ 40 := by omega
    have hz : z^2 ≤ 40 := by omega
    have hw : w^2 ≤ 40 := by omega
    have hx7 : x < 7 := by nlinarith
    have hy7 : y < 7 := by nlinarith
    have hz7 : z < 7 := by nlinarith
    have hw7 : w < 7 := by nlinarith
    exact ⟨hx7, hy7, hz7, hw7⟩
  · rfl
lemma not_rep_344 : ¬ A335624_rep 344 := by
  apply not_rep_of_not_rep_bool_bound 344 19
  · intro x y z w hsum
    have hx : x^2 ≤ 344 := by omega
    have hy : y^2 ≤ 344 := by omega
    have hz : z^2 ≤ 344 := by omega
    have hw : w^2 ≤ 344 := by omega
    have hx19 : x < 19 := by nlinarith
    have hy19 : y < 19 := by nlinarith
    have hz19 : z < 19 := by nlinarith
    have hw19 : w < 19 := by nlinarith
    exact ⟨hx19, hy19, hz19, hw19⟩
  · rfl

set_option maxHeartbeats 1000000
lemma sixteen_pow_mul_eight (k : ℕ) (m : ℕ) : 2 ^ (4 * k + 3) * m = 16 ^ k * (8 * m) := by
  rw [Nat.pow_add, Nat.pow_mul]
  ring

lemma A335624_eq_zero_of_rep_eq_zero (n : ℕ) (h : ¬ A335624_rep n) : A335624 n = 0 := by
  rwa [A335624_eq_zero_iff_not_rep]

lemma A335624_zero_of_form (k : ℕ) (m : ℕ) (hm : m = 1 ∨ m = 3 ∨ m = 5 ∨ m = 43) :
    A335624 (2 ^ (4 * k + 3) * m) = 0 := by
  induction' k with k ih
  · -- k = 0
    have h1 : 2 ^ (4 * 0 + 3) * m = 8 * m := by rfl
    rw [h1]
    rcases hm with rfl | rfl | rfl | rfl
    · exact A335624_eq_zero_of_rep_eq_zero 8 not_rep_8
    · exact A335624_eq_zero_of_rep_eq_zero 24 not_rep_24
    · exact A335624_eq_zero_of_rep_eq_zero 40 not_rep_40
    · exact A335624_eq_zero_of_rep_eq_zero 344 not_rep_344
  · -- inductive step
    have h_pow : 2 ^ (4 * (k + 1) + 3) * m = 16 * (2 ^ (4 * k + 3) * m) := by
      calc 2 ^ (4 * (k + 1) + 3) * m
        _ = 2 ^ (4 * k + 3 + 4) * m := by ring_nf
        _ = (2 ^ (4 * k + 3) * 2^4) * m := by rw [Nat.pow_add]
        _ = 16 * (2 ^ (4 * k + 3) * m) := by ring
    rw [h_pow]
    rw [A335624_sixteen_iff]
    · exact ih
    · -- we need to show 2 ^ (4 * k + 3) * m % 2 = 0
      have h_even : 2 ^ (4 * k + 3) * m = 2 * (2 ^ (4 * k + 2) * m) := by
        have h_add : 4 * k + 3 = (4 * k + 2) + 1 := by omega
        rw [h_add, Nat.pow_add]
        ring
      rw [h_even]
      rw [Nat.mul_mod_right]















