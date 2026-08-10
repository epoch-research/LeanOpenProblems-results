import FormalConjectures.Util.ProblemImports

set_option maxHeartbeats 1000000

open Nat Finset

/--
A335624: Number of ways to write $n$ as $x^2 + y^2 + z^2 + w^2$ with $x + 3y + 4z$ a square,
where $x, y, z, w$ are nonnegative integers.
-/
def A335624 (n : ℕ) : ℕ :=
  -- The variables x, y, z, w are bounded by sqrt(n), since they are non-negative.
  let B : ℕ := Nat.sqrt n + 1
  let R := range B

  R.sum fun x =>
  R.sum fun y =>
  R.sum fun z =>
  R.sum fun w =>
    if x^2 + y^2 + z^2 + w^2 = n
      -- The term x + 3*y + 4*z must be a perfect square.
      ∧ (let m := x + 3 * y + 4 * z; Nat.sqrt m ^ 2 = m)
    then 1 else 0

def A335624_rep (n : ℕ) : Prop :=
  ∃ x y z w : ℕ, x^2 + y^2 + z^2 + w^2 = n ∧ Nat.sqrt (x + 3 * y + 4 * z) ^ 2 = x + 3 * y + 4 * z

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
  have hsum1 : x1^2 + y1^2 + z1^2 + w1^2 = 4 * n := by
    have h_sub : (2*x1)^2 + (2*y1)^2 + (2*z1)^2 + (2*w1)^2 = 4 * (x1^2 + y1^2 + z1^2 + w1^2) := by ring
    have h_16 : 16 * n = 4 * (4 * n) := by ring
    rw [h_sub, h_16] at hsum
    exact Nat.eq_of_mul_eq_mul_left (by decide) hsum
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
  have hsum2 : x2^2 + y2^2 + z2^2 + w2^2 = n := by
    have h_sub : (2*x2)^2 + (2*y2)^2 + (2*z2)^2 + (2*w2)^2 = 4 * (x2^2 + y2^2 + z2^2 + w2^2) := by ring
    rw [h_sub] at hsum1
    exact Nat.eq_of_mul_eq_mul_left (by decide) hsum1
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

lemma sixteen_pow_mul_eight (k : ℕ) (m : ℕ) : 2 ^ (4 * k + 3) * m = 16 ^ k * (8 * m) := by
  rw [Nat.pow_add, Nat.pow_mul]
  ring

lemma A335624_eq_zero_of_rep_eq_zero (n : ℕ) (h : ¬ A335624_rep n) : A335624 n = 0 := by
  rwa [A335624_eq_zero_iff_not_rep]

lemma A335624_zero_of_form (k : ℕ) (m : ℕ) (hm : m = 1 ∨ m = 3 ∨ m = 5 ∨ m = 43) :
    A335624 (2 ^ (4 * k + 3) * m) = 0 := by
  induction' k with k ih
  · have h1 : 2 ^ (4 * 0 + 3) * m = 8 * m := by rfl
    rw [h1]
    rcases hm with rfl | rfl | rfl | rfl
    · exact A335624_eq_zero_of_rep_eq_zero 8 not_rep_8
    · exact A335624_eq_zero_of_rep_eq_zero 24 not_rep_24
    · exact A335624_eq_zero_of_rep_eq_zero 40 not_rep_40
    · exact A335624_eq_zero_of_rep_eq_zero 344 not_rep_344
  · have h_pow : 2 ^ (4 * (k + 1) + 3) * m = 16 * (2 ^ (4 * k + 3) * m) := by
      calc 2 ^ (4 * (k + 1) + 3) * m
        _ = 2 ^ (4 * k + 3 + 4) * m := by ring_nf
        _ = (2 ^ (4 * k + 3) * 2^4) * m := by rw [Nat.pow_add]
        _ = 16 * (2 ^ (4 * k + 3) * m) := by ring
    rw [h_pow]
    rw [A335624_sixteen_iff]
    · exact ih
    · have h_even : 2 ^ (4 * k + 3) * m = 2 * (2 ^ (4 * k + 2) * m) := by
        have h_add : 4 * k + 3 = (4 * k + 2) + 1 := by omega
        rw [h_add, Nat.pow_add]
        ring
      rw [h_even]
      rw [Nat.mul_mod_right]

lemma A335624_eq_zero_of_sixteen_eq_zero (n : ℕ) (h : A335624 (16 * n) = 0) : A335624 n = 0 := by
  rw [A335624_eq_zero_iff_not_rep] at h ⊢
  intro h_rep
  exact h (rep_of_rep_sixteen n h_rep)

/--
Conjecture: a(n) = 0 if and only if n has the form ^{4k+3} \cdot m$ (k >= 0 and m = 1, 3, 5, 43).
This is the main part of the OEIS conjecture.
-/
theorem A335624_conjecture_zero_iff (n : ℕ) :
  A335624 n = 0 ↔
    ∃ (k : ℕ) (m : ℕ),
      m ∈ ({1, 3, 5, 43} : Set ℕ) ∧
      n = 2 ^ (4 * k + 3) * m := by
  constructor
  · intro h
    induction' n using Nat.strong_induction_on with n ih
    by_cases hn0 : n = 0
    · subst hn0
      have h0 : A335624 0 = 1 := by decide
      rw [h0] at h
      contradiction
    · by_cases h16 : 16 ∣ n
      · obtain ⟨n', rfl⟩ := h16
        have hn' : n' < 16 * n' := by
          have hn'_gt : n' > 0 := by
            by_contra hn'0
            have hn'0 : n' = 0 := by omega
            subst hn'0
            simp only [mul_zero, not_true_eq_false] at hn0
          omega
        have hn'_zero : A335624 n' = 0 := A335624_eq_zero_of_sixteen_eq_zero n' h
        have ih' := ih n' hn' hn'_zero
        obtain ⟨k, m, hm, rfl⟩ := ih'
        refine ⟨k + 1, m, hm, ?_⟩
        calc 16 * (2 ^ (4 * k + 3) * m)
          _ = (2^4 * 2 ^ (4 * k + 3)) * m := by ring
          _ = 2 ^ (4 + (4 * k + 3)) * m := by rw [← Nat.pow_add]
          _ = 2 ^ (4 * (k + 1) + 3) * m := by
            congr 1
            congr 1
            omega
      · by_cases hn_lt : n < 345
        · interval_cases n
          · contradiction
          · exfalso
            have h_rep : A335624_rep 1 := by use 0, 0, 0, 1; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 1).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 2 := by use 0, 0, 1, 1; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 2).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 3 := by use 1, 1, 0, 1; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 3).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 4 := by use 0, 0, 0, 2; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 4).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 5 := by use 0, 0, 1, 2; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 5).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 6 := by use 1, 0, 2, 1; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 6).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 7 := by use 2, 1, 1, 1; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 7).mp h h_rep
          · refine ⟨0, 1, by decide, by decide⟩
          · exfalso
            have h_rep : A335624_rep 9 := by use 0, 0, 0, 3; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 9).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 10 := by use 0, 0, 1, 3; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 10).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 11 := by use 1, 1, 0, 3; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 11).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 12 := by use 1, 1, 3, 1; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 12).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 13 := by use 0, 3, 0, 2; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 13).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 14 := by use 1, 0, 2, 3; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 14).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 15 := by use 1, 1, 3, 2; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 15).mp h h_rep
          · exfalso; apply h16; decide
          · exfalso
            have h_rep : A335624_rep 17 := by use 0, 0, 1, 4; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 17).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 18 := by use 0, 3, 0, 3; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 18).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 19 := by use 3, 3, 1, 0; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 19).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 20 := by use 0, 0, 4, 2; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 20).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 21 := by use 0, 4, 1, 2; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 21).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 22 := by use 2, 1, 1, 4; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 22).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 23 := by use 3, 3, 1, 2; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 23).mp h h_rep
          · refine ⟨0, 3, by decide, by decide⟩
          · exfalso
            have h_rep : A335624_rep 25 := by use 0, 0, 0, 5; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 25).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 26 := by use 0, 0, 1, 5; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 26).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 27 := by use 1, 1, 0, 5; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 27).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 28 := by use 2, 2, 2, 4; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 28).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 29 := by use 0, 3, 4, 2; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 29).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 30 := by use 1, 0, 2, 5; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 30).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 31 := by use 2, 1, 1, 5; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 31).mp h h_rep
          · exfalso; apply h16; decide
          · exfalso
            have h_rep : A335624_rep 33 := by use 0, 4, 1, 4; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 33).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 34 := by use 0, 3, 0, 5; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 34).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 35 := by use 1, 4, 3, 3; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 35).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 36 := by use 0, 0, 0, 6; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 36).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 37 := by use 0, 0, 1, 6; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 37).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 38 := by use 1, 0, 6, 1; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 38).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 39 := by use 2, 1, 5, 3; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 39).mp h h_rep
          · refine ⟨0, 5, by decide, by decide⟩
          · exfalso
            have h_rep : A335624_rep 41 := by use 0, 0, 4, 5; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 41).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 42 := by use 0, 4, 1, 5; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 42).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 43 := by use 4, 3, 3, 3; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 43).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 44 := by use 3, 3, 1, 5; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 44).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 45 := by use 0, 3, 0, 6; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 45).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 46 := by use 1, 0, 6, 3; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 46).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 47 := by use 1, 1, 3, 6; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 47).mp h h_rep
          · exfalso; apply h16; decide
          · exfalso
            have h_rep : A335624_rep 49 := by use 0, 0, 0, 7; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 49).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 50 := by use 0, 0, 1, 7; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 50).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 51 := by use 0, 7, 1, 1; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 51).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 52 := by use 0, 0, 4, 6; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 52).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 53 := by use 0, 4, 1, 6; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 53).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 54 := by use 0, 7, 1, 2; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 54).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 55 := by use 1, 5, 5, 2; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 55).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 56 := by use 0, 4, 6, 2; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 56).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 57 := by use 2, 2, 7, 0; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 57).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 58 := by use 0, 3, 0, 7; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 58).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 59 := by use 0, 7, 1, 3; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 59).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 60 := by use 1, 1, 3, 7; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 60).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 61 := by use 0, 3, 4, 6; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 61).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 62 := by use 1, 0, 6, 5; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 62).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 63 := by use 3, 3, 6, 3; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 63).mp h h_rep
          · exfalso; apply h16; decide
          · exfalso
            have h_rep : A335624_rep 65 := by use 0, 0, 1, 8; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 65).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 66 := by use 0, 4, 1, 7; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 66).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 67 := by use 1, 1, 8, 1; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 67).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 68 := by use 0, 4, 6, 4; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 68).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 69 := by use 1, 0, 2, 8; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 69).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 70 := by use 1, 1, 8, 2; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 70).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 71 := by use 3, 6, 1, 5; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 71).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 72 := by use 2, 6, 4, 4; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 72).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 73 := by use 0, 3, 0, 8; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 73).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 74 := by use 0, 3, 4, 7; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 74).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 75 := by use 0, 7, 1, 5; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 75).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 76 := by use 1, 5, 5, 5; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 76).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 77 := by use 0, 4, 6, 5; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 77).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 78 := by use 3, 2, 4, 7; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 78).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 79 := by use 2, 1, 5, 7; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 79).mp h h_rep
          · exfalso; apply h16; decide
          · exfalso
            have h_rep : A335624_rep 81 := by use 0, 0, 0, 9; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 81).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 82 := by use 0, 0, 1, 9; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 82).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 83 := by use 1, 1, 0, 9; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 83).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 84 := by use 4, 0, 8, 2; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 84).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 85 := by use 0, 0, 9, 2; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 85).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 86 := by use 0, 7, 1, 6; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 86).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 87 := by use 1, 5, 5, 6; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 87).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 88 := by use 0, 4, 6, 6; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 88).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 89 := by use 0, 3, 4, 8; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 89).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 90 := by use 0, 0, 9, 3; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 90).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 91 := by use 1, 1, 8, 5; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 91).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 92 := by use 1, 1, 3, 9; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 92).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 93 := by use 2, 2, 2, 9; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 93).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 94 := by use 2, 1, 5, 8; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 94).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 95 := by use 1, 9, 2, 3; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 95).mp h h_rep
          · exfalso; apply h16; decide
          · exfalso
            have h_rep : A335624_rep 97 := by use 0, 0, 4, 9; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 97).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 98 := by use 0, 4, 1, 9; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 98).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 99 := by use 0, 7, 1, 7; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 99).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 100 := by use 0, 0, 0, 10; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 100).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 101 := by use 0, 0, 1, 10; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 101).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 102 := by use 0, 7, 7, 2; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 102).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 103 := by use 3, 3, 6, 7; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 103).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 104 := by use 8, 0, 2, 6; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 104).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 105 := by use 1, 0, 2, 10; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 105).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 106 := by use 0, 0, 9, 5; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 106).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 107 := by use 0, 7, 7, 3; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 107).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 108 := by use 5, 9, 1, 1; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 108).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 109 := by use 0, 3, 0, 10; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 109).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 110 := by use 0, 3, 10, 1; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 110).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 111 := by use 1, 1, 3, 10; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 111).mp h h_rep
          · exfalso; apply h16; decide
          · exfalso
            have h_rep : A335624_rep 113 := by use 0, 3, 10, 2; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 113).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 114 := by use 0, 7, 1, 8; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 114).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 115 := by use 1, 1, 8, 7; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 115).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 116 := by use 0, 0, 4, 10; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 116).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 117 := by use 0, 0, 9, 6; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 117).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 118 := by use 0, 3, 10, 3; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 118).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 119 := by use 2, 9, 5, 3; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 119).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 120 := by use 2, 6, 4, 8; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 120).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 121 := by use 0, 0, 0, 11; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 121).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 122 := by use 0, 0, 1, 11; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 122).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 123 := by use 0, 7, 7, 5; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 123).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 124 := by use 5, 1, 7, 7; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 124).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 125 := by use 0, 3, 4, 10; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 125).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 126 := by use 1, 0, 2, 11; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 126).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 127 := by use 2, 1, 1, 11; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 127).mp h h_rep
          · exfalso; apply h16; decide
          · exfalso
            have h_rep : A335624_rep 129 := by use 1, 8, 0, 8; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 129).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 130 := by use 0, 0, 9, 7; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 130).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 131 := by use 0, 7, 1, 9; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 131).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 132 := by use 1, 1, 3, 11; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 132).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 133 := by use 0, 4, 6, 9; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 133).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 134 := by use 0, 3, 10, 5; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 134).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 135 := by use 1, 9, 2, 7; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 135).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 136 := by use 6, 10, 0, 0; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 136).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 137 := by use 0, 0, 4, 11; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 137).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 138 := by use 0, 4, 1, 11; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 138).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 139 := by use 3, 11, 0, 3; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 139).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 140 := by use 3, 3, 1, 11; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 140).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 141 := by use 0, 11, 4, 2; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 141).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 142 := by use 2, 1, 11, 4; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 142).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 143 := by use 3, 6, 7, 7; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 143).mp h h_rep
          · exfalso; apply h16; decide
          · exfalso
            have h_rep : A335624_rep 145 := by use 0, 0, 1, 12; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 145).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 146 := by use 0, 3, 4, 11; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 146).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 147 := by use 0, 7, 7, 7; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 147).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 148 := by use 0, 12, 0, 2; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 148).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 149 := by use 1, 0, 2, 12; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 149).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 150 := by use 0, 7, 1, 10; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 150).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 151 := by use 1, 5, 5, 10; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 151).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 152 := by use 0, 4, 6, 10; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 152).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 153 := by use 0, 3, 0, 12; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 153).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 154 := by use 0, 8, 3, 9; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 154).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 155 := by use 1, 1, 3, 12; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 155).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 156 := by use 2, 2, 2, 12; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 156).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 157 := by use 2, 2, 7, 10; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 157).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 158 := by use 0, 3, 10, 7; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 158).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 159 := by use 2, 9, 5, 7; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 159).mp h h_rep
          · exfalso; apply h16; decide
          · exfalso
            have h_rep : A335624_rep 161 := by use 0, 4, 1, 12; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 161).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 162 := by use 0, 0, 9, 9; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 162).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 163 := by use 1, 9, 9, 0; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 163).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 164 := by use 0, 8, 10, 0; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 164).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 165 := by use 0, 8, 10, 1; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 165).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 166 := by use 1, 1, 8, 10; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 166).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 167 := by use 1, 9, 2, 9; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 167).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 168 := by use 0, 8, 10, 2; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 168).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 169 := by use 0, 0, 0, 13; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 169).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 170 := by use 0, 0, 1, 13; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 170).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 171 := by use 0, 7, 1, 11; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 171).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 172 := by use 1, 5, 5, 11; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 172).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 173 := by use 0, 3, 10, 8; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 173).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 174 := by use 1, 0, 2, 13; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 174).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 175 := by use 2, 1, 1, 13; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 175).mp h h_rep
          · exfalso; apply h16; decide
          · exfalso
            have h_rep : A335624_rep 177 := by use 2, 5, 2, 12; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 177).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 178 := by use 0, 3, 0, 13; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 178).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 179 := by use 0, 7, 7, 9; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 179).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 180 := by use 0, 8, 10, 4; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 180).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 181 := by use 0, 0, 9, 10; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 181).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 182 := by use 1, 8, 6, 9; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 182).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 183 := by use 3, 7, 10, 5; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 183).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 184 := by use 2, 10, 8, 4; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 184).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 185 := by use 0, 0, 4, 13; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 185).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 186 := by use 0, 4, 1, 13; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 186).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 187 := by use 1, 1, 8, 11; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 187).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 188 := by use 1, 9, 9, 5; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 188).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 189 := by use 0, 4, 13, 2; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 189).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 190 := by use 0, 3, 10, 9; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 190).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 191 := by use 2, 9, 5, 9; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 191).mp h h_rep
          · exfalso; apply h16; decide
          · exfalso
            have h_rep : A335624_rep 193 := by use 0, 12, 0, 7; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 193).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 194 := by use 0, 3, 4, 13; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 194).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 195 := by use 1, 4, 3, 13; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 195).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 196 := by use 0, 0, 0, 14; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 196).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 197 := by use 0, 0, 1, 14; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 197).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 198 := by use 0, 7, 7, 10; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 198).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 199 := by use 1, 9, 9, 6; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 199).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 200 := by use 0, 8, 10, 6; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 200).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 201 := by use 0, 4, 13, 4; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 201).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 202 := by use 0, 0, 9, 11; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 202).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 203 := by use 1, 12, 3, 7; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 203).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 204 := by use 2, 2, 14, 0; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 204).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 205 := by use 0, 3, 0, 14; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 205).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 206 := by use 1, 0, 6, 13; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 206).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 207 := by use 1, 1, 3, 14; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 207).mp h h_rep
          · exfalso; apply h16; decide
          · exfalso
            have h_rep : A335624_rep 209 := by use 0, 3, 10, 10; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 209).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 210 := by use 0, 4, 13, 5; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 210).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 211 := by use 3, 7, 3, 12; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 211).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 212 := by use 0, 0, 4, 14; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 212).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 213 := by use 0, 4, 1, 14; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 213).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 214 := by use 2, 5, 8, 11; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 214).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 215 := by use 1, 13, 6, 3; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 215).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 216 := by use 12, 0, 6, 6; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 216).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 217 := by use 0, 8, 3, 12; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 217).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 218 := by use 0, 11, 4, 9; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 218).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 219 := by use 0, 7, 1, 13; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 219).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 220 := by use 1, 5, 5, 13; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 220).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 221 := by use 0, 3, 4, 14; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 221).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 222 := by use 1, 4, 3, 14; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 222).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 223 := by use 3, 3, 6, 13; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 223).mp h h_rep
          · exfalso; apply h16; decide
          · exfalso
            have h_rep : A335624_rep 225 := by use 0, 0, 0, 15; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 225).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 226 := by use 0, 0, 1, 15; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 226).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 227 := by use 0, 15, 1, 1; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 227).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 228 := by use 0, 8, 10, 8; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 228).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 229 := by use 0, 12, 7, 6; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 229).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 230 := by use 0, 3, 10, 11; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 230).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 231 := by use 1, 1, 15, 2; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 231).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 232 := by use 2, 10, 8, 8; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 232).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 233 := by use 1, 0, 6, 14; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 233).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 234 := by use 0, 3, 0, 15; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 234).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 235 := by use 0, 15, 1, 3; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 235).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 236 := by use 1, 1, 3, 15; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 236).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 237 := by use 0, 11, 4, 10; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 237).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 238 := by use 3, 2, 0, 15; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 238).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 239 := by use 3, 7, 10, 9; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 239).mp h h_rep
          · exfalso; apply h16; decide
          · exfalso
            have h_rep : A335624_rep 241 := by use 0, 0, 4, 15; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 241).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 242 := by use 0, 4, 1, 15; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 242).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 243 := by use 1, 1, 15, 4; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 243).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 244 := by use 0, 12, 0, 10; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 244).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 245 := by use 0, 8, 10, 9; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 245).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 246 := by use 0, 7, 1, 14; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 246).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 247 := by use 1, 5, 5, 14; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 247).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 248 := by use 0, 4, 6, 14; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 248).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 249 := by use 0, 4, 13, 8; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 249).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 250 := by use 0, 0, 9, 13; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 250).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 251 := by use 0, 15, 1, 5; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 251).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 252 := by use 1, 1, 15, 5; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 252).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 253 := by use 0, 3, 10, 12; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 253).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 254 := by use 1, 12, 3, 10; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 254).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 255 := by use 1, 9, 2, 13; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 255).mp h h_rep
          · exfalso; apply h16; decide
          · exfalso
            have h_rep : A335624_rep 257 := by use 0, 0, 1, 16; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 257).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 258 := by use 0, 11, 4, 11; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 258).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 259 := by use 3, 15, 4, 3; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 259).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 260 := by use 0, 0, 16, 2; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 260).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 261 := by use 1, 0, 2, 16; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 261).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 262 := by use 0, 15, 1, 6; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 262).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 263 := by use 1, 1, 15, 6; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 263).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 264 := by use 0, 8, 10, 10; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 264).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 265 := by use 0, 0, 16, 3; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 265).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 266 := by use 0, 4, 13, 9; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 266).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 267 := by use 0, 7, 7, 13; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 267).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 268 := by use 2, 2, 2, 16; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 268).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 269 := by use 0, 8, 3, 14; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 269).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 270 := by use 1, 5, 12, 10; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 270).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 271 := by use 3, 6, 1, 15; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 271).mp h h_rep
          · exfalso; apply h16; decide
          · exfalso
            have h_rep : A335624_rep 273 := by use 0, 4, 1, 16; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 273).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 274 := by use 0, 7, 15, 0; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 274).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 275 := by use 0, 7, 1, 15; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 275).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 276 := by use 0, 16, 4, 2; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 276).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 277 := by use 0, 0, 9, 14; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 277).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 278 := by use 0, 3, 10, 13; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 278).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 279 := by use 2, 9, 5, 13; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 279).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 280 := by use 4, 8, 2, 14; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 280).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 281 := by use 0, 0, 16, 5; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 281).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 282 := by use 1, 4, 3, 16; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 282).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 283 := by use 0, 7, 15, 3; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 283).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 284 := by use 1, 9, 9, 11; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 284).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 285 := by use 0, 4, 13, 10; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 285).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 286 := by use 1, 8, 14, 5; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 286).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 287 := by use 1, 13, 6, 9; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 287).mp h h_rep
          · exfalso; apply h16; decide
          · exfalso
            have h_rep : A335624_rep 289 := by use 0, 0, 0, 17; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 289).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 290 := by use 0, 0, 1, 17; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 290).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 291 := by use 1, 1, 0, 17; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 291).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 292 := by use 0, 0, 16, 6; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 292).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 293 := by use 0, 12, 7, 10; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 293).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 294 := by use 0, 7, 7, 14; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 294).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 295 := by use 2, 1, 1, 17; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 295).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 296 := by use 4, 12, 6, 10; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 296).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 297 := by use 0, 16, 4, 5; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 297).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 298 := by use 0, 3, 0, 17; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 298).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 299 := by use 0, 7, 15, 5; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 299).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 300 := by use 1, 1, 3, 17; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 300).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 301 := by use 0, 11, 12, 6; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 301).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 302 := by use 1, 12, 11, 6; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 302).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 303 := by use 1, 17, 3, 2; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 303).mp h h_rep
          · exfalso; apply h16; decide
          · exfalso
            have h_rep : A335624_rep 305 := by use 0, 0, 4, 17; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 305).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 306 := by use 0, 0, 9, 15; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 306).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 307 := by use 0, 15, 1, 9; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 307).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 308 := by use 0, 4, 6, 16; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 308).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 309 := by use 2, 13, 10, 6; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 309).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 310 := by use 0, 7, 15, 6; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 310).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 311 := by use 1, 9, 2, 15; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 311).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 312 := by use 2, 6, 4, 16; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 312).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 313 := by use 0, 12, 0, 13; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 313).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 314 := by use 0, 3, 4, 17; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 314).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 315 := by use 0, 15, 9, 3; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 315).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 316 := by use 6, 6, 10, 12; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 316).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 317 := by use 3, 10, 12, 8; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 317).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 318 := by use 2, 5, 8, 15; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 318).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 319 := by use 2, 1, 5, 17; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 319).mp h h_rep
          · exfalso; apply h16; decide
          · exfalso
            have h_rep : A335624_rep 321 := by use 0, 16, 4, 7; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 321).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 322 := by use 0, 15, 9, 4; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 322).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 323 := by use 0, 7, 7, 15; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 323).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 324 := by use 0, 0, 0, 18; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 324).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 325 := by use 0, 0, 1, 18; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 325).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 326 := by use 0, 15, 1, 10; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 326).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 327 := by use 1, 1, 15, 10; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 327).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 328 := by use 8, 16, 2, 2; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 328).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 329 := by use 0, 4, 13, 12; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 329).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 330 := by use 1, 12, 11, 8; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 330).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 331 := by use 0, 15, 9, 5; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 331).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 332 := by use 1, 9, 9, 13; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 332).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 333 := by use 0, 3, 0, 18; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 333).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 334 := by use 0, 3, 10, 15; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 334).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 335 := by use 1, 1, 3, 18; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 335).mp h h_rep
          · exfalso; apply h16; decide
          · exfalso
            have h_rep : A335624_rep 337 := by use 0, 0, 9, 16; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 337).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 338 := by use 0, 7, 15, 8; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 338).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 339 := by use 0, 7, 1, 17; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 339).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 340 := by use 0, 0, 4, 18; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 340).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 341 := by use 0, 4, 1, 18; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 341).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 342 := by use 0, 3, 18, 3; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 342).mp h h_rep
          · exfalso
            have h_rep : A335624_rep 343 := by use 2, 17, 7, 1; constructor <;> norm_num
            exact (A335624_eq_zero_iff_not_rep 343).mp h h_rep
          · refine ⟨0, 43, by decide, by decide⟩
        · have h_goal : False := by sorry
  · intro ⟨k, m, hm, hn⟩
    have hm_or : m = 1 ∨ m = 3 ∨ m = 5 ∨ m = 43 := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
      rcases hm with rfl | rfl | rfl | rfl
      · left; rfl
      · right; left; rfl
      · right; right; left; rfl
      · right; right; right; rfl
    rw [hn]
    exact A335624_zero_of_form k m hm_or
