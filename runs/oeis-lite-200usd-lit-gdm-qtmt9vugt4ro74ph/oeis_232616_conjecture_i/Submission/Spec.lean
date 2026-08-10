import FormalConjectures.Util.ProblemImports
set_option linter.style.copyright.formalConjectures false
set_option linter.style.namespace false

set_option linter.all false

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 5000
set_option max_memory 64424509440
set_option interpreter.prefer_native true

open Finset ZMod Nat Set Classical

def A232616_prop (n m : ℕ) [NeZero n] : Prop :=
  (univ : Finset (ZMod n)) = (Finset.Icc 1 m).image fun k ↦ (Nat.cast (2 ^ k - k) : ZMod n)

noncomputable def A232616 (n : ℕ) : ℕ :=
  if h : n = 0 then 0
  else
    have : NeZero n := NeZero.mk h
    let S : Set ℕ := { m : ℕ | A232616_prop n m }
    sInf S

def powMod588 : ℕ → ZMod 550172
  | 0 => 1
  | j + 1 => powMod588 j * 433896

theorem lemma_pow (j : ℕ) : ((2 ^ (588 * j) : ℕ) : ZMod 550172) = powMod588 j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have h1 : 588 * (j + 1) = 588 * j + 588 := by omega
    rw [h1, pow_add, Nat.cast_mul, ih, Nat.cast_pow]
    have h2 : (Nat.cast 2 : ZMod 550172) ^ 588 = 433896 := by decide
    rw [h2]
    rfl

lemma dvd_of_zmod_eq_zero_spec {g a : ℕ} [NeZero g] (h : (a : ZMod g) = 0) : g ∣ a := by
  have h_val : (a : ZMod g).val = 0 := by rw [h, ZMod.val_zero]
  rw [ZMod.val_natCast] at h_val
  exact Nat.dvd_of_mod_eq_zero h_val

lemma dvd_of_eq_spec {g a b : ℕ} [NeZero g] (ha : b ≤ a) (h : (a : ZMod g) = (b : ZMod g)) : g ∣ a - b := by
  have h_eq : ((a - b : ℕ) : ZMod g) = 0 := by
    rw [Nat.cast_sub ha, h, sub_self]
  exact dvd_of_zmod_eq_zero_spec h_eq

lemma two_pow_le (a : ℕ) : 2 * a ≤ 2 ^ a := by
  induction a with
  | zero => omega
  | succ a ih =>
    rcases a with _ | a'
    · simp
    · have h_pow : 2 ^ (a' + 2) = 2 ^ (a' + 1) + 2 ^ (a' + 1) := by ring
      rw [h_pow]
      have h_two : 2 ≤ 2 ^ (a' + 1) := by
        have : 2 ^ 1 ≤ 2 ^ (a' + 1) := Nat.pow_le_pow_right (by decide) (by omega)
        exact this
      omega

theorem step_down (n g T : ℕ) [NeZero n] [NeZero g] (hg : g = Nat.gcd T n)
    (pow_congr : ∀ a b, n ≤ a → ((2 ^ (a + b * T) : ℕ) : ZMod n) = ((2 ^ a : ℕ) : ZMod n))
    (h_prev : ∀ y : ZMod g, ∃ a : ℕ, n ≤ a ∧ ((2^a - a : ℕ) : ZMod g) = y) :
    ∀ y : ZMod n, ∃ k : ℕ, n ≤ k ∧ ((2^k - k : ℕ) : ZMod n) = y := by
  intro y
  let y_g : ZMod g := (y.val : ZMod g)
  rcases h_prev y_g with ⟨a, ha, ha_eq⟩
  have hy_lt : y.val < n := val_lt y
  have ha1 : 1 ≤ a := by omega
  have h_exp_le : a - 1 ≤ 2 ^ a - a := by
    have h_two_a := two_pow_le a
    omega
  have hy_le : y.val ≤ 2 ^ a - a := by omega
  have h_dvd : g ∣ 2 ^ a - a - y.val := dvd_of_eq_spec hy_le ha_eq
  rcases h_dvd with ⟨q, h_q⟩
  let B : ℤ := q * T.gcdA n
  let b_zmod : ZMod n := (B : ZMod n)
  let b := b_zmod.val
  have hb_eq : (b : ZMod n) = (B : ZMod n) := natCast_zmod_val b_zmod
  have h_bezout : (g : ZMod n) = (T : ZMod n) * (T.gcdA n : ZMod n) := by
    have h_comm : g = Nat.gcd T n := hg
    have h_bezout_int := Nat.gcd_eq_gcd_ab T n
    rw [← h_comm] at h_bezout_int
    have h_cast : ((g : ℤ) : ZMod n) = (((T : ℤ) * T.gcdA n + (n : ℤ) * T.gcdB n : ℤ) : ZMod n) := by rw [h_bezout_int]
    push_cast at h_cast
    have hn0 : (n : ZMod n) = 0 := natCast_self n
    rw [hn0] at h_cast
    simp at h_cast
    rw [h_cast]
  have h_prod : (T : ZMod n) * (b : ZMod n) = (g : ZMod n) * (q : ZMod n) := by
    rw [hb_eq]
    dsimp only [B]
    push_cast
    rw [show (T : ZMod n) * ((q : ZMod n) * (T.gcdA n : ZMod n)) = ((T : ZMod n) * (T.gcdA n : ZMod n)) * (q : ZMod n) by ring]
    rw [← h_bezout]
  have h_nat_eq : g * q = 2 ^ a - a - y.val := h_q.symm
  have h_cast_nat : ((g * q : ℕ) : ZMod n) = ((2 ^ a - a - y.val : ℕ) : ZMod n) := by
    rw [← h_q]
  rw [Nat.cast_mul] at h_cast_nat
  rw [h_cast_nat] at h_prod
  let k := a + b * T
  use k
  constructor
  · have h_le_k : a ≤ k := by omega
    omega
  · have hk_le : k ≤ 2 ^ k := le_of_lt (Nat.lt_pow_self (by decide : 1 < 2))
    rw [Nat.cast_sub hk_le]
    have h_pow : ((2 ^ k : ℕ) : ZMod n) = ((2 ^ a : ℕ) : ZMod n) := by
      exact pow_congr a b ha
    rw [h_pow]
    have h_nat_sub : 2 ^ a - a = (2 ^ a - a - y.val) + y.val := by omega
    have h_cast_sub2 : ((2 ^ a - a : ℕ) : ZMod n) = ((2 ^ a - a - y.val : ℕ) : ZMod n) + (y.val : ZMod n) := by
      nth_rw 1 [h_nat_sub]
      rw [Nat.cast_add]
    have hy_val : (y.val : ZMod n) = y := natCast_zmod_val y
    rw [hy_val] at h_cast_sub2
    rw [← h_prod] at h_cast_sub2
    have ha_le2 : a ≤ 2 ^ a := le_of_lt (Nat.lt_pow_self (by decide : 1 < 2))
    rw [Nat.cast_sub ha_le2] at h_cast_sub2
    have h_final : ((2 ^ a : ℕ) : ZMod n) - ((a + b * T : ℕ) : ZMod n) = y := by
      have h_temp : ((2 ^ a : ℕ) : ZMod n) - (a : ZMod n) - (b : ZMod n) * (T : ZMod n) = y := by
        rw [h_cast_sub2]
        ring
      have h_rw : ((2 ^ a : ℕ) : ZMod n) - ((a + b * T : ℕ) : ZMod n) = ((2 ^ a : ℕ) : ZMod n) - (a : ZMod n) - (b : ZMod n) * (T : ZMod n) := by
        rw [Nat.cast_add, Nat.cast_mul]
        ring
      rw [h_rw]
      exact h_temp
    exact h_final

lemma shift_sol (n P m : ℕ) [NeZero n] (hm : n ∣ m) (hP1 : 1 ≤ P)
    (pow_congr : ∀ a b, n ≤ a → ((2 ^ (a + b * P) : ℕ) : ZMod n) = ((2 ^ a : ℕ) : ZMod n))
    (h_sol : ∀ y : ZMod n, ∃ a : ℕ, n ≤ a ∧ ((2^a - a : ℕ) : ZMod n) = y) :
    ∀ y : ZMod n, ∃ k : ℕ, m ≤ k ∧ ((2^k - k : ℕ) : ZMod n) = y := by
  intro y
  rcases h_sol y with ⟨a, ha, ha_eq⟩
  let b := m
  let k := a + b * P
  use k
  constructor
  · have h_le1 : m ≤ b * P := by
      have : m * 1 ≤ b * P := Nat.mul_le_mul_left m hP1
      rwa [mul_one] at this
    omega
  · have hk_le : k ≤ 2 ^ k := le_of_lt (Nat.lt_pow_self (by decide : 1 < 2))
    have ha_le : a ≤ 2 ^ a := le_of_lt (Nat.lt_pow_self (by decide : 1 < 2))
    rw [Nat.cast_sub hk_le]
    rw [Nat.cast_sub ha_le] at ha_eq
    rw [pow_congr a b ha]
    have h_dvd : n ∣ b * P := by
      change n ∣ m * P
      rcases hm with ⟨d, hd⟩
      use d * P
      rw [hd]
      ring
    have h_cast : ((b * P : ℕ) : ZMod n) = 0 := by
      rcases h_dvd with ⟨d, hd⟩
      rw [hd, Nat.cast_mul, show (n : ZMod n) = 0 from natCast_self n, zero_mul]
    have hk_mod : ((k : ℕ) : ZMod n) = ((a : ℕ) : ZMod n) := by
      change ((a + b * P : ℕ) : ZMod n) = ((a : ℕ) : ZMod n)
      rw [Nat.cast_add, h_cast, add_zero]
    rw [hk_mod]
    exact ha_eq

lemma pow_two_zmod2_eq_zero {x : ℕ} (hx : 1 ≤ x) :
    ((2 ^ x : ℕ) : ZMod 2) = 0 := by
  have h_eq : x = (x - 1) + 1 := by omega
  nth_rw 1 [h_eq]
  rw [pow_add, pow_one, Nat.cast_mul]
  have h_two : (((2 : ℕ) : ZMod 2) = 0) := rfl
  rw [h_two, mul_zero]

lemma pow_two_zmod4_eq_zero {x : ℕ} (hx : 2 ≤ x) :
    ((2 ^ x : ℕ) : ZMod 4) = 0 := by
  have h_eq : x = (x - 2) + 2 := by omega
  nth_rw 1 [h_eq]
  rw [pow_add, Nat.cast_mul]
  have h_four : ((2 ^ 2 : ℕ) : ZMod 4) = 0 := rfl
  rw [h_four, mul_zero]

lemma pow_congr_2_tot (a b : ℕ) (ha : 2 ≤ a) :
    ((2 ^ (a + b * 1) : ℕ) : ZMod 2) = ((2 ^ a : ℕ) : ZMod 2) := by
  have h1 : 1 ≤ a + b * 1 := by omega
  have h2 : 1 ≤ a := by omega
  rw [pow_two_zmod2_eq_zero h1, pow_two_zmod2_eq_zero h2]

lemma pow_congr_4_tot (a b : ℕ) (ha : 4 ≤ a) :
    ((2 ^ (a + b * 2) : ℕ) : ZMod 4) = ((2 ^ a : ℕ) : ZMod 4) := by
  have h1 : 2 ≤ a + b * 2 := by omega
  have h2 : 2 ≤ a := by omega
  rw [pow_two_zmod4_eq_zero h1, pow_two_zmod4_eq_zero h2]

theorem pow_congr_28_tot (a b : ℕ) (ha : 28 ≤ a) :
    ((2 ^ (a + b * 12) : ℕ) : ZMod 28) = ((2 ^ a : ℕ) : ZMod 28) := by
  have h_sub : 2 ≤ a := by omega
  have h_eq : a = (a - 2) + 2 := by omega
  induction b with
  | zero =>
    simp
  | succ b ih =>
    have h1 : a + (b + 1) * 12 = (a + b * 12) + 12 := by omega
    rw [h1, pow_add, Nat.cast_mul, ih]
    have h_pow_a : 2 ^ a = 2 ^ (a - 2) * 4 := by
      nth_rw 1 [h_eq]
      rw [pow_add]
      rfl
    rw [h_pow_a]
    rw [Nat.cast_mul]
    rw [mul_assoc]
    have h_inner : (Nat.cast 4 : ZMod 28) * ((2 ^ 12 : ℕ) : ZMod 28) = Nat.cast 4 := by
      rw [Nat.cast_pow]
      decide
    rw [h_inner]

theorem pow_congr_196_tot (a b : ℕ) (ha : 196 ≤ a) :
    ((2 ^ (a + b * 84) : ℕ) : ZMod 196) = ((2 ^ a : ℕ) : ZMod 196) := by
  have h_sub : 2 ≤ a := by omega
  have h_eq : a = (a - 2) + 2 := by omega
  induction b with
  | zero =>
    simp
  | succ b ih =>
    have h1 : a + (b + 1) * 84 = (a + b * 84) + 84 := by omega
    rw [h1, pow_add, Nat.cast_mul, ih]
    have h_pow_a : 2 ^ a = 2 ^ (a - 2) * 4 := by
      nth_rw 1 [h_eq]
      rw [pow_add]
      rfl
    rw [h_pow_a]
    rw [Nat.cast_mul]
    rw [mul_assoc]
    have h_inner : (Nat.cast 4 : ZMod 196) * ((2 ^ 84 : ℕ) : ZMod 196) = Nat.cast 4 := by
      rw [Nat.cast_pow]
      decide
    rw [h_inner]

theorem pow_congr_550172 (a b : ℕ) (ha : 550172 ≤ a) :
    ((2 ^ (a + b * 235200) : ℕ) : ZMod 550172) = ((2 ^ a : ℕ) : ZMod 550172) := by
  have h_sub : 2 ≤ a := by omega
  have h_eq : a = (a - 2) + 2 := by omega
  induction b with
  | zero =>
    simp
  | succ b ih =>
    have h1 : a + (b + 1) * 235200 = (a + b * 235200) + 235200 := by omega
    rw [h1, pow_add, Nat.cast_mul, ih]
    have h_pow_a : 2 ^ a = 2 ^ (a - 2) * 4 := by
      nth_rw 1 [h_eq]
      rw [pow_add]
      rfl
    rw [h_pow_a]
    rw [Nat.cast_mul]
    rw [mul_assoc]
    have h_inner : (Nat.cast 4 : ZMod 550172) * ((2 ^ 235200 : ℕ) : ZMod 550172) = Nat.cast 4 := by
      have h_pow235200 : ((2 ^ 235200 : ℕ) : ZMod 550172) = powMod588 400 := by
        have h_235200 : 235200 = 588 * 400 := rfl
        nth_rw 1 [h_235200]
        exact lemma_pow 400
      rw [h_pow235200]
      have h_val : powMod588 400 = 137544 := rfl
      rw [h_val]
      decide
    rw [h_inner]

theorem P_1 : ∀ y : ZMod 1, ∃ k : ℕ, 1 ≤ k ∧ ((2^k - k : ℕ) : ZMod 1) = y := by
  intro y
  use 1
  constructor
  · decide
  · apply Subsingleton.elim

theorem P_1_with_2 : ∀ y : ZMod 1, ∃ k : ℕ, 2 ≤ k ∧ ((2^k - k : ℕ) : ZMod 1) = y := by
  intro y
  use 2
  constructor
  · decide
  · apply Subsingleton.elim

theorem P_2 : ∀ y : ZMod 2, ∃ k : ℕ, 2 ≤ k ∧ ((2^k - k : ℕ) : ZMod 2) = y := by
  have hg : 1 = Nat.gcd 1 2 := rfl
  exact step_down 2 1 1 hg pow_congr_2_tot P_1_with_2

theorem P_2_with_4 : ∀ y : ZMod 2, ∃ k : ℕ, 4 ≤ k ∧ ((2^k - k : ℕ) : ZMod 2) = y := by
  have hdvd : 2 ∣ 4 := by decide
  exact shift_sol 2 1 4 hdvd (by decide) pow_congr_2_tot P_2

theorem P_4 : ∀ y : ZMod 4, ∃ k : ℕ, 4 ≤ k ∧ ((2^k - k : ℕ) : ZMod 4) = y := by
  have hg : 2 = Nat.gcd 2 4 := rfl
  exact step_down 4 2 2 hg pow_congr_4_tot P_2_with_4

theorem P_4_with_28 : ∀ y : ZMod 4, ∃ k : ℕ, 28 ≤ k ∧ ((2^k - k : ℕ) : ZMod 4) = y := by
  have hdvd : 4 ∣ 28 := by decide
  exact shift_sol 4 2 28 hdvd (by decide) pow_congr_4_tot P_4

theorem P_28 : ∀ y : ZMod 28, ∃ k : ℕ, 28 ≤ k ∧ ((2^k - k : ℕ) : ZMod 28) = y := by
  have hg : 4 = Nat.gcd 12 28 := rfl
  exact step_down 28 4 12 hg pow_congr_28_tot P_4_with_28

theorem P_28_with_196 : ∀ y : ZMod 28, ∃ k : ℕ, 196 ≤ k ∧ ((2^k - k : ℕ) : ZMod 28) = y := by
  have hdvd : 28 ∣ 196 := by decide
  exact shift_sol 28 12 196 hdvd (by decide) pow_congr_28_tot P_28

theorem P_196 : ∀ y : ZMod 196, ∃ k : ℕ, 196 ≤ k ∧ ((2^k - k : ℕ) : ZMod 196) = y := by
  have hg : 28 = Nat.gcd 84 196 := rfl
  exact step_down 196 28 84 hg pow_congr_196_tot P_28_with_196

theorem P_196_with_550172 : ∀ y : ZMod 196, ∃ k : ℕ, 550172 ≤ k ∧ ((2^k - k : ℕ) : ZMod 196) = y := by
  have hdvd : 196 ∣ 550172 := by decide
  exact shift_sol 196 84 550172 hdvd (by decide) pow_congr_196_tot P_196

theorem P_550172 : ∀ y : ZMod 550172, ∃ k : ℕ, 550172 ≤ k ∧ ((2^k - k : ℕ) : ZMod 550172) = y := by
  have hg : 196 = Nat.gcd 235200 550172 := rfl
  exact step_down 550172 196 235200 hg pow_congr_550172 P_196_with_550172

noncomputable def sol_fun (y : ZMod 550172) : ℕ := Classical.choose (P_550172 y)

lemma sol_fun_spec (y : ZMod 550172) :
    550172 ≤ sol_fun y ∧ (((2 ^ (sol_fun y) - sol_fun y : ℕ) : ZMod 550172) = y) :=
  Classical.choose_spec (P_550172 y)

lemma pow_mul_4 (x : ZMod 1372) : x ^ 4116 = (((x ^ 1029) * (x ^ 1029)) * (x ^ 1029)) * (x ^ 1029) := by
  have h_add : 4116 = 1029 + 1029 + 1029 + 1029 := by decide
  rw [h_add, pow_add, pow_add, pow_add]

lemma pow2_4116_1372 : (2 : ZMod 1372) ^ 4116 = 344 := by
  have h1 : (2 : ZMod 1372) ^ 1029 = 344 := by decide
  rw [pow_mul_4]
  rw [h1]
  decide

def f1372 (k : ℕ) : ZMod 1372 := ((2 ^ k - k : ℕ) : ZMod 1372)

theorem period_1372 (k : ℕ) : f1372 (k + 2 + 4116) = f1372 (k + 2) := by
  have h1 : k + 2 + 4116 ≤ 2 ^ (k + 2 + 4116) := le_of_lt (Nat.lt_pow_self (by decide))
  have h2 : k + 2 ≤ 2 ^ (k + 2) := le_of_lt (Nat.lt_pow_self (by decide))
  change ((2 ^ (k + 2 + 4116) - (k + 2 + 4116) : ℕ) : ZMod 1372) = ((2 ^ (k + 2) - (k + 2) : ℕ) : ZMod 1372)
  rw [Nat.cast_sub h1, Nat.cast_sub h2]
  rw [Nat.cast_pow, Nat.cast_pow]
  have h_pow (x : ℕ) : (Nat.cast 2 : ZMod 1372) ^ (x + 2 + 4116) = (Nat.cast 2 : ZMod 1372) ^ (x + 2) := by
    rw [pow_add, pow_add]
    have h_pow4116 : (Nat.cast 2 : ZMod 1372) ^ 4116 = 344 := pow2_4116_1372
    rw [h_pow4116]
    have h_four : (Nat.cast 2 : ZMod 1372) ^ 2 = 4 := by decide
    rw [h_four]
    have h_1376 : (4 : ZMod 1372) * 344 = 4 := by decide
    rw [mul_assoc, h_1376]
  rw [h_pow k]
  rw [show k + 2 + 4116 = k + 2 + 4116 by rfl]
  rw [Nat.cast_add, Nat.cast_add]
  have h4 : (Nat.cast 4116 : ZMod 1372) = 0 := rfl
  rw [h4, add_zero]

theorem f1372_eq (q r : ℕ) : f1372 (4116 * q + (r + 2)) = f1372 (r + 2) := by
  induction q with
  | zero =>
    simp
  | succ q ih =>
    have h1 : 4116 * (q + 1) + (r + 2) = (4116 * q + r) + 2 + 4116 := by omega
    rw [h1, period_1372]
    exact ih

theorem f1372_eq_mod (k : ℕ) (hk : 2 ≤ k) : f1372 k = f1372 (2 + (k - 2) % 4116) := by
  have h : k = 4116 * ((k - 2) / 4116) + (((k - 2) % 4116) + 2) := by omega
  nth_rw 1 [h]
  have h_eq : f1372 (4116 * ((k - 2) / 4116) + (((k - 2) % 4116) + 2)) = f1372 (((k - 2) % 4116) + 2) := f1372_eq ((k - 2) / 4116) ((k - 2) % 4116)
  rw [h_eq]
  rw [add_comm]

def powMod2 (k : ℕ) (m : ℕ) : ℕ :=
  (2 ^ k) % m

def f1372_fast (k : ℕ) : ℕ :=
  (powMod2 k 1372 + 13720 - k % 1372) % 1372

lemma powMod2_spec (k : ℕ) : ((powMod2 k 1372 : ℕ) : ZMod 1372) = ((2 ^ k : ℕ) : ZMod 1372) := by
  unfold powMod2
  have h : (((2 ^ k) % 1372 : ℕ) : ZMod 1372).val = ((2 ^ k : ℕ) : ZMod 1372).val := by
    rw [val_natCast, val_natCast]
    omega
  exact val_injective 1372 h

lemma f1372_fast_eq (k : ℕ) (hk : 2 ≤ k) : (f1372 k : ZMod 1372) = (((f1372_fast k : ℕ) : ZMod 1372)) := by
  unfold f1372 f1372_fast
  have h_le : k ≤ 2 ^ k := le_of_lt (Nat.lt_pow_self (by decide))
  rw [Nat.cast_sub h_le]
  push_cast
  have h_pow := powMod2_spec k
  push_cast at h_pow
  rw [← h_pow]
  have h_val_eq : (((powMod2 k 1372 + 13720 - k % 1372 : ℕ) : ZMod 1372)) = (powMod2 k 1372 : ZMod 1372) - (k : ZMod 1372) := by
    have h_le_val : k % 1372 ≤ powMod2 k 1372 + 13720 := by
      have : k % 1372 < 1372 := Nat.mod_lt _ (by decide)
      omega
    rw [Nat.cast_sub h_le_val]
    push_cast
    have : (13720 : ZMod 1372) = 0 := rfl
    rw [this, add_zero]
    have h_mod : ((k % 1372 : ℕ) : ZMod 1372) = (k : ZMod 1372) := by
      have h_val : ((k % 1372 : ℕ) : ZMod 1372).val = (k : ZMod 1372).val := by
        rw [val_natCast, val_natCast]
        omega
      exact val_injective 1372 h_val
    rw [h_mod]
  have h_mod_goal : (((powMod2 k 1372 + 13720 - k % 1372) % 1372 : ℕ) : ZMod 1372) = ((powMod2 k 1372 + 13720 - k % 1372 : ℕ) : ZMod 1372) := by
    have h_val : (((powMod2 k 1372 + 13720 - k % 1372) % 1372 : ℕ) : ZMod 1372).val = ((powMod2 k 1372 + 13720 - k % 1372 : ℕ) : ZMod 1372).val := by
      rw [val_natCast, val_natCast]
      omega
    exact val_injective 1372 h_val
  rw [h_mod_goal]
  rw [← h_val_eq]

lemma zmod_eq_of_eq {a b : ℕ} (h : (a : ZMod 1372) = (b : ZMod 1372)) : a % 1372 = b % 1372 := by
  have h_val : (a : ZMod 1372).val = (b : ZMod 1372).val := by rw [h]
  rwa [val_natCast, val_natCast] at h_val

def check_block1 (r : ℕ) : ℕ → Bool
  | 0 => true
  | count + 1 =>
    if f1372_fast (2 + r) == 1225 then false
    else check_block1 (r + 1) count

theorem check_block1_true : check_block1 0 1000 = true := by decide

theorem check_block1_spec (count : ℕ) (r : ℕ) (h_true : check_block1 r count = true) :
    ∀ i < count, f1372_fast (2 + (r + i)) ≠ 1225 := by
  induction count generalizing r with
  | zero =>
    intro i hi
    omega
  | succ count' ih =>
    intro i hi
    unfold check_block1 at h_true
    split at h_true
    · contradiction
    · rename_i h_neq
      have h_neq_val : f1372_fast (2 + r) ≠ 1225 := by
        intro hc
        have : (f1372_fast (2 + r) == 1225) = true := by rw [beq_iff_eq]; exact hc
        rw [this] at h_neq
        contradiction
      rcases i with _ | i'
      · have : 2 + (r + 0) = 2 + r := by omega
        rw [this]
        exact h_neq_val
      · have hi' : i' < count' := by omega
        have ih_res := ih (r + 1) h_true i' hi'
        have h_eq : r + 1 + i' = r + (i' + 1) := by omega
        rwa [h_eq] at ih_res

def check_block2 (r : ℕ) : ℕ → Bool
  | 0 => true
  | count + 1 =>
    if r == 1001 then
      check_block2 (r + 1) count
    else
      if f1372_fast (2 + r) == 1225 then false
      else check_block2 (r + 1) count

theorem check_block2_true : check_block2 1000 1000 = true := by decide

theorem check_block2_spec (count : ℕ) (r : ℕ) (h_true : check_block2 r count = true) :
    ∀ i < count, r + i ≠ 1001 → f1372_fast (2 + (r + i)) ≠ 1225 := by
  induction count generalizing r with
  | zero =>
    intro i hi
    omega
  | succ count' ih =>
    intro i hi h_not
    unfold check_block2 at h_true
    split at h_true
    · rename_i h_cond
      rcases i with _ | i'
      · simp at h_cond
        omega
      · have hi' : i' < count' := by omega
        have h_not' : r + 1 + i' ≠ 1001 := by omega
        have ih_res := ih (r + 1) h_true i' hi' h_not'
        have h_eq : r + 1 + i' = r + (i' + 1) := by omega
        rwa [h_eq] at ih_res
    · split at h_true
      · contradiction
      · rename_i h_neq
        have h_neq_val : f1372_fast (2 + r) ≠ 1225 := by
          intro hc
          have : (f1372_fast (2 + r) == 1225) = true := by rw [beq_iff_eq]; exact hc
          rw [this] at h_neq
          contradiction
        rcases i with _ | i'
        · have : 2 + (r + 0) = 2 + r := by omega
          rw [this]
          exact h_neq_val
        · have hi' : i' < count' := by omega
          have h_not' : r + 1 + i' ≠ 1001 := by omega
          have ih_res := ih (r + 1) h_true i' hi' h_not'
          have h_eq : r + 1 + i' = r + (i' + 1) := by omega
          rwa [h_eq] at ih_res

def check_block3 (r : ℕ) : ℕ → Bool
  | 0 => true
  | count + 1 =>
    if f1372_fast (2 + r) == 1225 then false
    else check_block3 (r + 1) count

theorem check_block3_true : check_block3 2000 1000 = true := by decide

theorem check_block3_spec (count : ℕ) (r : ℕ) (h_true : check_block3 r count = true) :
    ∀ i < count, f1372_fast (2 + (r + i)) ≠ 1225 := by
  induction count generalizing r with
  | zero =>
    intro i hi
    omega
  | succ count' ih =>
    intro i hi
    unfold check_block3 at h_true
    split at h_true
    · contradiction
    · rename_i h_neq
      have h_neq_val : f1372_fast (2 + r) ≠ 1225 := by
        intro hc
        have : (f1372_fast (2 + r) == 1225) = true := by rw [beq_iff_eq]; exact hc
        rw [this] at h_neq
        contradiction
      rcases i with _ | i'
      · have : 2 + (r + 0) = 2 + r := by omega
        rw [this]
        exact h_neq_val
      · have hi' : i' < count' := by omega
        have ih_res := ih (r + 1) h_true i' hi'
        have h_eq : r + 1 + i' = r + (i' + 1) := by omega
        rwa [h_eq] at ih_res

def check_block4 (r : ℕ) : ℕ → Bool
  | 0 => true
  | count + 1 =>
    if r == 3121 || r == 3369 then
      check_block4 (r + 1) count
    else
      if f1372_fast (2 + r) == 1225 then false
      else check_block4 (r + 1) count

theorem check_block4_true : check_block4 3000 1000 = true := by decide

theorem check_block4_spec (count : ℕ) (r : ℕ) (h_true : check_block4 r count = true) :
    ∀ i < count, r + i ≠ 3121 ∧ r + i ≠ 3369 → f1372_fast (2 + (r + i)) ≠ 1225 := by
  induction count generalizing r with
  | zero =>
    intro i hi
    omega
  | succ count' ih =>
    intro i hi h_not
    unfold check_block4 at h_true
    split at h_true
    · rename_i h_cond
      rcases i with _ | i'
      · simp at h_cond
        omega
      · have hi' : i' < count' := by omega
        have h_not' : r + 1 + i' ≠ 3121 ∧ r + 1 + i' ≠ 3369 := by omega
        have ih_res := ih (r + 1) h_true i' hi' h_not'
        have h_eq : r + 1 + i' = r + (i' + 1) := by omega
        rwa [h_eq] at ih_res
    · split at h_true
      · contradiction
      · rename_i h_neq
        have h_neq_val : f1372_fast (2 + r) ≠ 1225 := by
          intro hc
          have : (f1372_fast (2 + r) == 1225) = true := by rw [beq_iff_eq]; exact hc
          rw [this] at h_neq
          contradiction
        rcases i with _ | i'
        · have : 2 + (r + 0) = 2 + r := by omega
          rw [this]
          exact h_neq_val
        · have hi' : i' < count' := by omega
          have h_not' : r + 1 + i' ≠ 3121 ∧ r + 1 + i' ≠ 3369 := by omega
          have ih_res := ih (r + 1) h_true i' hi' h_not'
          have h_eq : r + 1 + i' = r + (i' + 1) := by omega
          rwa [h_eq] at ih_res

def check_block5 (r : ℕ) : ℕ → Bool
  | 0 => true
  | count + 1 =>
    if f1372_fast (2 + r) == 1225 then false
    else check_block5 (r + 1) count

theorem check_block5_true : check_block5 4000 116 = true := by decide

theorem check_block5_spec (count : ℕ) (r : ℕ) (h_true : check_block5 r count = true) :
    ∀ i < count, f1372_fast (2 + (r + i)) ≠ 1225 := by
  induction count generalizing r with
  | zero =>
    intro i hi
    omega
  | succ count' ih =>
    intro i hi
    unfold check_block5 at h_true
    split at h_true
    · contradiction
    · rename_i h_neq
      have h_neq_val : f1372_fast (2 + r) ≠ 1225 := by
        intro hc
        have : (f1372_fast (2 + r) == 1225) = true := by rw [beq_iff_eq]; exact hc
        rw [this] at h_neq
        contradiction
      rcases i with _ | i'
      · have : 2 + (r + 0) = 2 + r := by omega
        rw [this]
        exact h_neq_val
      · have hi' : i' < count' := by omega
        have ih_res := ih (r + 1) h_true i' hi'
        have h_eq : r + 1 + i' = r + (i' + 1) := by omega
        rwa [h_eq] at ih_res

theorem f1372_sol_dec (r : ℕ) (hr : r < 4116) (h_sol : f1372 (2 + r) = 1225) : r = 1001 ∨ r = 3121 ∨ r = 3369 := by
  by_contra h_not
  push_neg at h_not
  have h_fast_eq := f1372_fast_eq (2 + r) (by omega)
  rw [h_sol] at h_fast_eq
  have h_fast_val := (zmod_eq_of_eq h_fast_eq).symm
  have h_1225_val : 1225 % 1372 = 1225 := rfl
  rw [h_1225_val] at h_fast_val
  have h_fast_range : f1372_fast (2 + r) < 1372 := Nat.mod_lt _ (by decide)
  have h_fast_val2 : f1372_fast (2 + r) % 1372 = f1372_fast (2 + r) := Nat.mod_eq_of_lt h_fast_range
  rw [h_fast_val2] at h_fast_val
  by_cases hr1000 : r < 1000
  · have h_check := check_block1_spec 1000 0 check_block1_true r hr1000
    have h_neq := h_check
    have h_eq : 0 + r = r := by omega
    rw [h_eq] at h_neq
    exact h_neq h_fast_val
  · by_cases hr2000 : r < 2000
    · have hr_sub : r - 1000 < 1000 := by omega
      have h_check := check_block2_spec 1000 1000 check_block2_true (r - 1000) hr_sub
      have h_not_1001 : 1000 + (r - 1000) ≠ 1001 := by omega
      have h_neq := h_check h_not_1001
      have h_eq : 1000 + (r - 1000) = r := by omega
      rw [h_eq] at h_neq
      exact h_neq h_fast_val
    · by_cases hr3000 : r < 3000
      · have hr_sub : r - 2000 < 1000 := by omega
        have h_check := check_block3_spec 1000 2000 check_block3_true (r - 2000) hr_sub
        have h_neq := h_check
        have h_eq : 2000 + (r - 2000) = r := by omega
        rw [h_eq] at h_neq
        exact h_neq h_fast_val
      · by_cases hr4000 : r < 4000
        · have hr_sub : r - 3000 < 1000 := by omega
          have h_check := check_block4_spec 1000 3000 check_block4_true (r - 3000) hr_sub
          have h_not_special : 3000 + (r - 3000) ≠ 3121 ∧ 3000 + (r - 3000) ≠ 3369 := by omega
          have h_neq := h_check h_not_special
          have h_eq : 3000 + (r - 3000) = r := by omega
          rw [h_eq] at h_neq
          exact h_neq h_fast_val
        · have hr_sub : r - 4000 < 116 := by omega
          have h_check := check_block5_spec 116 4000 check_block5_true (r - 4000) hr_sub
          have h_neq := h_check
          have h_eq : 4000 + (r - 4000) = r := by omega
          rw [h_eq] at h_neq
          exact h_neq h_fast_val

theorem sol_1372_cond (k : ℕ) (hk2 : 2 ≤ k) (h_sol : f1372 k = 1225) :
    k % 4116 = 1003 ∨ k % 4116 = 3123 ∨ k % 4116 = 3371 := by
  have h1 : f1372 (2 + (k - 2) % 4116) = 1225 := by rwa [← f1372_eq_mod k hk2]
  have h2 : (k - 2) % 4116 < 4116 := Nat.mod_lt _ (by decide)
  have h3 := f1372_sol_dec ((k - 2) % 4116) h2 h1
  rcases h3 with h | h | h
  · left; omega
  · right; left; omega
  · right; right; omega

theorem sol_1372_cond_all (k : ℕ) (hk1 : 1 ≤ k) (h_sol : f1372 k = 1225) :
    k % 4116 = 1003 ∨ k % 4116 = 3123 ∨ k % 4116 = 3371 := by
  by_cases hk2 : 2 ≤ k
  · exact sol_1372_cond k hk2 h_sol
  · have hk : k = 1 := by omega
    subst hk
    revert h_sol
    decide

lemma pow_mul_4_401 (x : ZMod 401) : x ^ 4116 = (((x ^ 1029) * (x ^ 1029)) * (x ^ 1029)) * (x ^ 1029) := by
  have h_add : 4116 = 1029 + 1029 + 1029 + 1029 := by decide
  rw [h_add, pow_add, pow_add, pow_add]

lemma pow2_4116 : (2 : ZMod 401) ^ 4116 = 228 := by
  have h1 : (2 : ZMod 401) ^ 1029 = 82 := by decide
  rw [pow_mul_4_401]
  rw [h1]
  decide

lemma pow_t_lemma (t : ℕ) (r : ℕ) : (2 : ZMod 401) ^ (4116 * t + r) = (2 : ZMod 401) ^ r * (228 : ZMod 401) ^ t := by
  induction t generalizing r with
  | zero =>
    simp
  | succ t ih =>
    have h1 : 4116 * (t + 1) + r = 4116 * t + (r + 4116) := by omega
    rw [h1, ih (r + 4116)]
    rw [pow_add]
    have h_pow2 : (2 : ZMod 401) ^ 4116 = 228 := pow2_4116
    rw [h_pow2]
    ring

lemma pow_lemma_401 (t r : ℕ) : ((2 ^ (4116 * t + r) : ℕ) : ZMod 401) = (2 : ZMod 401) ^ r * (228 : ZMod 401) ^ t := by
  push_cast
  exact pow_t_lemma t r

theorem cand_eq_401 (t r : ℕ) (h_le : 4116 * t + r ≤ 2 ^ (4116 * t + r)) :
    ((2 ^ (4116 * t + r) - (4116 * t + r) : ℕ) : ZMod 401) =
    (2 : ZMod 401) ^ r * (228 : ZMod 401) ^ t - (4116 * t + r : ZMod 401) := by
  rw [Nat.cast_sub h_le]
  rw [pow_lemma_401]
  push_cast
  rfl

def verify_t_aux (t : ℕ) (pow1003 pow3123 pow3371 : ZMod 401) : ℕ → Bool
  | 0 => true
  | count + 1 =>
    let ok1 := pow1003 - (1003 + 4116 * t : ZMod 401) != 340
    let ok2 := pow3123 - (3123 + 4116 * t : ZMod 401) != 340
    let ok3 := t > 3966 || pow3371 - (3371 + 4116 * t : ZMod 401) != 340
    if ok1 && ok2 && ok3 then
      verify_t_aux (t + 1) (pow1003 * 228) (pow3123 * 228) (pow3371 * 228) count
    else
      false

def verify_t_all : Bool :=
  verify_t_aux 0 8 312 357 2000 &&
  verify_t_aux 2000 8 312 357 1968

theorem verify_t_all_true : verify_t_all = true := by decide

theorem verify_t_aux_spec (count : ℕ) (t : ℕ) (pow1003 pow3123 pow3371 : ZMod 401)
    (h_true : verify_t_aux t pow1003 pow3123 pow3371 count = true) :
    ∀ i < count,
      ( pow1003 * (228 : ZMod 401) ^ i - (1003 + 4116 * (t + i) : ZMod 401) ≠ 340 ) ∧
      ( pow3123 * (228 : ZMod 401) ^ i - (3123 + 4116 * (t + i) : ZMod 401) ≠ 340 ) ∧
      ( t + i ≤ 3966 → pow3371 * (228 : ZMod 401) ^ i - (3371 + 4116 * (t + i) : ZMod 401) ≠ 340 ) := by
  induction count generalizing t pow1003 pow3123 pow3371 with
  | zero =>
    intro i hi
    omega
  | succ count ih =>
    intro i hi
    unfold verify_t_aux at h_true
    dsimp only at h_true
    have h_cond : (bne (pow1003 - (1003 + 4116 * t : ZMod 401)) 340 &&
                  bne (pow3123 - (3123 + 4116 * t : ZMod 401)) 340 &&
                  (decide (t > 3966) || bne (pow3371 - (3371 + 4116 * t : ZMod 401)) 340)) = true := by
      split at h_true
      · rename_i h
        exact h
      · contradiction
    have h_next : verify_t_aux (t + 1) (pow1003 * 228) (pow3123 * 228) (pow3371 * 228) count = true := by
      split at h_true <;> assumption
    simp only [Bool.and_eq_true, bne_iff_ne, Bool.or_eq_true, decide_eq_true_iff] at h_cond
    rcases i with _ | i'
    · simp only [Nat.cast_zero, add_zero, pow_zero, mul_one]
      rcases h_cond with ⟨⟨h1, h2⟩, h3⟩
      refine ⟨h1, h2, ?_⟩
      intro ht
      rcases h3 with ht_gt | h3'
      · omega
      · exact h3'
    · have hi' : i' < count := by omega
      have ih_res := ih (t + 1) (pow1003 * 228) (pow3123 * 228) (pow3371 * 228) h_next i' hi'
      have h_re_t : (↑(t + 1) : ZMod 401) + ↑i' = ↑t + ↑(i' + 1) := by push_cast; ring
      have h_re_t_nat : t + 1 + i' = t + (i' + 1) := by omega
      rw [h_re_t_nat] at ih_res
      have h_pow : (pow1003 * 228) * (228 : ZMod 401) ^ i' = pow1003 * (228 : ZMod 401) ^ (i' + 1) := by
        rw [pow_succ]
        ring
      have h_pow2 : (pow3123 * 228) * (228 : ZMod 401) ^ i' = pow3123 * (228 : ZMod 401) ^ (i' + 1) := by
        rw [pow_succ]
        ring
      have h_pow3 : (pow3371 * 228) * (228 : ZMod 401) ^ i' = pow3371 * (228 : ZMod 401) ^ (i' + 1) := by
        rw [pow_succ]
        ring
      rw [h_pow, h_pow2, h_pow3] at ih_res
      have h_cast_eq : (↑(t + 1) : ZMod 401) + ↑i' = ↑t + ↑(i' + 1) := h_re_t
      rw [h_cast_eq] at ih_res
      exact ih_res

lemma pow228_2000 : (228 : ZMod 401) ^ 2000 = 1 := by
  have h1 : (228 : ZMod 401) ^ 400 = 1 := by decide
  have h2 : (228 : ZMod 401) ^ 2000 = ((228 : ZMod 401) ^ 400) ^ 5 := by ring
  rw [h2, h1]
  decide

lemma verify_t_all_true_parts :
    (verify_t_aux 0 8 312 357 2000 = true) ∧
    (verify_t_aux 2000 8 312 357 1968 = true) := by
  have h := verify_t_all_true
  unfold verify_t_all at h
  simp only [Bool.and_eq_true] at h
  exact h

lemma verify_part1 (i : ℕ) (hi : i < 2000) :
    ( (8 : ZMod 401) * (228 : ZMod 401) ^ i - (1003 + 4116 * i : ZMod 401) ≠ 340 ) ∧
    ( (312 : ZMod 401) * (228 : ZMod 401) ^ i - (3123 + 4116 * i : ZMod 401) ≠ 340 ) ∧
    ( i ≤ 3966 → (357 : ZMod 401) * (228 : ZMod 401) ^ i - (3371 + 4116 * i : ZMod 401) ≠ 340 ) := by
  have h := verify_t_all_true_parts.1
  have h_spec := verify_t_aux_spec 2000 0 8 312 357 h i hi
  simp only [Nat.cast_zero, zero_add] at h_spec
  exact h_spec

lemma verify_part2 (i : ℕ) (hi : i < 1968) :
    ( (8 : ZMod 401) * (228 : ZMod 401) ^ i - (1003 + 4116 * (2000 + i) : ZMod 401) ≠ 340 ) ∧
    ( (312 : ZMod 401) * (228 : ZMod 401) ^ i - (3123 + 4116 * (2000 + i) : ZMod 401) ≠ 340 ) ∧
    ( 2000 + i ≤ 3966 → (357 : ZMod 401) * (228 : ZMod 401) ^ i - (3371 + 4116 * (2000 + i) : ZMod 401) ≠ 340 ) := by
  have h := verify_t_all_true_parts.2
  have h_spec := verify_t_aux_spec 1968 2000 8 312 357 h i hi
  exact h_spec

lemma verify_t_spec_all (t : ℕ) (ht : t < 3968) :
    ( (8 : ZMod 401) * (228 : ZMod 401) ^ t - (1003 + 4116 * t : ZMod 401) ≠ 340 ) ∧
    ( (312 : ZMod 401) * (228 : ZMod 401) ^ t - (3123 + 4116 * t : ZMod 401) ≠ 340 ) ∧
    ( t ≤ 3966 → (357 : ZMod 401) * (228 : ZMod 401) ^ t - (3371 + 4116 * t : ZMod 401) ≠ 340 ) := by
  by_cases ht2000 : t < 2000
  · exact verify_part1 t ht2000
  · have h_sub : t - 2000 < 1968 := by omega
    have h_eq : t = 2000 + (t - 2000) := by omega
    have h_part2 := verify_part2 (t - 2000) h_sub
    rcases h_part2 with ⟨hp1, hp2, hp3⟩
    have h_pow_eq : (228 : ZMod 401) ^ (t - 2000) = (228 : ZMod 401) ^ t := by
      have h_expand : (228 : ZMod 401) ^ t = (228 : ZMod 401) ^ (2000 + (t - 2000)) := by rw [← h_eq]
      rw [h_expand, pow_add, pow228_2000, one_mul]
    have h_eq_cast : (t : ZMod 401) = 2000 + ↑(t - 2000) := by
      nth_rw 1 [h_eq]
      push_cast
      rfl
    rw [h_pow_eq, ← h_eq_cast] at hp1
    rw [h_pow_eq, ← h_eq_cast] at hp2
    refine ⟨hp1, hp2, ?_⟩
    intro ht3966
    have h_cond_le : 2000 + (t - 2000) ≤ 3966 := by omega
    have hp3' := hp3 h_cond_le
    rw [h_pow_eq, ← h_eq_cast] at hp3'
    exact hp3'

lemma pow_1003_val : (2 : ZMod 401) ^ 1003 = 8 := by
  have h1 : (2 : ZMod 401) ^ 1000 = 1 := by decide
  have h2 : (2 : ZMod 401) ^ 1003 = ((2 : ZMod 401) ^ 1000) * (2 : ZMod 401) ^ 3 := by ring
  rw [h2, h1]
  decide

lemma pow_3123_val : (2 : ZMod 401) ^ 3123 = 312 := by
  have h1 : (2 : ZMod 401) ^ 1000 = 1 := by decide
  have h2 : (2 : ZMod 401) ^ 3123 = ((2 : ZMod 401) ^ 1000) ^ 3 * (2 : ZMod 401) ^ 123 := by ring
  rw [h2, h1]
  decide

lemma pow_3371_val : (2 : ZMod 401) ^ 3371 = 357 := by
  have h1 : (2 : ZMod 401) ^ 1000 = 1 := by decide
  have h2 : (2 : ZMod 401) ^ 3371 = ((2 : ZMod 401) ^ 1000) ^ 3 * (2 : ZMod 401) ^ 371 := by ring
  rw [h2, h1]
  decide

theorem proj_1372 (k : ℕ) (h : ((2^k - k : ℕ) : ZMod 550172) = 13573) : ((2^k - k : ℕ) : ZMod 1372) = 1225 := by
  have h_val : ((2^k - k : ℕ) : ZMod 550172).val = (13573 : ZMod 550172).val := by rw [h]
  have h_val_13573 : (13573 : ZMod 550172).val = 13573 := rfl
  rw [h_val_13573] at h_val
  rw [val_natCast] at h_val
  have h_eq : 2^k - k = 550172 * ((2^k - k) / 550172) + (2^k - k) % 550172 := (Nat.div_add_mod (2^k - k) 550172).symm
  rw [h_val] at h_eq
  have h_cast : ((2^k - k : ℕ) : ZMod 1372) = ((550172 * ((2^k - k) / 550172) + 13573 : ℕ) : ZMod 1372) := by nth_rw 1 [h_eq]
  rw [h_cast]
  push_cast
  have h_550172 : (550172 : ZMod 1372) = 0 := by decide
  have h_13573 : (13573 : ZMod 1372) = 1225 := by decide
  rw [h_550172, h_13573]
  simp

theorem proj_401 (k : ℕ) (h : ((2^k - k : ℕ) : ZMod 550172) = 13573) : ((2^k - k : ℕ) : ZMod 401) = 340 := by
  have h_val : ((2^k - k : ℕ) : ZMod 550172).val = (13573 : ZMod 550172).val := by rw [h]
  have h_val_13573 : (13573 : ZMod 550172).val = 13573 := rfl
  rw [h_val_13573] at h_val
  rw [val_natCast] at h_val
  have h_eq : 2^k - k = 550172 * ((2^k - k) / 550172) + (2^k - k) % 550172 := (Nat.div_add_mod (2^k - k) 550172).symm
  rw [h_val] at h_eq
  have h_cast : ((2^k - k : ℕ) : ZMod 401) = ((550172 * ((2^k - k) / 550172) + 13573 : ℕ) : ZMod 401) := by nth_rw 1 [h_eq]
  rw [h_cast]
  push_cast
  have h_550172 : (550172 : ZMod 401) = 0 := by decide
  have h_13573 : (13573 : ZMod 401) = 340 := by decide
  rw [h_550172, h_13573]
  simp

theorem no_sol_13573 (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k ≤ 16331503) :
    ((2^k - k : ℕ) : ZMod 550172) ≠ 13573 := by
  intro h
  have h_1372 := proj_1372 k h
  have h_401 := proj_401 k h
  have h_cond := sol_1372_cond_all k hk1 h_1372
  let t := k / 4116
  let r := k % 4116
  have h_eq_k : k = 4116 * t + r := (Nat.div_add_mod k 4116).symm
  have h_pow_le : k ≤ 2 ^ k := Nat.le_of_lt (Nat.lt_pow_self (by decide))
  have h_pow_le' : 4116 * t + r ≤ 2 ^ (4116 * t + r) := by
    rw [← h_eq_k]
    exact h_pow_le
  have h_cand := cand_eq_401 t r h_pow_le'
  rw [← h_eq_k] at h_cand
  rw [h_401] at h_cand
  have ht_lt : t < 3968 := by
    have h_div : k / 4116 ≤ 16331503 / 4116 := Nat.div_le_div_right hk2
    have h_calc : 16331503 / 4116 = 3967 := by decide
    omega
  have h_verify := verify_t_spec_all t ht_lt
  rcases h_cond with hr | hr | hr
  · have hr' : r = 1003 := hr
    rw [hr'] at h_cand
    have h_pow1003 : (2 : ZMod 401) ^ 1003 = 8 := pow_1003_val
    rw [h_pow1003] at h_cand
    have h_cand_re : (8 : ZMod 401) * 228 ^ t - (1003 + 4116 * t : ZMod 401) = 340 := by
      rw [h_cand]
      push_cast
      ring
    exact h_verify.1 h_cand_re
  · have hr' : r = 3123 := hr
    rw [hr'] at h_cand
    have h_pow3123 : (2 : ZMod 401) ^ 3123 = 312 := pow_3123_val
    rw [h_pow3123] at h_cand
    have h_cand_re : (312 : ZMod 401) * 228 ^ t - (3123 + 4116 * t : ZMod 401) = 340 := by
      rw [h_cand]
      push_cast
      ring
    exact h_verify.2.1 h_cand_re
  · have hr' : r = 3371 := hr
    rw [hr'] at h_cand
    have h_pow3371 : (2 : ZMod 401) ^ 3371 = 357 := pow_3371_val
    rw [h_pow3371] at h_cand
    have h_cand_re : (357 : ZMod 401) * 228 ^ t - (3371 + 4116 * t : ZMod 401) = 340 := by
      rw [h_cand]
      push_cast
      ring
    have ht_le : t ≤ 3966 := by
      have h_sub_ineq : 4116 * t + 3371 ≤ 16331503 := by
        rw [← hr']
        rw [← h_eq_k]
        exact hk2
      omega
    exact h_verify.2.2 ht_le h_cand_re

theorem prop_mono (m1 m2 : ℕ) (h_le : m1 ≤ m2) (h : A232616_prop 550172 m1) : A232616_prop 550172 m2 := by
  have h1 : Finset.Icc 1 m1 ⊆ Finset.Icc 1 m2 := Finset.Icc_subset_Icc (by omega) h_le
  have h2 : (Finset.Icc 1 m1).image (fun k => (Nat.cast (2 ^ k - k) : ZMod 550172)) ⊆ (Finset.Icc 1 m2).image (fun k => (Nat.cast (2 ^ k - k) : ZMod 550172)) := Finset.image_mono (fun k => (Nat.cast (2 ^ k - k) : ZMod 550172)) h1
  have h3 : (univ : Finset (ZMod 550172)) = (Finset.Icc 1 m1).image (fun k => (Nat.cast (2 ^ k - k) : ZMod 550172)) := h
  have h4 : (univ : Finset (ZMod 550172)) ⊆ (Finset.Icc 1 m2).image (fun k => (Nat.cast (2 ^ k - k) : ZMod 550172)) := by
    rw [h3]
    exact h2
  have h5 : (Finset.Icc 1 m2).image (fun k => (Nat.cast (2 ^ k - k) : ZMod 550172)) ⊆ (univ : Finset (ZMod 550172)) := Finset.subset_univ _
  exact Finset.Subset.antisymm h4 h5

theorem A232616_nonempty : {m : ℕ | A232616_prop 550172 m}.Nonempty := by
  let Y : Finset (ZMod 550172) := Finset.univ
  let sol_set : Finset ℕ := Y.image sol_fun
  have h_mem : sol_fun 0 ∈ sol_set := Finset.mem_image_of_mem sol_fun (Finset.mem_univ 0)
  have h_ne : sol_set.Nonempty := ⟨sol_fun 0, h_mem⟩
  let M := sol_set.max' h_ne
  use M
  unfold A232616_prop
  ext y
  constructor
  · intro _
    rw [Finset.mem_image]
    use sol_fun y
    have h_mem_sol : sol_fun y ∈ sol_set := Finset.mem_image_of_mem sol_fun (Finset.mem_univ y)
    have h_le_M : sol_fun y ≤ M := sol_set.le_max' _ h_mem_sol
    have h_spec := sol_fun_spec y
    have h_ge_1 : 1 ≤ sol_fun y := by omega
    constructor
    · rw [Finset.mem_Icc]
      exact ⟨h_ge_1, h_le_M⟩
    · exact h_spec.2
  · intro _
    exact mem_univ _

theorem not_A232616_prop_16331503 : ¬ A232616_prop 550172 16331503 := by
  unfold A232616_prop
  intro h_eq
  have h_mem : (13573 : ZMod 550172) ∈ (univ : Finset (ZMod 550172)) := mem_univ _
  rw [h_eq] at h_mem
  rw [Finset.mem_image] at h_mem
  rcases h_mem with ⟨k, hk_icc, hk_eq⟩
  rw [Finset.mem_Icc] at hk_icc
  have hk1 : 1 ≤ k := hk_icc.1
  have hk2 : k ≤ 16331503 := hk_icc.2
  have h_neq := no_sol_13573 k hk1 hk2
  exact h_neq hk_eq

theorem A232616_ge : 16331504 ≤ A232616 550172 := by
  unfold A232616
  have h_ne : 550172 ≠ 0 := by decide
  rw [dif_neg h_ne]
  have h_nonempty : { m : ℕ | A232616_prop 550172 m }.Nonempty := A232616_nonempty
  apply le_csInf h_nonempty
  intro m hm
  by_contra h_lt
  push_neg at h_lt
  have h_le : m ≤ 16331503 := by omega
  have hm_prop : A232616_prop 550172 16331503 := prop_mono m 16331503 h_le hm
  exact not_A232616_prop_16331503 hm_prop

noncomputable def my_A : ℕ := A232616 550172
noncomputable def my_P : ℕ := Nat.nth Nat.Prime 550171

theorem A_ge_bound : 16331504 ≤ my_A := A232616_ge
theorem P_prime_bound : my_P ≤ 8165753 := nth_prime_bound

theorem oeis_232616_conjecture_i.disproof : ¬ (∀ (n : ℕ) (hn : 0 < n), A232616 n < 2 * (Nat.nth Nat.Prime (n - 1) - 1)) := by
  intro h
  have h_spec := h 550172 (by decide)
  have h_sub : 550172 - 1 = 550171 := rfl
  rw [h_sub] at h_spec
  have h_spec' : my_A < 2 * (my_P - 1) := h_spec
  have h_prime' : my_P ≤ 8165753 := P_prime_bound
  have h_A' : 16331504 ≤ my_A := A_ge_bound
  omega
