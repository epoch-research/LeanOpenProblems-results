import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false

open Nat

/-! Squares are never 2 or 3 mod 4. -/

lemma sq_mod_four_ne_two (n : ℕ) : n ^ 2 % 4 ≠ 2 := by
  have : n % 4 < 4 := Nat.mod_lt n (by decide)
  have heq : n ^ 2 % 4 = (n % 4) ^ 2 % 4 := by rw [Nat.pow_mod]
  rw [heq]
  interval_cases n % 4 <;> norm_num

lemma sq_mod_four_ne_three (n : ℕ) : n ^ 2 % 4 ≠ 3 := by
  have : n % 4 < 4 := Nat.mod_lt n (by decide)
  have heq : n ^ 2 % 4 = (n % 4) ^ 2 % 4 := by rw [Nat.pow_mod]
  rw [heq]
  interval_cases n % 4 <;> norm_num

lemma x_odd_of_sq_eq_cube_add_two {x y : ℕ} (h : y ^ 2 = x ^ 3 + 2) : Odd x := by
  by_contra hx
  have hxE : Even x := Nat.not_odd_iff_even.mp hx
  obtain ⟨k, hk⟩ := hxE
  have hx3 : x ^ 3 % 4 = 0 := by
    rw [hk]
    have : (k + k) ^ 3 = 8 * k ^ 3 := by ring
    rw [this]; omega
  have : y ^ 2 % 4 = 2 := by
    rw [h, Nat.add_mod, hx3]
  exact sq_mod_four_ne_two y this

lemma y_odd_of_sq_eq_cube_add_two {x y : ℕ} (h : y ^ 2 = x ^ 3 + 2) : Odd y := by
  have hx := x_odd_of_sq_eq_cube_add_two h
  have hx3 : Odd (x ^ 3) := Odd.pow hx
  have hsum : Odd (x ^ 3 + 2) := by
    rw [Nat.odd_add]
    exact iff_of_true hx3 even_two
  have : Odd (y ^ 2) := by rwa [h]
  simpa [Nat.odd_pow_iff (by decide : (2 : ℕ) ≠ 0)] using this

lemma geom_cube_odd (x : ℕ) : x ^ 2 - x + 1 = x ^ 2 + 1 - x := by
  cases x with
  | zero => simp
  | succ n =>
    have : n + 1 ≤ (n + 1) ^ 2 := Nat.le_self_pow (by omega) _
    omega

lemma cube_add_one_factor (x : ℕ) : x ^ 3 + 1 = (x + 1) * (x ^ 2 - x + 1) := by
  have hZ : ((x : ℤ) ^ 3 + 1) = ((x : ℤ) + 1) * ((x : ℤ) ^ 2 - (x : ℤ) + 1) := by ring
  apply (Int.natCast_inj).mp
  have hx : x ≤ x ^ 2 + 1 := by
    cases x with
    | zero => simp
    | succ n =>
      have : n + 1 ≤ (n + 1) ^ 2 := Nat.le_self_pow (by omega) _
      omega
  have hcast : ((x ^ 2 - x + 1 : ℕ) : ℤ) = (x : ℤ) ^ 2 - x + 1 := by
    have h1 : ((x ^ 2 + 1 - x : ℕ) : ℤ) = (x : ℤ) ^ 2 + 1 - x := by
      rw [Nat.cast_sub hx]; push_cast; rfl
    rw [← geom_cube_odd] at h1
    convert h1 using 1
    push_cast; ring
  rw [Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_one, hcast, Nat.cast_add,
      Nat.cast_one]
  exact hZ


lemma sq_sub_x_add_one_odd {x : ℕ} (hx : Odd x) : Odd (x ^ 2 - x + 1) := by
  have hpos : 1 ≤ x := Odd.pos hx
  have hle : x ≤ x ^ 2 := Nat.le_self_pow (by omega) _
  have hx2 : Odd (x ^ 2) := Odd.pow hx
  have he : Even (x ^ 2 - x) := by
    rw [Nat.even_sub hle]
    constructor
    · intro hEven
      exact absurd hEven (Nat.not_even_iff_odd.mpr hx2)
    · intro hEven
      exact absurd hEven (Nat.not_even_iff_odd.mpr hx)
  change Odd ((x ^ 2 - x) + 1)
  rw [Nat.odd_iff]
  have : (x ^ 2 - x) % 2 = 0 := Nat.even_iff.mp he
  omega

lemma gcd_add_mul_right_self (a b c : ℕ) : Nat.gcd a (a * b + c) = Nat.gcd a c := by
  rw [Nat.gcd_comm]
  have := Nat.gcd_add_mul_right_left c a b
  -- gcd (c + a*b) a = gcd c a
  simpa [Nat.add_comm, Nat.mul_comm, Nat.gcd_comm] using this

lemma gcd_succ_cubic (x : ℕ) :
    Nat.gcd (x + 1) (x ^ 2 - x + 1) = Nat.gcd (x + 1) 3 := by
  rcases lt_or_ge x 2 with hx | hx
  · interval_cases x <;> simp
  · -- x ≥ 2: x^2 - x + 1 = (x+1)*(x-2) + 3
    have hdecomp : x ^ 2 - x + 1 = (x + 1) * (x - 2) + 3 := by
      have hx2 : 2 ≤ x := hx
      have : x - 2 + 2 = x := Nat.sub_add_cancel hx2
      have hZ : ((x : ℤ) ^ 2 - x + 1) = ((x : ℤ) + 1) * ((x : ℤ) - 2) + 3 := by ring
      apply Int.ofNat_inj.mp
      have hL : ((x ^ 2 - x + 1 : ℕ) : ℤ) = (x : ℤ) ^ 2 - x + 1 := by
        have : x ≤ x ^ 2 := Nat.le_self_pow (by omega) _
        have h1 : ((x ^ 2 - x : ℕ) : ℤ) = (x : ℤ) ^ 2 - x := by
          rw [Nat.cast_sub this]; push_cast; rfl
        rw [Nat.cast_add, h1]; push_cast; rfl
      have hR : (((x + 1) * (x - 2) + 3 : ℕ) : ℤ) =
          ((x : ℤ) + 1) * ((x : ℤ) - 2) + 3 := by
        have : ((x - 2 : ℕ) : ℤ) = (x : ℤ) - 2 := by
          rw [Nat.cast_sub hx2]; push_cast; rfl
        push_cast
        rw [this]
      rw [hL, hR]
      exact hZ
    rw [hdecomp]
    simpa [Nat.mul_comm] using gcd_add_mul_right_self (x + 1) (x - 2) 3

lemma y_pos_of_sq_eq_cube_add_two {x y : ℕ} (h : y ^ 2 = x ^ 3 + 2) : 1 ≤ y := by
  have : 2 ≤ y ^ 2 := by
    rw [h]; omega
  have : 1 ≤ y := by
    by_contra hy
    interval_cases y <;> simp at this
  exact this

lemma factor_y_sq_sub_one {x y : ℕ} (h : y ^ 2 = x ^ 3 + 2) :
    (y - 1) * (y + 1) = (x + 1) * (x ^ 2 - x + 1) := by
  have hy : 1 ≤ y := y_pos_of_sq_eq_cube_add_two h
  have : (y - 1) * (y + 1) = y ^ 2 - 1 := by
    have hsq := Nat.sq_sub_sq y 1
    simpa [Nat.mul_comm, one_pow] using hsq.symm
  have h1 : x ^ 3 + 2 - 1 = x ^ 3 + 1 := by omega
  rw [this, h, h1, cube_add_one_factor]

lemma even_pred_of_odd {y : ℕ} (hy : Odd y) (hy1 : 1 ≤ y) : Even (y - 1) := by
  rw [Nat.even_sub hy1]
  constructor
  · intro hyE
    exact absurd hyE (Nat.not_even_iff_odd.mpr hy)
  · intro h1
    exact absurd h1 (by decide : ¬Even 1)

lemma gcd_y_pred_succ {y : ℕ} (hy : Odd y) (hy1 : 1 ≤ y) :
    Nat.gcd (y - 1) (y + 1) = 2 := by
  have h2 : Nat.gcd (y - 1) (y + 1) = Nat.gcd (y - 1) 2 := by
    have : y + 1 = (y - 1) * 1 + 2 := by omega
    rw [this, gcd_add_mul_right_self]
  have hdiv : 2 ∣ y - 1 := even_iff_two_dvd.mp (even_pred_of_odd hy hy1)
  have : Nat.gcd (y - 1) 2 = 2 := by
    have hdvd : Nat.gcd (y - 1) 2 ∣ 2 := Nat.gcd_dvd_right _ _
    have hpos : 0 < Nat.gcd (y - 1) 2 := Nat.gcd_pos_of_pos_right _ (by decide)
    have hle : Nat.gcd (y - 1) 2 ≤ 2 := Nat.le_of_dvd (by decide) hdvd
    have hcases : Nat.gcd (y - 1) 2 = 1 ∨ Nat.gcd (y - 1) 2 = 2 := by omega
    rcases hcases with h1 | h2'
    · have : 2 ∣ Nat.gcd (y - 1) 2 := Nat.dvd_gcd hdiv (dvd_refl 2)
      rw [h1] at this
      omega
    · exact h2'
  rwa [h2]

/-- `x^2 - x + 1 ≥ (x^2)/2` for `x ≥ 3`. -/
lemma geom_cube_ge {x : ℕ} (hx : 3 ≤ x) : x ^ 2 / 2 ≤ x ^ 2 - x + 1 := by
  have : x ≤ x ^ 2 / 2 := by
    have : 2 * x ≤ x ^ 2 := by
      have : 2 ≤ x := by omega
      have := Nat.mul_le_mul_left x this
      nlinarith
    omega
  omega

/-- If `y - 1 ≥ x ^ 2 - x + 1` and `y ^ 2 = x ^ 3 + 2` with `x ≥ 2`, contradiction. -/
lemma large_pred_impossible {x y : ℕ} (hx : 2 ≤ x) (h : y ^ 2 = x ^ 3 + 2)
    (hle : x ^ 2 - x + 1 ≤ y - 1) : False := by
  have hy1 : 1 ≤ y := y_pos_of_sq_eq_cube_add_two h
  have hy : x ^ 2 - x + 2 ≤ y := by omega
  have : (x ^ 2 - x + 2) ^ 2 ≤ y ^ 2 := Nat.pow_le_pow_left hy 2
  rw [h] at this
  have hx2 : x ≤ x ^ 2 := Nat.le_self_pow (by omega) _
  have hZ : ((x ^ 2 - x + 2 : ℕ) : ℤ) ^ 2 ≤ (x : ℤ) ^ 3 + 2 := by exact_mod_cast this
  have hL : ((x ^ 2 - x + 2 : ℕ) : ℤ) = (x : ℤ) ^ 2 - x + 2 := by
    have : ((x ^ 2 - x : ℕ) : ℤ) = (x : ℤ) ^ 2 - x := by
      rw [Nat.cast_sub hx2]; push_cast; rfl
    rw [Nat.cast_add, this]; push_cast; rfl
  rw [hL] at hZ
  nlinarith [sq_nonneg ((x : ℤ) - 2), sq_nonneg ((x : ℤ) - 1)]

/-- The `A = Φ` alignment: `y - 1` is a multiple of `x^2 - x + 1`. -/
lemma case_A_eq_Phi {x y : ℕ} (hx : 2 ≤ x) (h : y ^ 2 = x ^ 3 + 2)
    (hdvd : x ^ 2 - x + 1 ∣ y - 1) : False := by
  have : x ^ 2 - x + 1 ≤ y - 1 := by
    have hpos : 0 < x ^ 2 - x + 1 := by
      have : x ≤ x ^ 2 := Nat.le_self_pow (by omega) _
      omega
    exact Nat.le_of_dvd (by
      have hy : 1 ≤ y := y_pos_of_sq_eq_cube_add_two h
      have : 2 ≤ y ^ 2 := by rw [h]; omega
      have : 2 ≤ y := by
        by_contra hy'
        interval_cases y <;> omega
      omega) hdvd
  exact large_pred_impossible hx h this

lemma even_succ_of_odd {n : ℕ} (h : Odd n) : Even (n + 1) := by
  rw [Nat.even_iff]
  have : n % 2 = 1 := Nat.odd_iff.mp h
  omega

lemma odd_succ_of_even {n : ℕ} (h : Even n) : Odd (n + 1) := by
  rw [Nat.odd_iff]
  have : n % 2 = 0 := Nat.even_iff.mp h
  omega

/-- `4x^2 - 5x - 1 = 0` has no natural solution. -/
lemma no_nat_root_four_five_one {x : ℕ} (h : 4 * x ^ 2 = 5 * x + 1) : False := by
  have hZ : (4 : ℤ) * x ^ 2 - 5 * x - 1 = 0 := by
    exact_mod_cast (by omega : 4 * x ^ 2 - 5 * x - 1 = 0)
  have hdisc : (5 : ℤ) ^ 2 + 16 = 41 := by norm_num
  -- (8x - 5)^2 = 25 + 32 = 57? Use (2x-1)(2x) ≈ x
  -- 4x^2 - 5x - 1 = 0 ⇒ (8x-5)^2 = 25+32=57 not square
  have : ((8 : ℤ) * x - 5) ^ 2 = 25 + 32 * x ^ 2 wait
  -- From 4x^2 = 5x+1, multiply by 4: 16x^2 = 20x+4, (4x- something)
  have : (8 * x - 5) ^ 2 = 41 := by
    have : (8 * x - 5 : ℤ) ^ 2 = 64 * x ^ 2 - 80 * x + 25 := by ring
    have : (4 : ℤ) * x ^ 2 = 5 * x + 1 := by exact_mod_cast h
    nlinarith
  have : ¬ IsSquare (41 : ℤ) := by
    intro ⟨k, hk⟩
    have hk' : k ^ 2 = 41 := by rw [← hk]; simp [sq]
    have habs : |k| ≤ 7 := by
      have : k ^ 2 < (7 : ℤ) ^ 2 + 1 := by nlinarith
      have : |k| ≤ 7 := by
        have : k ^ 2 ≤ 49 := by nlinarith
        have := abs_le_of_sq_le_sq this (by decide : (0 : ℤ) ≤ 7)
        -- |k|^2 ≤ 49 ⇒ |k| ≤ 7
        have : |k| ^ 2 ≤ 7 ^ 2 := by simpa [sq_abs] using this
        exact le_of_abs_le ?_
        sorry
      exact this
    have : |k| = 6 ∨ |k| = 7 := by
      have : 6 ≤ |k| := by
        have : (6 : ℤ) ^ 2 ≤ k ^ 2 := by nlinarith
        exact le_abs.mpr ?_
        sorry
      omega
    rcases this with h6 | h7
    · rcases eq_or_eq_neg_of_abs_eq h6 with rfl | rfl <;> norm_num at hk'
    · rcases eq_or_eq_neg_of_abs_eq h7 with rfl | rfl <;> norm_num at hk'
  exact this ⟨8 * x - 5, by simp [sq]; linarith⟩





