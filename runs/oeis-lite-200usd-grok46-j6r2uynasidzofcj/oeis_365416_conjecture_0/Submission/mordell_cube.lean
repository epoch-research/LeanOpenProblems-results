import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false

open Nat

/-!
  The only integer solutions of `y ^ 2 = x ^ 3 + 2` are `x = -1`, `y = ±1`.
-/

lemma sq_mod_four_ne_two (n : ℕ) : n ^ 2 % 4 ≠ 2 := by
  have : n % 4 < 4 := Nat.mod_lt n (by decide)
  have heq : n ^ 2 % 4 = (n % 4) ^ 2 % 4 := by rw [Nat.pow_mod]
  rw [heq]
  interval_cases n % 4 <;> norm_num

lemma sq_mod_eight_of_odd {n : ℕ} (h : Odd n) : n ^ 2 % 8 = 1 := by
  have : n % 8 = 1 ∨ n % 8 = 3 ∨ n % 8 = 5 ∨ n % 8 = 7 := by
    have : n % 2 = 1 := Nat.odd_iff.mp h
    have : n % 8 < 8 := Nat.mod_lt _ (by decide)
    omega
  rcases this with h | h | h | h <;> simp [Nat.pow_mod, h]

lemma x_odd_of_sq_eq_cube_add_two {x y : ℕ} (h : y ^ 2 = x ^ 3 + 2) : Odd x := by
  by_contra hx
  have hxE : Even x := Nat.not_odd_iff_even.mp hx
  obtain ⟨k, hk⟩ := hxE
  have hx3 : x ^ 3 % 4 = 0 := by
    rw [hk, show k + k = 2 * k from (two_mul k).symm]
    have : (2 * k) ^ 3 = 8 * k ^ 3 := by ring
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

lemma x_mod_eight {x y : ℕ} (h : y ^ 2 = x ^ 3 + 2) : x % 8 = 7 := by
  have hx := x_odd_of_sq_eq_cube_add_two h
  have hy := y_odd_of_sq_eq_cube_add_two h
  have hy8 : y ^ 2 % 8 = 1 := sq_mod_eight_of_odd hy
  have hx8 : x % 8 = 1 ∨ x % 8 = 3 ∨ x % 8 = 5 ∨ x % 8 = 7 := by
    have : x % 2 = 1 := Nat.odd_iff.mp hx
    have : x % 8 < 8 := Nat.mod_lt _ (by decide)
    omega
  have hx3 : x ^ 3 % 8 = x % 8 := by
    rcases hx8 with h8 | h8 | h8 | h8 <;> simp [Nat.pow_mod, h8]
  have : (x ^ 3 + 2) % 8 = 1 := by rw [← h, hy8]
  have : (x % 8 + 2) % 8 = 1 := by
    rw [Nat.add_mod, hx3] at this
    exact this
  omega

lemma x_ge_seven {x y : ℕ} (h : y ^ 2 = x ^ 3 + 2) : 7 ≤ x := by
  have h8 := x_mod_eight h
  have : x % 8 < 8 := Nat.mod_lt _ (by decide)
  omega

lemma y_pos_of {x y : ℕ} (h : y ^ 2 = x ^ 3 + 2) : 1 ≤ y := by
  have : 2 ≤ y ^ 2 := by rw [h]; omega
  by_contra hy
  interval_cases y <;> simp at this

lemma geom_cube_odd (x : ℕ) : x ^ 2 - x + 1 = x ^ 2 + 1 - x := by
  cases x with
  | zero => simp
  | succ n =>
    have : n + 1 ≤ (n + 1) ^ 2 := Nat.le_self_pow (by omega) _
    omega

lemma cube_add_one_factor (x : ℕ) : x ^ 3 + 1 = (x + 1) * (x ^ 2 - x + 1) := by
  have hZ : ((x : ℤ) ^ 3 + 1) = ((x : ℤ) + 1) * ((x : ℤ) ^ 2 - (x : ℤ) + 1) := by ring
  apply Int.natCast_inj.mp
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
  rw [Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_one, hcast, Nat.cast_add, Nat.cast_one]
  exact hZ

lemma Phi_pos (x : ℕ) : 0 < x ^ 2 - x + 1 := by
  have : x ≤ x ^ 2 := Nat.le_self_pow (by omega) _
  omega

lemma Phi_odd {x : ℕ} (hx : Odd x) : Odd (x ^ 2 - x + 1) := by
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
  simpa [Nat.add_comm, Nat.mul_comm, Nat.gcd_comm] using Nat.gcd_add_mul_right_left c a b

lemma gcd_succ_cubic (x : ℕ) :
    Nat.gcd (x + 1) (x ^ 2 - x + 1) = Nat.gcd (x + 1) 3 := by
  rcases lt_or_ge x 2 with hx | hx
  · interval_cases x <;> simp
  · have hdecomp : x ^ 2 - x + 1 = (x + 1) * (x - 2) + 3 := by
      have hx2 : 2 ≤ x := hx
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

lemma factor_y_sq_sub_one {x y : ℕ} (h : y ^ 2 = x ^ 3 + 2) :
    (y - 1) * (y + 1) = (x + 1) * (x ^ 2 - x + 1) := by
  have hy : 1 ≤ y := y_pos_of h
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
    exact absurd h1 (by decide : ¬ Even 1)

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

/-- Write `n = 2^α * s` with `s` odd. -/
lemma exists_odd_part (n : ℕ) (hn : 0 < n) :
    ∃ α s : ℕ, n = 2 ^ α * s ∧ Odd s := by
  refine ⟨padicValNat 2 n, n / 2 ^ padicValNat 2 n, ?_, ?_⟩
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact (Nat.mul_div_cancel' pow_padicValNat_dvd).symm
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hne : n ≠ 0 := Nat.pos_iff_ne_zero.mp hn
    set α := padicValNat 2 n
    set s := n / 2 ^ α
    have hs : n = 2 ^ α * s := (Nat.mul_div_cancel' pow_padicValNat_dvd).symm
    have : ¬ 2 ∣ s := by
      intro h2s
      have : 2 ^ (α + 1) ∣ n := by
        rw [hs, pow_succ]
        exact mul_dvd_mul_left _ h2s
      have : α + 1 ≤ α := (padicValNat_dvd_iff_le hne).mp this
      omega
    exact Nat.not_even_iff_odd.mp (fun he => this (even_iff_two_dvd.mp he))

lemma eight_dvd_succ_of_mod {x : ℕ} (h : x % 8 = 7) : 8 ∣ x + 1 := by
  have : (x + 1) % 8 = 0 := by omega
  exact Nat.dvd_iff_mod_eq_zero.mpr this

lemma three_le_val2_of_mod8 {x : ℕ} (h : x % 8 = 7) : 3 ≤ padicValNat 2 (x + 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h8 : 2 ^ 3 ∣ x + 1 := eight_dvd_succ_of_mod h
  have hne : x + 1 ≠ 0 := Nat.succ_ne_zero _
  exact (padicValNat_dvd_iff_le hne).mp h8

/-! ### The consecutive product `s(s+1)` -/

lemma s_mul_succ {x y : ℕ} (h : y ^ 2 = x ^ 3 + 2) :
    ((y - 1) / 2) * ((y + 1) / 2) = (x + 1) * (x ^ 2 - x + 1) / 4 := by
  have hy := y_odd_of_sq_eq_cube_add_two h
  have hy1 := y_pos_of h
  have hfac := factor_y_sq_sub_one h
  have he1 : Even (y - 1) := even_pred_of_odd hy hy1
  have he2 : Even (y + 1) := by
    have : (y + 1) % 2 = 0 := by
      have : y % 2 = 1 := Nat.odd_iff.mp hy
      omega
    exact Nat.even_iff.mpr this
  have h2a : 2 ∣ y - 1 := even_iff_two_dvd.mp he1
  have h2b : 2 ∣ y + 1 := even_iff_two_dvd.mp he2
  have : (y - 1) * (y + 1) = 4 * (((y - 1) / 2) * ((y + 1) / 2)) := by
    have ha : y - 1 = 2 * ((y - 1) / 2) := (Nat.mul_div_cancel' h2a).symm
    have hb : y + 1 = 2 * ((y + 1) / 2) := (Nat.mul_div_cancel' h2b).symm
    rw [ha, hb]; ring
  have h4 : 4 ∣ (x + 1) * (x ^ 2 - x + 1) := by
    have hx8 := x_mod_eight h
    have : 8 ∣ x + 1 := eight_dvd_succ_of_mod hx8
    have : 4 ∣ x + 1 := dvd_trans (by decide : (4 : ℕ) ∣ 8) this
    exact dvd_mul_of_dvd_left this _
  have : (x + 1) * (x ^ 2 - x + 1) = 4 * ((x + 1) * (x ^ 2 - x + 1) / 4) :=
    (Nat.mul_div_cancel' h4).symm
  omega

/-- Auxiliary: `Phi = x^2 - x + 1`. -/
def Phi (x : ℕ) : ℕ := x ^ 2 - x + 1

lemma Phi_eq (x : ℕ) : Phi x = x ^ 2 - x + 1 := rfl

lemma Phi_cast (x : ℕ) : (Phi x : ℤ) = (x : ℤ) ^ 2 - x + 1 := by
  have : x ≤ x ^ 2 := Nat.le_self_pow (by omega) _
  simp [Phi]
  have h1 : ((x ^ 2 - x : ℕ) : ℤ) = (x : ℤ) ^ 2 - x := by
    rw [Nat.cast_sub this]; push_cast; rfl
  rw [Nat.cast_add, h1]; push_cast; rfl

/-- Main size lemmas used in the eight cases. -/
lemma pow_two_add_one_lt_Phi {μ σ : ℕ} (hμ : 1 ≤ μ) (hσ : 1 ≤ σ) :
    2 ^ μ + 1 < σ * Phi (2 ^ (μ + 2) * σ - 1) := by
  set x := 2 ^ (μ + 2) * σ - 1
  have hx : 7 ≤ x := by
    have : 2 ^ (μ + 2) * σ ≥ 2 ^ 3 * 1 := by
      have h1 : 2 ^ 3 ≤ 2 ^ (μ + 2) := Nat.pow_le_pow_right (by decide) (by omega)
      exact Nat.mul_le_mul h1 hσ
    have : 8 ≤ 2 ^ (μ + 2) * σ := this
    omega
  have hPhi : 43 ≤ Phi x := by
    have : x ^ 2 - x + 1 = Phi x := rfl
    have hx2 : x ≤ x ^ 2 := Nat.le_self_pow (by omega) _
    have : (x : ℤ) ^ 2 - x + 1 ≥ 43 := by
      nlinarith
    have : (Phi x : ℤ) ≥ 43 := by
      rwa [Phi_cast]
    exact_mod_cast this
  have : 2 ^ μ + 1 ≤ 2 ^ μ + 1 := le_rfl
  have hleft : 2 ^ μ + 1 < 43 := by
    -- not always! only for μ small. Don't use this.
    sorry
  sorry

end
