import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false

open Nat

lemma add_one_pow_sub_pow_ge_three {y n : ℕ} (hn : 2 ≤ n) (hy : 1 ≤ y) :
    3 ≤ (y + 1) ^ n - y ^ n := by
  have hZ : (3 : ℤ) ≤ ((y + 1 : ℕ) : ℤ) ^ n - (y : ℤ) ^ n := by
    have hnm : n = n - 2 + 2 := by omega
    have hsq : ((y + 1 : ℕ) : ℤ) ^ 2 - (y : ℤ) ^ 2 = 2 * y + 1 := by
      push_cast; ring
    have hle : (y : ℤ) ^ (n - 2) ≤ ((y + 1 : ℕ) : ℤ) ^ (n - 2) := by
      exact_mod_cast Nat.pow_le_pow_left (Nat.le_succ y) (n - 2)
    have hdecomp : ((y + 1 : ℕ) : ℤ) ^ n - (y : ℤ) ^ n
        = ((y + 1 : ℕ) : ℤ) ^ (n - 2) * ((y + 1 : ℕ) : ℤ) ^ 2
          - (y : ℤ) ^ (n - 2) * (y : ℤ) ^ 2 := by
      conv_lhs => rw [hnm]
      rw [pow_add, pow_add]
    have hge : ((y + 1 : ℕ) : ℤ) ^ (n - 2) * (((y + 1 : ℕ) : ℤ) ^ 2 - (y : ℤ) ^ 2)
        ≤ ((y + 1 : ℕ) : ℤ) ^ (n - 2) * ((y + 1 : ℕ) : ℤ) ^ 2
          - (y : ℤ) ^ (n - 2) * (y : ℤ) ^ 2 := by
      nlinarith
    have ha : (1 : ℤ) ≤ ((y + 1 : ℕ) : ℤ) ^ (n - 2) := by
      exact_mod_cast (Nat.one_le_pow (n - 2) (y + 1) (by omega))
    nlinarith
  have hnn : y ^ n ≤ (y + 1) ^ n := Nat.pow_le_pow_left (Nat.le_succ y) n
  exact_mod_cast hZ

lemma pow_sub_pow_ge_three {x y n : ℕ} (hn : 2 ≤ n) (hy : 1 ≤ y) (hxy : y < x) :
    3 ≤ x ^ n - y ^ n := by
  have hx : y + 1 ≤ x := by omega
  have hle : (y + 1) ^ n ≤ x ^ n := Nat.pow_le_pow_left hx n
  have hgap := add_one_pow_sub_pow_ge_three hn hy
  omega

lemma pow_sub_pow_ne_two {x y n : ℕ} (hn : 2 ≤ n) (hy : 1 ≤ y) (hxy : y < x) :
    x ^ n - y ^ n ≠ 2 := by
  have := pow_sub_pow_ge_three hn hy hxy
  omega

lemma gcd_exponents_eq_one {p q ea eb : ℕ}
    (hp : 2 ≤ p) (hq : 2 ≤ q) (_hea : 2 ≤ ea) (_heb : 2 ≤ eb)
    (hdiff : q ^ eb = p ^ ea + 2) : Nat.gcd ea eb = 1 := by
  let d := Nat.gcd ea eb
  have hd_dvd_a : d ∣ ea := Nat.gcd_dvd_left ea eb
  have hd_dvd_b : d ∣ eb := Nat.gcd_dvd_right ea eb
  obtain ⟨ea', hea'⟩ := hd_dvd_a
  obtain ⟨eb', heb'⟩ := hd_dvd_b
  have hp_pow : p ^ ea = (p ^ ea') ^ d := by
    rw [hea', mul_comm d ea', pow_mul]
  have hq_pow : q ^ eb = (q ^ eb') ^ d := by
    rw [heb', mul_comm d eb', pow_mul]
  have hpow : (q ^ eb') ^ d = (p ^ ea') ^ d + 2 := by
    rwa [← hq_pow, ← hp_pow]
  by_contra hne
  have hdpos : 0 < d := Nat.gcd_pos_of_pos_left eb (by omega)
  have hd2 : 2 ≤ d := by
    have : d ≠ 1 := hne
    omega
  have hbase : 0 < p ^ ea' := pow_pos (by omega) _
  have hqp : p ^ ea' < q ^ eb' := by
    have hlt' : (p ^ ea') ^ d < (q ^ eb') ^ d := by omega
    exact (Nat.pow_lt_pow_iff_left (Nat.ne_of_gt hdpos)).mp hlt'
  have hy : 1 ≤ p ^ ea' := hbase
  apply pow_sub_pow_ne_two (x := q ^ eb') (y := p ^ ea') (n := d) hd2 hy hqp
  omega

lemma cubes_diff_two {x y : ℕ} (h : x ^ 3 = y ^ 3 + 2) : False := by
  have hyx : y < x := by
    by_contra hle
    have : x ^ 3 ≤ y ^ 3 := Nat.pow_le_pow_left (Nat.le_of_not_lt hle) 3
    omega
  rcases Nat.eq_zero_or_pos y with hy0 | hy1
  · subst hy0
    have : x ^ 3 = 2 := h
    have hxle : x ≤ 1 := by
      by_contra hx
      have : 2 ≤ x := by omega
      have : 8 ≤ x ^ 3 := calc
        8 = 2 ^ 3 := by norm_num
        _ ≤ x ^ 3 := Nat.pow_le_pow_left this 3
      omega
    interval_cases x <;> norm_num at this
  · exact pow_sub_pow_ne_two (by decide : (2 : ℕ) ≤ 3) hy1 hyx (by omega)

lemma add_one_pow_gt_pow_add_two {p a : ℕ} (hp : 2 ≤ p) (ha : 3 ≤ a) :
    p ^ a + 2 < (p + 1) ^ a := by
  have hgap := add_one_pow_sub_pow_ge_three (y := p) (n := a) (by omega) (by omega)
  omega
