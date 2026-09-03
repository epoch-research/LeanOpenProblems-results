import FormalConjecturesUtil

/-! Pairwise nonresonance for the two largest odd moduli. -/

namespace Erdos7Reduction

private theorem stdAddChar_mul_int (m k : ℕ) [NeZero m] [NeZero k] (u v : ℤ) :
    ZMod.stdAddChar (u : ZMod m) * ZMod.stdAddChar (v : ZMod k) =
      ZMod.stdAddChar ((u * k + v * m : ℤ) : ZMod (m * k)) := by
  rw [ZMod.stdAddChar_coe, ZMod.stdAddChar_coe, ZMod.stdAddChar_coe,
    ← Complex.exp_add]
  congr 1
  push_cast
  have hm : (m : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne m)
  have hk : (k : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne k)
  field_simp

private theorem stdAddChar_int_eq_one_iff (m : ℕ) [NeZero m] (u : ℤ) :
    ZMod.stdAddChar (u : ZMod m) = 1 ↔ (m : ℤ) ∣ u := by
  rw [← (ZMod.stdAddChar (N := m)).map_zero_eq_one,
    ZMod.injective_stdAddChar.eq_iff, ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- An odd pair cannot resonate positively with a smaller modulus. -/
theorem odd_pair_add_nonresonance (m k n : ℕ) (hm : Odd m) (hk : Odd k)
    (hn : 0 < n) (hnm : n < m) (hnk : n < k) :
    ¬ m * k ∣ n * k + n * m := by
  intro hd
  have hk0 : 0 < k := by omega
  have hp : 0 < n * k + n * m := by positivity
  have hlt : n * k + n * m < 2 * (m * k) := by
    have h₁ := Nat.mul_lt_mul_of_pos_right hnm (by omega : 0 < k)
    have h₂ := Nat.mul_lt_mul_of_pos_right hnk (by omega : 0 < m)
    nlinarith
  have heq := Nat.eq_of_dvd_of_lt_two_mul (ne_of_gt hp) hd hlt
  have he : Even (m * k) := by
    rw [← heq, ← Nat.mul_add]
    exact (hk.add_odd hm).mul_left n
  exact (Nat.not_even_iff_odd.mpr (hm.mul hk)) he

/-- The difference of reciprocal characters of distinct moduli cannot resonate
with a smaller modulus. This part does not require oddness. -/
theorem pair_sub_nonresonance (m k n : ℕ) (hn : 0 < n)
    (hnk : n < k) (hkm : k < m) :
    ¬ (m * k : ℤ) ∣ (n : ℤ) * k - (n : ℤ) * m := by
  intro hd
  have hd' : m * k ∣ n * (m - k) := by
    apply Int.natCast_dvd_natCast.mp
    convert dvd_neg.mpr hd using 1
    push_cast [Nat.cast_sub hkm.le]
    ring
  have hpos : 0 < n * (m - k) := Nat.mul_pos hn (Nat.sub_pos_of_lt hkm)
  have hlt : n * (m - k) < m * k := by
    have h₁ := Nat.mul_lt_mul_of_pos_right hnk (Nat.sub_pos_of_lt hkm)
    have hsub : m - k + k = m := Nat.sub_add_cancel hkm.le
    nlinarith
  exact (not_lt_of_ge (Nat.le_of_dvd hpos hd')) hlt

/-- Both mixed character frequencies are nontrivial below the two largest odd moduli. -/
theorem odd_pair_character_nonresonance (m k n : ℕ) (hm : Odd m) (hk : Odd k)
    (hn : 0 < n) (hnk : n < k) (hkm : k < m) :
    letI : NeZero m := ⟨by omega⟩
    letI : NeZero k := ⟨by omega⟩
    ZMod.stdAddChar (n : ZMod m) * ZMod.stdAddChar (n : ZMod k) ≠ 1 ∧
      ZMod.stdAddChar (n : ZMod m) * ZMod.stdAddChar (-(n : ℤ) : ZMod k) ≠ 1 := by
  letI : NeZero m := ⟨by omega⟩
  letI : NeZero k := ⟨by omega⟩
  constructor
  · intro h
    have hz : (m * k : ℤ) ∣ (n : ℤ) * k + (n : ℤ) * m := by
      apply (stdAddChar_int_eq_one_iff (m * k) _).mp
      rw [← stdAddChar_mul_int]
      simpa only [Int.cast_natCast, Int.cast_neg] using h
    have hnat : m * k ∣ n * k + n * m := by exact_mod_cast hz
    exact odd_pair_add_nonresonance m k n hm hk hn (lt_trans hnk hkm) hnk hnat
  · intro h
    have hz : (m * k : ℤ) ∣ (n : ℤ) * k - (n : ℤ) * m := by
      apply (stdAddChar_int_eq_one_iff (m * k) _).mp
      rw [sub_eq_add_neg, ← neg_mul, ← stdAddChar_mul_int]
      simpa only [Int.cast_natCast, Int.cast_neg] using h
    exact pair_sub_nonresonance m k n hn hnk hkm hz

#print axioms odd_pair_character_nonresonance
end Erdos7Reduction
