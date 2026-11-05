import Submission.TypeIIOffsetBound

/-!
# A reciprocal cofactor test for the full Type-II axis

The exact modular test can be applied to either factor of `m² = d*v`:
`(4*m-1) ∣ p+4*d` if and only if `(4*m-1) ∣ 4*v*p+1`.
The equivalence is elementary and does not assert existence of a witness.
The file does not import or modify `Submission.Spec`.
-/

namespace Erdos242

/-- The complementary square divisor `v=m²/d` changes a Type-II congruence
into a factor test for `4vp+1`. No primality hypothesis is needed. -/
theorem typeII_reciprocal_congruence (p m d v : ℕ) (hm : 0 < m)
    (hdv : d * v = m ^ 2) :
    (4 * m - 1 ∣ p + 4 * d) ↔ (4 * m - 1 ∣ 4 * v * p + 1) := by
  let h := 4 * m - 1
  have hh : h + 1 = 4 * m := by dsimp [h]; omega
  have hsquare : 16 * m ^ 2 = 1 + h * (h + 2) := by
    calc
      16 * m ^ 2 = (4 * m) ^ 2 := by ring
      _ = (h + 1) ^ 2 := by rw [hh]
      _ = 1 + h * (h + 2) := by ring
  have hfactor : 4 * v * (p + 4 * d) = (4 * v * p + 1) + h * (h + 2) := by
    calc
      4 * v * (p + 4 * d) = 4 * v * p + 16 * (d * v) := by ring
      _ = 4 * v * p + 16 * m ^ 2 := by rw [hdv]
      _ = (4 * v * p + 1) + h * (h + 2) := by omega
  have hcop4m : h.Coprime (4 * m) := by
    rw [← hh]
    exact Nat.coprime_self_add_right.mpr (Nat.coprime_one_right h)
  have hcop4 : h.Coprime 4 := hcop4m.of_dvd_right (dvd_mul_right 4 m)
  have hcopm : h.Coprime m := hcop4m.of_dvd_right (dvd_mul_left m 4)
  have hvdvd : v ∣ m ^ 2 := by
    rw [← hdv]
    exact dvd_mul_left v d
  have hcopv : h.Coprime v := (hcopm.pow_right 2).of_dvd_right hvdvd
  have hcop : h.Coprime (4 * v) := hcop4.mul_right hcopv
  change (h ∣ p + 4 * d) ↔ (h ∣ 4 * v * p + 1)
  constructor
  · intro hw
    have hsum : h ∣ (4 * v * p + 1) + h * (h + 2) := by
      rw [← hfactor]
      exact hw.mul_left (4 * v)
    exact (Nat.dvd_add_iff_left (dvd_mul_right h (h + 2))).mpr hsum
  · intro hw
    have hsum : h ∣ (4 * v * p + 1) + h * (h + 2) :=
      dvd_add hw (dvd_mul_right h (h + 2))
    have hprod : h ∣ (4 * v) * (p + 4 * d) := by
      rw [hfactor]
      exact hsum
    exact hcop.dvd_of_dvd_mul_left hprod

/-- An exact dual of `FullSquareAxis`: search instead over factors of `4vp+1`
with `v∣m²`. The size inequality `4m²<vp` is equivalent to `4d<p`
for `d=m²/v`; on hard primes the `m` bound is automatic. -/
theorem full_square_axis_iff_reciprocal (p : ℕ) (hp24 : p % 24 = 1) :
    FullSquareAxis p ↔
      ∃ m v : ℕ, 0 < m ∧ 0 < v ∧ v ∣ m ^ 2 ∧
        4 * m ^ 2 < v * p ∧ 4 * m - 1 ∣ 4 * v * p + 1 := by
  constructor
  · rintro ⟨m, d, hm, _, hd, hdsq, hsmall, hdiv⟩
    let v := m ^ 2 / d
    have hdv : d * v = m ^ 2 := Nat.mul_div_cancel' hdsq
    have hv : 0 < v := Nat.pos_of_mul_pos_left (by rw [hdv]; positivity)
    have hvdiv : v ∣ m ^ 2 := by
      rw [← hdv]
      exact dvd_mul_left v d
    have hsize : 4 * m ^ 2 < v * p := by
      calc
        4 * m ^ 2 = v * (4 * d) := by rw [← hdv]; ring
        _ < v * p := (Nat.mul_lt_mul_left hv).mpr hsmall
    exact ⟨m, v, hm, hv, hvdiv, hsize,
      (typeII_reciprocal_congruence p m d v hm hdv).mp hdiv⟩
  · rintro ⟨m, v, hm, hv, hvdiv, hsize, hrecip⟩
    let d := m ^ 2 / v
    have hvd : v * d = m ^ 2 := Nat.mul_div_cancel' hvdiv
    have hd : 0 < d := Nat.pos_of_mul_pos_left (by rw [hvd]; positivity)
    have hdsq : d ∣ m ^ 2 := by
      rw [← hvd]
      exact dvd_mul_left d v
    have hsmall : 4 * d < p := by
      apply (Nat.mul_lt_mul_left hv).mp
      calc
        v * (4 * d) = 4 * m ^ 2 := by rw [← hvd]; ring
        _ < v * p := hsize
    have hdv : d * v = m ^ 2 := by rw [mul_comm]; exact hvd
    have hdiv : 4 * m - 1 ∣ p + 4 * d :=
      (typeII_reciprocal_congruence p m d v hm hdv).mpr hrecip
    exact ⟨m, d, hm, full_square_axis_bound p m d hp24 hm hsmall hdiv,
      hd, hdsq, hsmall, hdiv⟩

/-- Examples deliberately use `d∣m²`, not the narrower `d∣m` test. -/
example : (4 * 4 - 1 ∣ 4 * 2 * 193 + 1) ∧
    (4 * 12 - 1 ∣ 4 * 9 * 2521 + 1) ∧
    (4 * 10 - 1 ∣ 4 * 2 * 66529 + 1) := by norm_num

end Erdos242
