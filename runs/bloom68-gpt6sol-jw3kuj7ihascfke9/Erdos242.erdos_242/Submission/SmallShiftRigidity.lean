import Submission.FullSquareAxis
import Submission.MinusTwoBarrier

/-!
# Rigidity of the first three positive shifts in the full Type-II divisor axis

This file contains conditional statements, not a proof of universal pointwise
coverage. It neither imports nor changes `Submission.Spec`.
-/

namespace Erdos242

/-- If `4m-1` divides `4d-r` for `1≤r≤3` and `d∣m²`, then the *only*
possible square-divisor choice is `d=r*m`; in particular `r∣m`.
The restriction `r≤3` ensures `4d-r>0`: for `r=4`, `d=1` instead gives
`4d-r=0` for every `m`. -/
theorem short_positive_shift_rigid (m d r : ℕ) (hm : 0 < m) (hd : 0 < d)
    (hrpos : 0 < r) (hrsmall : r ≤ 3) (hdsq : d ∣ m ^ 2)
    (hdiv : 4 * m - 1 ∣ 4 * d - r) : d = r * m ∧ r ∣ m := by
  let h := 4 * m - 1
  let e := m ^ 2 / d
  let t := (4 * d - r) / h
  have hh : h + 1 = 4 * m := by dsimp [h]; omega
  have hde : d * e = m ^ 2 := Nat.mul_div_cancel' hdsq
  have hepos : 0 < e := by
    by_contra hn
    have he0 : e = 0 := Nat.eq_zero_of_not_pos hn
    rw [he0] at hde
    nlinarith only [hde, hm]
  have hdr : (4 * d - r) + r = 4 * d := by omega
  have hdt : h * t = 4 * d - r := Nat.mul_div_cancel' hdiv
  have hht := congrArg (fun v : ℕ => v * t) hh
  have hmodid : 4 * (m * t) + r = t + 4 * d := by
    nlinarith only [hht, hdt, hdr]
  have htmod : t % 4 = r := by
    have hmod : (t + 4 * d) % 4 = r % 4 := by rw [← hmodid]; omega
    omega
  have htge : r ≤ t := by
    have hle : t % 4 ≤ t := Nat.mod_le _ _
    omega
  have hhr := congrArg (fun v : ℕ => r * v) hh
  have hmul : h * r ≤ h * t := Nat.mul_le_mul_left h htge
  have hdge : r * m ≤ d := by
    nlinarith only [hdt, hdr, hhr, hmul]
  have hhm := congrArg (fun v : ℕ => v * (4 * m + 1)) hh
  have hsq : 16 * m ^ 2 = h * (4 * m + 1) + 1 := by
    nlinarith only [hhm]
  have hrepos : 0 < r * e := Nat.mul_pos hrpos hepos
  have here : (4 * r * e - 1) + 1 = 4 * r * e := by
    have hge : 1 < 4 * r * e := by nlinarith only [hrepos]
    omega
  have hcombine : 4 * e * (4 * d - r) + 4 * r * e = 16 * (d * e) := by
    have hdre := congrArg (fun v : ℕ => 4 * e * v) hdr
    nlinarith only [hdre]
  have hident : 4 * e * (4 * d - r) + (4 * r * e - 1) =
      h * (4 * m + 1) := by
    nlinarith only [hcombine, hde, hsq, here]
  have hdivmul : h ∣ 4 * e * (4 * d - r) := hdiv.mul_left (4 * e)
  have hdivboth : h ∣ 4 * e * (4 * d - r) + (4 * r * e - 1) := by
    rw [hident]
    exact dvd_mul_right h _
  have hdual : h ∣ 4 * r * e - 1 := by
    have hsum : h ∣ (4 * r * e - 1) + 4 * e * (4 * d - r) := by
      simpa only [add_comm] using hdivboth
    exact (Nat.dvd_add_iff_left hdivmul).mpr hsum
  have hle : h ≤ 4 * r * e - 1 := by
    have hpos : 0 < 4 * r * e - 1 := by
      have hassoc : 4 * r * e = 4 * (r * e) := by ring
      rw [hassoc]
      omega
    exact Nat.le_of_dvd hpos hdual
  have herege : m ≤ r * e := by
    have hassoc : 4 * r * e = 4 * (r * e) := by ring
    rw [hassoc] at hle
    dsimp [h] at hle
    omega
  have hdre := congrArg (fun v : ℕ => r * v) hde
  have htarget : d * (r * e) = (r * m) * m := by nlinarith only [hdre]
  have hdle : d ≤ r * m := by
    by_contra hn
    have hlt : (r * m) * m < d * m :=
      Nat.mul_lt_mul_of_pos_right (by omega) hm
    have hle' : d * m ≤ d * (r * e) := Nat.mul_le_mul_left d herege
    omega
  have hd_eq : d = r * m := by omega
  have hcancel : m * (r * e) = m * m := by
    calc
      m * (r * e) = (r * m) * e := by ring
      _ = d * e := by rw [hd_eq]
      _ = m ^ 2 := hde
      _ = m * m := by ring
  have hre : r * e = m := Nat.eq_of_mul_eq_mul_left hm hcancel
  exact ⟨hd_eq, ⟨e, by simpa only [mul_comm] using hre.symm⟩⟩

/-- The full `d∣m²` condition provides no extra choices **within** the
`p+1,p+2,p+3` divisor tests. A witness with `4m-1∣p+r` already forces
`d=rm` and `r∣m`, whether or not `p` is prime. -/
theorem short_shift_only_canonical (p m d r : ℕ) (hm : 0 < m)
    (hd : 0 < d) (hrpos : 0 < r) (hrsmall : r ≤ 3)
    (hdsq : d ∣ m ^ 2)
    (hshift : 4 * m - 1 ∣ p + r)
    (hcert : 4 * m - 1 ∣ p + 4 * d) : d = r * m ∧ r ∣ m := by
  have hsub : (p + r) + (4 * d - r) = p + 4 * d := by omega
  have hdiff : 4 * m - 1 ∣ 4 * d - r := by
    have hsum : 4 * m - 1 ∣ (p + r) + (4 * d - r) := by
      rw [hsub]
      exact hcert
    have hsum' : 4 * m - 1 ∣ (4 * d - r) + (p + r) := by
      simpa only [add_comm] using hsum
    exact (Nat.dvd_add_iff_left hshift).mpr hsum'
  exact short_positive_shift_rigid m d r hm hd hrpos hrsmall hdsq hdiff

/-- For every number `p=24k+1`, the full Type-II `p+2`-factor strategy is
**exactly** the existence of a divisor `7 (mod 8)` of `p+2`. In particular,
allowing all divisors `d∣m²` does not rescue a `3 (mod 8)` factor here.
This is an equivalence for the `p+2` *subfamily*, not for all Type-II solutions. -/
theorem plus_two_shift_exact (k : ℕ) :
    (∃ m d : ℕ, 0 < m ∧ 0 < d ∧ d ∣ m ^ 2 ∧
      4 * d < 24 * k + 1 ∧
      4 * m - 1 ∣ (24 * k + 1) + 2 ∧
      4 * m - 1 ∣ (24 * k + 1) + 4 * d) ↔
    ∃ h : ℕ, h % 8 = 7 ∧ h ∣ (24 * k + 1) + 2 := by
  constructor
  · rintro ⟨m, d, hm, hd, hdsq, _, hshift, hcert⟩
    have heven : 2 ∣ m :=
      (short_shift_only_canonical (24 * k + 1) m d 2 hm hd
        (by omega) (by omega) hdsq hshift hcert).2
    have hrem : m % 2 = 0 := Nat.mod_eq_zero_of_dvd heven
    refine ⟨4 * m - 1, ?_, hshift⟩
    omega
  · rintro ⟨h, hh8, hshift⟩
    let m := (h + 1) / 4
    let d := 2 * m
    have hform : 4 * m - 1 = h := by dsimp [m]; omega
    have hm : 0 < m := by dsimp [m]; omega
    have hevenrem : m % 2 = 0 := by dsimp [m]; omega
    have heven : 2 ∣ m := Nat.dvd_of_mod_eq_zero hevenrem
    have hd : 0 < d := by dsimp [d]; omega
    have hdsq : d ∣ m ^ 2 := by
      obtain ⟨v, hv⟩ := heven
      refine ⟨v, ?_⟩
      dsimp [d]
      rw [hv]
      ring
    let q := ((24 * k + 1) + 2) / h
    have hq : h * q = (24 * k + 1) + 2 := Nat.mul_div_cancel' hshift
    have hqpos : 0 < q := by
      by_contra hn
      have hq0 : q = 0 := Nat.eq_zero_of_not_pos hn
      rw [hq0] at hq
      simp at hq
    have hhq := congrArg (fun v : ℕ => v * q) (show h + 1 = 4 * m by omega)
    have hmodid : (24 * k + 1) + 2 + q = 4 * (m * q) := by
      nlinarith only [hq, hhq]
    have hqmod : q % 4 = 1 := by omega
    have hqne : q ≠ 1 := by
      intro hqone
      rw [hqone, mul_one] at hq
      omega
    have hqge : 5 ≤ q := by
      have hle : q % 4 ≤ q := Nat.mod_le _ _
      omega
    have hmul : h * 5 ≤ h * q := Nat.mul_le_mul_left h hqge
    have h5 := congrArg (fun v : ℕ => 5 * v) (show h + 1 = 4 * m by omega)
    have hsmall : 4 * d < 24 * k + 1 := by
      dsimp [d]
      nlinarith only [hmul, hq, h5, hm]
    have hshiftcert : 4 * m - 1 ∣ (24 * k + 1) + 4 * d := by
      have heq : (24 * k + 1) + 4 * d = ((24 * k + 1) + 2) + 2 * h := by
        dsimp [d]
        omega
      rw [hform, heq]
      exact dvd_add hshift (dvd_mul_left h 2)
    exact ⟨m, d, hm, hd, hdsq, hsmall, by simpa only [hform] using hshift,
      hshiftcert⟩


/-- A `7 (mod 8)` divisor of `p+2` gives a genuinely ordered solution
via the *full* Type-II modular certificate. This conditional result is
silent when there is no such divisor. -/
theorem good_of_plus_two_seven_mod_eight_divisor (k h : ℕ)
    (hh8 : h % 8 = 7) (hdiv : h ∣ (24 * k + 1) + 2) :
    Good (24 * k + 1) := by
  obtain ⟨m, d, hm, hd, hdsq, hsmall, _, hcert⟩ :=
    (plus_two_shift_exact k).mpr ⟨h, hh8, hdiv⟩
  have hp24 : (24 * k + 1) % 24 = 1 := by omega
  have hw : FullSquareAxis (24 * k + 1) :=
    (full_square_axis_iff (24 * k + 1) hp24).mpr
      ⟨m, d, hm, hd, hdsq, hsmall, hcert⟩
  exact full_square_axis_good (24 * k + 1) hw

/-- The analogous *exact subfamily* for `p+3`: the modulus must be
`11 (mod 12)`, equivalently `3∣m`, and the unique divisor is `d=3m`.
This is not a universal covering statement for hard primes. -/
theorem plus_three_shift_exact (k : ℕ) :
    (∃ m d : ℕ, 0 < m ∧ 0 < d ∧ d ∣ m ^ 2 ∧
      4 * d < 24 * k + 1 ∧
      4 * m - 1 ∣ (24 * k + 1) + 3 ∧
      4 * m - 1 ∣ (24 * k + 1) + 4 * d) ↔
    ∃ h : ℕ, h % 12 = 11 ∧ h ∣ (24 * k + 1) + 3 := by
  constructor
  · rintro ⟨m, d, hm, hd, hdsq, _, hshift, hcert⟩
    have hthree : 3 ∣ m :=
      (short_shift_only_canonical (24 * k + 1) m d 3 hm hd
        (by omega) (by omega) hdsq hshift hcert).2
    have hrem : m % 3 = 0 := Nat.mod_eq_zero_of_dvd hthree
    refine ⟨4 * m - 1, ?_, hshift⟩
    omega
  · rintro ⟨h, hh12, hshift⟩
    let m := (h + 1) / 4
    let d := 3 * m
    have hform : 4 * m - 1 = h := by dsimp [m]; omega
    have hm : 0 < m := by dsimp [m]; omega
    have hthree : 3 ∣ m := Nat.dvd_of_mod_eq_zero (by dsimp [m]; omega)
    have hmge : 3 ≤ m := by
      have hrem : m % 3 = 0 := Nat.mod_eq_zero_of_dvd hthree
      omega
    have hd : 0 < d := by dsimp [d]; omega
    have hdsq : d ∣ m ^ 2 := by
      obtain ⟨v, hv⟩ := hthree
      refine ⟨v, ?_⟩
      dsimp [d]
      rw [hv]
      ring
    let q := ((24 * k + 1) + 3) / h
    have hq : h * q = (24 * k + 1) + 3 := Nat.mul_div_cancel' hshift
    have hqpos : 0 < q := by
      by_contra hn
      have hq0 : q = 0 := Nat.eq_zero_of_not_pos hn
      rw [hq0] at hq
      simp at hq
    have hhq := congrArg (fun v : ℕ => v * q) (show h + 1 = 4 * m by omega)
    have hmodid : (24 * k + 1) + 3 + q = 4 * (m * q) := by
      nlinarith only [hq, hhq]
    have hqmod : q % 4 = 0 := by omega
    have hqge : 4 ≤ q := by
      have hle : q % 4 ≤ q := Nat.mod_le _ _
      omega
    have hmul : h * 4 ≤ h * q := Nat.mul_le_mul_left h hqge
    have h4 := congrArg (fun v : ℕ => 4 * v) (show h + 1 = 4 * m by omega)
    have hsmall : 4 * d < 24 * k + 1 := by
      dsimp [d]
      nlinarith only [hmul, hq, h4, hmge]
    have hshiftcert : 4 * m - 1 ∣ (24 * k + 1) + 4 * d := by
      have heq : (24 * k + 1) + 4 * d = ((24 * k + 1) + 3) + 3 * h := by
        dsimp [d]
        omega
      rw [hform, heq]
      exact dvd_add hshift (dvd_mul_left h 3)
    exact ⟨m, d, hm, hd, hdsq, hsmall, by simpa only [hform] using hshift,
      hshiftcert⟩

/-- Among **all** pairs `d∣m²`, the residue `3 ≡ -4d (mod 4m-1)`
occurs only for `(m,d)=(2,1)` (modulus `7`). A factor of `p-3`
therefore cannot provide a new Type-II witness beyond `7∣p+4`. -/
theorem minus_three_only_m2_d1 (m d : ℕ) (hm : 0 < m) (hd : 0 < d)
    (hdsq : d ∣ m ^ 2) (hdiv : 4 * m - 1 ∣ 3 + 4 * d) :
    m = 2 ∧ d = 1 := by
  let h := 4 * m - 1
  let e := m ^ 2 / d
  let t := (3 + 4 * d) / h
  let u := (12 * e + 1) / h
  have hh : h + 1 = 4 * m := by dsimp [h]; omega
  have hde : d * e = m ^ 2 := Nat.mul_div_cancel' hdsq
  have hdt : h * t = 3 + 4 * d := Nat.mul_div_cancel' hdiv
  have htprod := congrArg (fun v : ℕ => v * t) hh
  have hteq : 3 + 4 * d + t = 4 * (m * t) := by
    nlinarith only [hdt, htprod]
  have ht4 : t % 4 = 1 := by omega
  have ht : t = 1 ∨ 5 ≤ t := by
    have hle : t % 4 ≤ t := Nat.mod_le _ _
    omega
  have hediv : h ∣ 12 * e + 1 := by
    have hdual := (typeII_modular_dual 3 m d hm hdsq).mp hdiv
    simpa only [h, e, Nat.reduceMul, mul_assoc] using hdual
  have hdu : h * u = 12 * e + 1 := Nat.mul_div_cancel' hediv
  have huprod := congrArg (fun v : ℕ => v * u) hh
  have hueq : 12 * e + 1 + u = 4 * (m * u) := by
    nlinarith only [hdu, huprod]
  have hu4 : u % 4 = 3 := by omega
  have huge : 3 ≤ u := by
    have hle : u % 4 ≤ u := Nat.mod_le _ _
    omega
  have hmul : h * 3 ≤ h * u := Nat.mul_le_mul_left h huge
  have hege : m ≤ e := by
    rw [hdu] at hmul
    dsimp [h] at hmul
    omega
  rcases ht with ht | ht
  · have hmd : m = d + 1 := by
      rw [ht, mul_one] at hdt
      dsimp [h] at hdt
      omega
    have hsq : m ^ 2 = d * (d + 2) + 1 := by rw [hmd]; ring
    have hsqdiv : d ∣ d * (d + 2) + 1 := by rw [← hsq]; exact hdsq
    have hone : d ∣ 1 := (Nat.dvd_add_iff_left (dvd_mul_right d (d + 2))).mpr
      (by simpa only [add_comm] using hsqdiv)
    have hdle : d ≤ 1 := Nat.le_of_dvd (by decide) hone
    omega
  · have htlb : h * 5 ≤ h * t := Nat.mul_le_mul_left h ht
    have hdge : 5 * m - 2 ≤ d := by
      rw [hdt] at htlb
      dsimp [h] at htlb
      omega
    have hbound : (5 * m - 2) * m ≤ m ^ 2 := by
      calc
        (5 * m - 2) * m ≤ d * m := Nat.mul_le_mul_right m hdge
        _ ≤ d * e := Nat.mul_le_mul_left d hege
        _ = m ^ 2 := hde
    have hstrict : m ^ 2 < (5 * m - 2) * m := by
      calc
        m ^ 2 = m * m := by ring
        _ < (5 * m - 2) * m :=
          Nat.mul_lt_mul_of_pos_right (by omega) hm
    exact (not_le_of_gt hstrict) hbound |>.elim

/-- For a hard `p=24k+1`, if the Type-II modulus divides `p-3`, it must
be `7` and its square divisor must be `1`; equivalently it already divides
`p+4`. This does not exclude any other modulus for the same prime. -/
theorem hard_minus_three_fiber (k m d : ℕ) (hk : 0 < k)
    (hm : 0 < m) (hd : 0 < d) (hdsq : d ∣ m ^ 2)
    (hminus : 4 * m - 1 ∣ (24 * k + 1) - 3)
    (hcert : 4 * m - 1 ∣ (24 * k + 1) + 4 * d) :
    m = 2 ∧ d = 1 := by
  have heq : ((24 * k + 1) - 3) + (3 + 4 * d) =
      (24 * k + 1) + 4 * d := by omega
  have hsum : 4 * m - 1 ∣ ((24 * k + 1) - 3) + (3 + 4 * d) := by
    rw [heq]
    exact hcert
  have hsum' : 4 * m - 1 ∣ (3 + 4 * d) + ((24 * k + 1) - 3) := by
    simpa only [add_comm] using hsum
  have hdiv : 4 * m - 1 ∣ 3 + 4 * d :=
    (Nat.dvd_add_iff_left hminus).mpr hsum'
  exact minus_three_only_m2_d1 m d hm hd hdsq hdiv

/-- Exact integer witnesses for the stress examples outside the `p+2`
subfamily, and for a `7 (mod 8)` factor with no `5 (mod 8)` factor. -/
theorem additional_full_square_witnesses :
    FullSquareAxis 18481 ∧ FullSquareAxis 1321 ∧
      FullSquareAxis 2784961 := by
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨46, 92, by norm_num, by norm_num, by norm_num,
        by norm_num, by norm_num, by norm_num⟩
  · exact ⟨2, 4, by norm_num, by norm_num, by norm_num,
        by norm_num, by norm_num, by norm_num⟩
  · exact ⟨12, 6, by norm_num, by norm_num, by norm_num,
        by norm_num, by norm_num, by norm_num⟩


end Erdos242
