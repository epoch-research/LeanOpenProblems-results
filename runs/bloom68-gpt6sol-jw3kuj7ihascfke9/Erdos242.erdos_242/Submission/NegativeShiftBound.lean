import Submission.CoveringGap
import Submission.SmallShiftRigidity

/-!
# Every fixed negative shift gives only bounded Type-II parameters

Even when the modulus `4*m-1` is chosen *after* factoring `p-r`, a full
square-divisor Type-II certificate whose modulus divides `p-r` has
`4*m ≤ r²+2*r`. Combining this elementary bound with the existing
CRT/Dirichlet theorem rules out all finitely many prescribed negative
shifts, simultaneously, for arbitrarily large hard primes. This does
not exclude other Type-II moduli, Type I, or Erdős--Straus solutions.
`Submission.Spec` is not imported or modified.
-/

namespace Erdos242

/-- If `h=4m-1` divides `r+4d` and `d∣m²`, then `m` is bounded solely by
`r`. The dual square divisor `e=m²/d` gives `h∣4re+1`. Its quotient is
`3 (mod 4)`, so `re≥2m`, which bounds the original quotient of `r+4d`
by `r`. The short equation `d=t*m-c` then forces `d∣c²`. -/
theorem negative_shift_parameter_bound (r m d : ℕ)
    (hr : 0 < r) (hm : 0 < m) (hd : 0 < d)
    (hdsq : d ∣ m ^ 2) (hdiv : 4 * m - 1 ∣ r + 4 * d) :
    4 * m ≤ r ^ 2 + 2 * r := by
  let h := 4 * m - 1
  let e := m ^ 2 / d
  let t := (r + 4 * d) / h
  let u := (4 * r * e + 1) / h
  have hh : h + 1 = 4 * m := by dsimp [h]; omega
  have hhpos : 0 < h := by omega
  have hde : d * e = m ^ 2 := Nat.mul_div_cancel' hdsq
  have hdt : h * t = r + 4 * d := Nat.mul_div_cancel' hdiv
  have hediv : h ∣ 4 * r * e + 1 :=
    (typeII_modular_dual r m d hm hdsq).mp hdiv
  have heu : h * u = 4 * r * e + 1 := Nat.mul_div_cancel' hediv
  have huidentity : u + 4 * (r * e) + 1 = 4 * (m * u) := by
    have heq := congrArg (fun v : ℕ => v * u) hh
    nlinarith only [heq, heu]
  have humod : u % 4 = 3 := by
    have hmod : (u + 4 * (r * e) + 1) % 4 = 0 := by
      rw [huidentity]
      omega
    omega
  have huge : 3 ≤ u := by
    have hle := Nat.mod_le u 4
    omega
  have hre : 2 * m ≤ r * e := by
    have hucomp : 3 * h ≤ h * u := by
      simpa only [mul_comm] using Nat.mul_le_mul_left h huge
    rw [heu] at hucomp
    have hquad : 3 * h ≤ 4 * (r * e) + 1 := by
      simpa only [mul_assoc] using hucomp
    omega
  have hdm : 2 * d ≤ r * m := by
    have hprod : (2 * d) * m ≤ (r * m) * m := by
      calc
        (2 * d) * m = d * (2 * m) := by ring
        _ ≤ d * (r * e) := Nat.mul_le_mul_left d hre
        _ = r * (d * e) := by ring
        _ = r * m ^ 2 := by rw [hde]
        _ = (r * m) * m := by ring
    by_contra hn
    have hstrict : (r * m) * m < (2 * d) * m :=
      Nat.mul_lt_mul_of_pos_right (by omega) hm
    omega
  have hrm : r ≤ r * m := by
    simpa only [mul_one] using
      (Nat.mul_le_mul_left r (show 1 ≤ m by omega))
  have hhr : r * h + r = 4 * (r * m) := by
    calc
      r * h + r = r * (h + 1) := by ring
      _ = r * (4 * m) := by rw [hh]
      _ = 4 * (r * m) := by ring
  have ht_le : t ≤ r := by
    have hdt' : t * h = r + 4 * d := by simpa only [mul_comm] using hdt
    have htr : t * h ≤ r * h := by
      have hfour : 4 * d ≤ 2 * (r * m) := by omega
      omega
    by_contra hn
    have hstrict : r * h < t * h :=
      Nat.mul_lt_mul_of_pos_right (by omega) hhpos
    omega
  have htpos : 0 < t := by
    by_contra hn
    have ht0 : t = 0 := Nat.eq_zero_of_not_pos hn
    rw [ht0] at hdt
    simp at hdt
    omega
  have heq4 : (t + r) + 4 * d = 4 * (t * m) := by
    have heq := congrArg (fun v : ℕ => v * t) hh
    nlinarith only [heq, hdt]
  have hmod : (t + r) % 4 = 0 := by
    have hmod' : ((t + r) + 4 * d) % 4 = 0 := by rw [heq4]; omega
    omega
  obtain ⟨c, hc⟩ : 4 ∣ t + r := Nat.dvd_of_mod_eq_zero hmod
  have hc_bound : 2 * c ≤ r := by omega
  have hdceq : d + c = t * m := by nlinarith only [heq4, hc]
  have hcpos : 0 < c := by omega
  have hdc : d ∣ c ^ 2 := by
    have hsq : d ∣ (t * m) ^ 2 := by
      simpa only [mul_pow] using hdsq.mul_left (t ^ 2)
    have hkey : c ^ 2 + d * (2 * c + d) = (d + c) ^ 2 := by ring
    have htotal : d ∣ c ^ 2 + d * (2 * c + d) := by
      rw [hkey, hdceq]
      exact hsq
    exact (Nat.dvd_add_iff_left (dvd_mul_right d _)).mpr htotal
  have hdle : d ≤ c ^ 2 := Nat.le_of_dvd (by positivity) hdc
  have hmle : m ≤ c ^ 2 + c := by
    have hmul : m ≤ t * m := by
      simpa only [one_mul] using Nat.mul_le_mul_right m (show 1 ≤ t by omega)
    omega
  have hcsq : 4 * c ^ 2 ≤ r ^ 2 := by
    have hpow : (2 * c) ^ 2 ≤ r ^ 2 := Nat.pow_le_pow_left hc_bound 2
    nlinarith only [hpow]
  nlinarith only [hmle, hcsq, hc_bound]

/-- A Type-II modulus dividing a negative shift `p-r` cannot have an
unbounded parameter for fixed `r`, even if it was selected as a divisor
of `p-r` depending on `p`. No primality or size hypothesis is needed
apart from `r≤p` to interpret subtraction on naturals. -/
theorem negative_shift_typeII_bound (p r m d : ℕ) (hr : 0 < r)
    (hrp : r ≤ p) (hm : 0 < m) (hd : 0 < d) (hdsq : d ∣ m ^ 2)
    (hshift : 4 * m - 1 ∣ p - r)
    (hcert : 4 * m - 1 ∣ p + 4 * d) :
    4 * m ≤ r ^ 2 + 2 * r := by
  have heq : (p - r) + (r + 4 * d) = p + 4 * d := by omega
  have hboth : 4 * m - 1 ∣ (p - r) + (r + 4 * d) := by
    rw [heq]
    exact hcert
  have hdiv : 4 * m - 1 ∣ r + 4 * d :=
    (Nat.dvd_add_iff_right hshift).mpr hboth
  exact negative_shift_parameter_bound r m d hr hm hd hdsq hdiv

/-- For every finite list of negative shifts `p-1,...,p-R`, some
arbitrarily large primes `p≡1 (mod 840)` have **no** Type-II witness
whose modulus divides a member of the list, even when the modulus is
allowed to vary with `p`. Other Type-II witnesses and Type I are not
excluded. This is obtained from the CRT/Dirichlet fixed-parameter
obstruction *after* the universal `m` bound has been proved. -/
theorem hard_primes_escape_finite_negative_shifts (R N : ℕ) :
    ∃ p : ℕ, N < p ∧ p.Prime ∧ p % 840 = 1 ∧
      ∀ r m d : ℕ, 0 < r → r ≤ R → 0 < m → 0 < d → d ∣ m ^ 2 →
        ¬ (4 * m - 1 ∣ p - r ∧ 4 * m - 1 ∣ p + 4 * d) := by
  obtain ⟨p, hpmax, hp, hp840, hno⟩ :=
    hard_primes_escape_bounded_modular_parameters (R ^ 2 + 2 * R) (max N R)
  refine ⟨p, by omega, hp, hp840, ?_⟩
  intro r m d hr hrR hm hd hdsq ⟨hshift, hcert⟩
  have hrp : r ≤ p := by omega
  have hbound :=
    negative_shift_typeII_bound p r m d hr hrp hm hd hdsq hshift hcert
  have hmB : m ≤ R ^ 2 + 2 * R := by
    have hpow : r ^ 2 ≤ R ^ 2 := Nat.pow_le_pow_left hrR 2
    omega
  exact hno m d hm hmB hd hdsq hcert

/-- A small hard prime refuting the *specific* `p+2`-factor strategy,
not the full Type-II axis: `97+2=99=3²·11` has no divisor `7 (mod 8)`,
but `7 ∣ 97+4·2` gives a full certificate at `m=2,d=2`. -/
theorem prime_97_full_typeII_but_no_plus_two_factor :
    (97 : ℕ).Prime ∧ FullSquareAxis 97 ∧
      ¬ (∃ m d : ℕ, 0 < m ∧ 0 < d ∧ d ∣ m ^ 2 ∧
        4 * d < 97 ∧ 4 * m - 1 ∣ 97 + 2 ∧
        4 * m - 1 ∣ 97 + 4 * d) := by
  have hno : ¬ ∃ h : ℕ, h % 8 = 7 ∧ h ∣ 97 + 2 := by
    rintro ⟨h, hh, hdiv⟩
    have hmem : h ∈ Nat.divisors 99 :=
      (Nat.mem_divisors).mpr ⟨by simpa only [Nat.reduceAdd] using hdiv, by norm_num⟩
    have hbad : ∀ t ∈ Nat.divisors 99, t % 8 ≠ 7 := by decide
    exact hbad h hmem hh
  have hw : FullSquareAxis 97 := by
    refine ⟨2, 2, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num
  refine ⟨by norm_num, hw, ?_⟩
  intro hpair
  have hpair' := (plus_two_shift_exact 4).mp
    (by simpa only [Nat.reduceMul, Nat.reduceAdd] using hpair)
  exact hno (by simpa only [Nat.reduceMul, Nat.reduceAdd] using hpair')


end Erdos242

#print axioms Erdos242.negative_shift_parameter_bound
#print axioms Erdos242.hard_primes_escape_finite_negative_shifts
