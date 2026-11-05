import Submission.Classification

/-!
# A complementary Type-I factorization for hard Erdős–Straus primes

These identities give **conditional**, strictly ordered solutions.  In particular,
no theorem in this file asserts that an eligible factor exists for every prime.
`Submission/Spec.lean` is not imported or changed.
-/

namespace Erdos242

/-- The product identity `hp+1=4qc`, `q+1=ht` gives a Type-I witness
`x=tc`, and the *explicitly ordered* denominators `tc, qtc, pqc`.
The conditions are equations in natural numbers, not rational divisibility
heuristics. -/
theorem typeI_ordered_of_factor_product (p h q c t : ℕ)
    (hp : 0 < p) (hh : 3 ≤ h) (hq : 1 < q) (hc : 0 < c) (ht : 0 < t)
    (hqt : q + 1 = h * t) (hpc : h * p + 1 = 4 * q * c) :
    TypeI p (t * c) ∧ 1 ≤ t * c ∧ t * c < q * (t * c) ∧
      q * (t * c) < p * q * c ∧
      (4 / p : ℚ) = 1 / (t * c) + 1 / (q * (t * c)) + 1 / (p * q * c) := by
  have hxpos : 0 < t * c := Nat.mul_pos ht hc
  have hsum : h * (4 * (t * c)) = h * p + 4 * c + 1 := by
    calc
      h * (4 * (t * c)) = 4 * c * (h * t) := by ring
      _ = 4 * c * (q + 1) := by rw [← hqt]
      _ = (h * p + 1) + 4 * c := by rw [hpc]; ring
      _ = h * p + 4 * c + 1 := by omega
  have hlo : p < 4 * (t * c) := by
    by_contra hnot
    have hle : 4 * (t * c) ≤ p := by omega
    have hmul := Nat.mul_le_mul_left h hle
    nlinarith [hsum]
  have hcoef : h * (4 * (t * c) - p) = 4 * c + 1 := by
    have hdecomp : (4 * (t * c) - p) + p = 4 * (t * c) :=
      Nat.sub_add_cancel (by omega)
    have hmul := congrArg (fun n : ℕ => h * n) hdecomp
    nlinarith [hsum, hmul]
  have hqc : 2 * c ≤ q * c := Nat.mul_le_mul_right c (by omega : 2 ≤ q)
  have hdiff : 2 * c * (q + 1) + 1 < 4 * q * c := by
    nlinarith [hqc]
  have hhalfsum : h * (2 * (t * c)) = 2 * c * (q + 1) := by
    calc
      h * (2 * (t * c)) = 2 * c * (h * t) := by ring
      _ = 2 * c * (q + 1) := by rw [← hqt]
  have hhalf : 2 * (t * c) < p := by
    apply (Nat.mul_lt_mul_left (by omega : 0 < h)).mp
    nlinarith [hhalfsum, hdiff, hpc]
  have ht_le_x : t ≤ t * c := by
    simpa only [mul_one] using Nat.mul_le_mul_left t (by omega : 1 ≤ c)
  have htp : t < p := by omega
  have hxy : t * c < q * (t * c) := by
    simpa only [one_mul] using Nat.mul_lt_mul_of_pos_right hq hxpos
  have hyz : q * (t * c) < p * q * c := by
    have h := Nat.mul_lt_mul_of_pos_right htp (Nat.mul_pos (by omega : 0 < q) hc)
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h
  have hI : TypeI p (t * c) := by
    refine ⟨c, hc, ?_, ?_⟩
    · refine ⟨t * (t * c), ?_⟩
      ring
    · refine ⟨h, ?_⟩
      simpa only [mul_comm] using hcoef.symm
  have hnum : 4 * q * c * t = p * q + p + t := by
    calc
      4 * q * c * t = (h * p + 1) * t := by rw [hpc]
      _ = p * (h * t) + t := by ring
      _ = p * (q + 1) + t := by rw [← hqt]
      _ = p * q + p + t := by ring
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  have hqq : (q : ℚ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have hcq : (c : ℚ) ≠ 0 := by exact_mod_cast (by omega : c ≠ 0)
  have htq : (t : ℚ) ≠ 0 := by exact_mod_cast (by omega : t ≠ 0)
  have hnumq : 4 * (q : ℚ) * c * t = p * q + p + t := by exact_mod_cast hnum
  refine ⟨hI, by omega, hxy, hyz, ?_⟩
  field_simp
  nlinarith [hnumq]

/-- In particular the two factor equations always produce a `Good` witness,
without any primality assumption. -/
theorem good_of_factor_product (p h q c t : ℕ)
    (hp : 0 < p) (hh : 3 ≤ h) (hq : 1 < q) (hc : 0 < c) (ht : 0 < t)
    (hqt : q + 1 = h * t) (hpc : h * p + 1 = 4 * q * c) :
    TypeI p (t * c) ∧ Good p := by
  obtain ⟨hI, hx, hxy, hyz, heq⟩ :=
    typeI_ordered_of_factor_product p h q c t hp hh hq hc ht hqt hpc
  refine ⟨hI, ⟨t * c, q * (t * c), p * q * c, hx, hxy, hyz, ?_⟩⟩
  simpa only [Nat.cast_mul] using heq

/-- The complementary factorization of `p+t=qs` has `q+1=ht` and
`4c+1=hs`.  Its *cofactor* is the Type-I modulus `4x-p=s`, where `x=tc`.
For even `t` and `p ≡ 1 (mod 4)`, the two latter conditions arise from
factors `q ≡ 3t-1 (mod 4t)`; see `FactorTrisection.md`.
This is a conditional factor test, not a factor-existence theorem. -/
theorem typeI_good_of_shifted_factor (p t q s h c : ℕ)
    (hp : 0 < p) (ht : 0 < t) (hq : 1 < q) (hh : 3 ≤ h) (hc : 0 < c)
    (hfac : p + t = q * s) (hqt : q + 1 = h * t) (hcs : 4 * c + 1 = h * s) :
    4 * (t * c) = p + s ∧ TypeI p (t * c) ∧ Good p := by
  have hshift : 4 * (t * c) + t = p + s + t := by
    calc
      4 * (t * c) + t = t * (4 * c + 1) := by ring
      _ = t * (h * s) := by rw [hcs]
      _ = (h * t) * s := by ring
      _ = (q + 1) * s := by rw [← hqt]
      _ = (p + t) + s := by rw [hfac]; ring
      _ = p + s + t := by ring
  have hpc' : h * p + 1 + q = 4 * q * c + q := by
    calc
      h * p + 1 + q = h * (p + t) := by nlinarith only [hqt]
      _ = h * (q * s) := by rw [hfac]
      _ = q * (h * s) := by ring
      _ = q * (4 * c + 1) := by rw [← hcs]
      _ = 4 * q * c + q := by ring
  have hpc : h * p + 1 = 4 * q * c := by omega
  obtain ⟨hI, hG⟩ := good_of_factor_product p h q c t hp hh hq hc ht hqt hpc
  exact ⟨by omega, hI, hG⟩


/-- A factor `q ≡ 5 (mod 8)` of `p+2` produces a complementary
**Type-I** witness when `p ≡ 1 (mod 8)`.  For instance the prime factor
`29` of `2521+2` works, although `29 ≡ 5 (mod 8)` does not meet the
usual Type-II test `q ≡ 7 (mod 8)`.  This gives no assertion that
all numbers `p+2` have such a factor. -/
theorem typeI_of_pplus_two_factor_five_mod_eight (p q : ℕ)
    (hp8 : p % 8 = 1) (hq8 : q % 8 = 5) (hqdiv : q ∣ p + 2) :
    ∃ x : ℕ, TypeI p x ∧ Good p := by
  let s := (p + 2) / q
  have hfac : p + 2 = q * s := (Nat.mul_div_cancel' hqdiv).symm
  have hsmod : s % 8 = 7 := by
    have hmod : (q % 8 * (s % 8)) % 8 = 3 := by
      rw [← Nat.mul_mod, ← hfac]
      omega
    rw [hq8] at hmod
    omega
  let a := q / 8
  let b := s / 8
  have hqform : q = 8 * a + 5 := by dsimp [a]; omega
  have hsform : s = 8 * b + 7 := by dsimp [b]; omega
  let h := 4 * a + 3
  let c := 8 * a * b + 7 * a + 6 * b + 5
  have hqt : q + 1 = h * 2 := by rw [hqform]; dsimp [h]; ring
  have hcs : 4 * c + 1 = h * s := by rw [hsform]; dsimp [h, c]; ring
  obtain ⟨_, hI, hG⟩ := typeI_good_of_shifted_factor p 2 q s h c
    (by have := Nat.mod_le p 8; omega) (by omega) (by omega) (by dsimp [h]; omega)
    (by dsimp [c]; omega) hfac hqt hcs
  exact ⟨2 * c, hI, hG⟩

/-- An unconditional polynomial identity for **selected** integers,
including some hard primes: writing `r=3u+2`, `q=3v+2`, we have
`3p+1=4rq` and the denominators are `r(v+1)`, `qr(v+1)`, `prq`.
The witness is Type I with `c=r`, `4x-p=4u+3`, and is strictly ordered
also at the edge `u=v=0` (`p=5`). -/
theorem trisection_polynomial (u v : ℕ) :
    let p := 12 * u * v + 8 * u + 8 * v + 5
    let r := 3 * u + 2
    let q := 3 * v + 2
    let x := (v + 1) * r
    TypeI p x ∧ 1 ≤ x ∧ x < q * x ∧ q * x < p * q * r ∧
      (4 / p : ℚ) = 1 / x + 1 / (q * x) + 1 / (p * q * r) := by
  dsimp
  have hqt : (3 * v + 2) + 1 = 3 * (v + 1) := by omega
  have hpc : 3 * (12 * u * v + 8 * u + 8 * v + 5) + 1 =
      4 * (3 * v + 2) * (3 * u + 2) := by ring
  simpa only [Nat.cast_mul] using
    (typeI_ordered_of_factor_product
      (12 * u * v + 8 * u + 8 * v + 5) 3 (3 * v + 2) (3 * u + 2) (v + 1)
      (by omega) (by norm_num) (by omega) (by omega) (by omega) hqt hpc)

/-- The polynomial identity yields an ordered solution (and a Type-I
certificate) with no assumption that its integer `p` is prime. -/
theorem good_trisection_polynomial (u v : ℕ) :
    TypeI (12 * u * v + 8 * u + 8 * v + 5) ((v + 1) * (3 * u + 2)) ∧
      Good (12 * u * v + 8 * u + 8 * v + 5) := by
  obtain ⟨hI, hx, hxy, hyz, heq⟩ := trisection_polynomial u v
  exact ⟨hI, ⟨(v + 1) * (3 * u + 2),
    (3 * v + 2) * ((v + 1) * (3 * u + 2)),
    (12 * u * v + 8 * u + 8 * v + 5) * (3 * v + 2) * (3 * u + 2),
    hx, hxy, hyz, by simpa only [Nat.cast_mul] using heq⟩⟩

/-- For `p=24k+1`, a factor `r ≡ 2 (mod 3)` of `M=18k+1=(3p+1)/4`
produces Type I at the *explicit* first denominator `x=(M+r)/3`.
There is no hypothesis that `r` be prime or the least such factor. -/
theorem hard_good_of_trisected_factor (k r : ℕ)
    (hr : r % 3 = 2) (hrdiv : r ∣ 18 * k + 1) :
    TypeI (24 * k + 1) ((18 * k + 1 + r) / 3) ∧ Good (24 * k + 1) := by
  let q := (18 * k + 1) / r
  have hrpos : 0 < r := by omega
  have hprod : r * q = 18 * k + 1 := Nat.mul_div_cancel' hrdiv
  have hqmod : q % 3 = 2 := by
    have hmod : (r % 3 * (q % 3)) % 3 = 1 := by
      rw [← Nat.mul_mod, hprod]
      omega
    rw [hr] at hmod
    omega
  have hqpos : 1 < q := by
    have hle : q % 3 ≤ q := Nat.mod_le q 3
    omega
  let t := q / 3 + 1
  have hqt : q + 1 = 3 * t := by dsimp [t]; omega
  have hpc : 3 * (24 * k + 1) + 1 = 4 * q * r := by
    calc
      3 * (24 * k + 1) + 1 = 4 * (18 * k + 1) := by ring
      _ = 4 * (r * q) := by rw [hprod]
      _ = 4 * q * r := by ring
  obtain ⟨hI, hG⟩ :=
    good_of_factor_product (24 * k + 1) 3 q r t (by omega)
      (by norm_num) hqpos hrpos (by dsimp [t]; omega) hqt hpc
  have hx : (18 * k + 1 + r) / 3 = t * r := by
    have hnum : 18 * k + 1 + r = 3 * (t * r) := by
      calc
        18 * k + 1 + r = r * q + r := by rw [hprod]
        _ = r * (q + 1) := by ring
        _ = r * (3 * t) := by rw [hqt]
        _ = 3 * (t * r) := by ring
    rw [hnum]
    simp
  rw [hx]
  exact ⟨hI, hG⟩

/-- **Exact scope of this particular polynomial**, not a classification of
all Erdős–Straus solutions: for `p=24k+1`, it applies exactly when
`M=18k+1` has a factor `2 (mod 3)`.  If the factor is composite, it
contains a prime with the same residue, so a prime factor may be used. -/
theorem hard_polynomial_iff_aux_factor (k : ℕ) :
    (∃ u v : ℕ, 24 * k + 1 = 12 * u * v + 8 * u + 8 * v + 5) ↔
      ∃ r : ℕ, r % 3 = 2 ∧ r ∣ 18 * k + 1 := by
  constructor
  · rintro ⟨u, v, heq⟩
    refine ⟨3 * u + 2, by omega, ?_⟩
    refine ⟨3 * v + 2, ?_⟩
    have hmul : 4 * (18 * k + 1) =
        4 * ((3 * u + 2) * (3 * v + 2)) := by
      calc
        4 * (18 * k + 1) = 3 * (24 * k + 1) + 1 := by ring
        _ = 3 * (12 * u * v + 8 * u + 8 * v + 5) + 1 := by rw [heq]
        _ = 4 * ((3 * u + 2) * (3 * v + 2)) := by ring
    omega
  · rintro ⟨r, hr, hrdiv⟩
    let q := (18 * k + 1) / r
    have hprod : r * q = 18 * k + 1 := Nat.mul_div_cancel' hrdiv
    have hqmod : q % 3 = 2 := by
      have hmod : (r % 3 * (q % 3)) % 3 = 1 := by
        rw [← Nat.mul_mod, hprod]
        omega
      rw [hr] at hmod
      omega
    let u := r / 3
    let v := q / 3
    have hrform : r = 3 * u + 2 := by dsimp [u]; omega
    have hqform : q = 3 * v + 2 := by dsimp [v]; omega
    have hmul : 3 * (24 * k + 1) + 1 = 4 * r * q := by
      calc
        3 * (24 * k + 1) + 1 = 4 * (18 * k + 1) := by ring
        _ = 4 * (r * q) := by rw [hprod]
        _ = 4 * r * q := by ring
    rw [hrform, hqform] at hmul
    refine ⟨u, v, ?_⟩
    nlinarith only [hmul]

section
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000

/-- A certificate that the new `h=3` test is *not universal*:
`(3*2521+1)/4=1891=31*61`, with both primes `1 (mod 3)`. -/
theorem no_trisected_factor_2521 (r : ℕ) (hr : r ∣ 1891) : r % 3 ≠ 2 := by
  have hrmem : r ∈ Nat.divisors 1891 := Nat.mem_divisors.mpr ⟨hr, by norm_num⟩
  have hlist : (Nat.divisors 1891 : Finset ℕ) = {1, 31, 61, 1891} := by decide
  rw [hlist] at hrmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hrmem
  rcases hrmem with h | h | h | h <;> simp [h]

theorem not_trisection_polynomial_2521 :
    ¬ ∃ u v : ℕ, 2521 = 12 * u * v + 8 * u + 8 * v + 5 := by
  intro h
  have hpoly : ∃ u v : ℕ, 24 * 105 + 1 = 12 * u * v + 8 * u + 8 * v + 5 := by
    simpa using h
  obtain ⟨r, hrmod, hrdiv⟩ := (hard_polynomial_iff_aux_factor 105).mp hpoly
  have hrdiv' : r ∣ 1891 := by simpa using hrdiv
  exact no_trisected_factor_2521 r hrdiv' hrmod

end

/-- A residual hard prime: the factorization `18*530+1=29*329`
gives `u=9`, `v=109` and a Type-I first denominator `3190`.
This is **not** an all-hard-primes theorem. -/
theorem prime_12721 : Nat.Prime 12721 := by norm_num

/-- Checked factor data: the minimal first denominator and the three
usual `p+1`, `p+4`, `4p+1` odd-factor tests do not themselves supply
a `3 (mod 4)` factor for this hard prime. -/
theorem residual_12721_factor_data :
    (3181 : ℕ).Prime ∧ (4241 : ℕ).Prime ∧ (6361 : ℕ).Prime ∧
      (509 : ℕ).Prime ∧ (10177 : ℕ).Prime ∧
      12721 % 840 = 121 ∧
      12721 + 1 = 2 * 6361 ∧ 12721 + 2 = 3 * 4241 ∧
      12721 + 4 = 5 ^ 2 * 509 ∧ 4 * 12721 + 1 = 5 * 10177 ∧
      (12721 + 3) / 4 = 3181 ∧ (3 * 12721 + 1) / 4 = 7 * 29 * 47 := by
  norm_num


theorem typeI_12721_trisected : TypeI 12721 3190 := by
  have h := (good_trisection_polynomial 9 109).1
  norm_num at h ⊢
  exact h

theorem good_12721_trisected : Good 12721 := by
  have h := (good_trisection_polynomial 9 109).2
  norm_num at h ⊢
  exact h

theorem good_12721_explicit :
    (4 / 12721 : ℚ) = 1 / 3190 + 1 / 1049510 + 1 / 121371061 := by
  norm_num

/-- The `q=29` factor of `2521+2=29*87`, with `h=15`, instead gives
Type I at `x=652`.  The simpler `h=3` trisection test fails for this
prime; other Type-I/II tests remain possible. -/
theorem typeI_2521_shifted : TypeI 2521 652 ∧ Good 2521 := by
  obtain ⟨_, hI, hG⟩ := typeI_good_of_shifted_factor 2521 2 29 87 15 326
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  exact ⟨hI, hG⟩

theorem good_2521_typeI_explicit :
    (4 / 2521 : ℚ) = 1 / 652 + 1 / 18908 + 1 / 23833534 := by
  norm_num

/-- Even when both the `h=3` polynomial and the `p+2` residue test fail,
a larger shift can supply Type I. Here `5569+17=798*7`,
`798+1=47*17`, and `4*82+1=47*7`.  The shift is odd, so the
assumed `4c+1=hs` integrality is checked explicitly. -/
theorem typeI_5569_shifted : TypeI 5569 1394 ∧ Good 5569 := by
  obtain ⟨_, hI, hG⟩ := typeI_good_of_shifted_factor 5569 17 798 7 47 82
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  exact ⟨hI, hG⟩

theorem good_5569_typeI_explicit :
    (4 / 5569 : ℚ) = 1 / 1394 + 1 / 1112412 + 1 / 364413084 := by
  norm_num

/-- The factor tests in the last example are genuinely different from
both `h=3` and the `p+2` residue test. -/
theorem residual_5569_factor_data :
    (5569 : ℕ).Prime ∧ (4177 : ℕ).Prime ∧ (619 : ℕ).Prime ∧
      (3 * 5569 + 1) / 4 = 4177 ∧ 5569 + 2 = 3 ^ 2 * 619 := by
  norm_num



end Erdos242
