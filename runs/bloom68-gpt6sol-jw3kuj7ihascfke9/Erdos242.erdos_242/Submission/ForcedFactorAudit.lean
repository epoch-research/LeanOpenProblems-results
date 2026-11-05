import Submission.PointwiseJacobi
import Submission.HardTypeIISize

/-!
# Forced-factor diagnostics for hard Erdős–Straus primes

The factors of `p-1` cannot by themselves build a working first denominator:
each is a quadratic residue modulo a hard prime `p=24k+1`. A prime factor
`3 (mod 4)` of `p+1` does give an ordered Type-II solution, but such a factor
need not exist. The resulting dichotomy and a sharpened exact cover are
conditional/negative statements, **not** a proof of the conjecture.

This file does not import or modify `Submission.Spec`.
-/

namespace Erdos242

private theorem hard_two_jacobi_one (k : ℕ) :
    jacobiSym (2 : ℤ) (24 * k + 1) = 1 := by
  have hodd : Odd (24 * k + 1) := Nat.odd_iff.mpr (by omega)
  rw [jacobiSym.at_two hodd, ZMod.χ₈_nat_eq_if_mod_eight]
  have h2 : (24 * k + 1) % 2 = 1 := by omega
  have h8 : (24 * k + 1) % 8 = 1 := by omega
  simp [h2, h8]

/-- Every prime factor of `p-1` is a quadratic residue modulo `p=24k+1`.
Primality of `p` itself is not needed for this Jacobi identity. -/
theorem hard_minus_one_prime_factor_residue (k ell : ℕ) (hell : ell.Prime)
    (hdiv : ell ∣ 24 * k) : jacobiSym (ell : ℤ) (24 * k + 1) = 1 := by
  rcases hell.eq_two_or_odd' with htwo | hodd
  · subst ell
    exact hard_two_jacobi_one k
  · have hrec : jacobiSym (ell : ℤ) (24 * k + 1) =
        jacobiSym ((24 * k + 1 : ℕ) : ℤ) ell :=
      (jacobiSym.quadratic_reciprocity_one_mod_four
        (by omega : (24 * k + 1) % 4 = 1) hodd).symm
    obtain ⟨t, ht⟩ := hdiv
    have heq : ((24 * k + 1 : ℕ) : ℤ) = (ell : ℤ) * t + 1 := by
      exact_mod_cast (show 24 * k + 1 = ell * t + 1 by omega)
    have hmod : ((24 * k + 1 : ℕ) : ℤ) % ell = (1 : ℤ) % ell := by
      rw [heq]
      simp [Int.add_emod]
    rw [hrec, jacobiSym.mod_left' hmod]
    simp

/-- No first denominator built entirely from prime factors of `p-1` can
satisfy *either full divisor criterion*. The exponent is arbitrary and the
range restrictions only say that `x` is an ordered candidate. -/
theorem hard_minus_one_supported_no_types (k x e : ℕ)
    (hpp : (24 * k + 1).Prime)
    (hlo : 24 * k + 1 < 4 * x) (hhi : x < 24 * k + 1)
    (hxdvd : x ∣ (24 * k) ^ e) :
    ¬TypeI (24 * k + 1) x ∧ ¬TypeII (24 * k + 1) x := by
  apply no_types_if_prime_factors_residue (24 * k + 1) x hpp (by omega) hlo hhi
  intro ell hell helld
  exact hard_minus_one_prime_factor_residue k ell hell
    (hell.dvd_of_dvd_pow (dvd_trans helld hxdvd))

/-- The *last* eligible first denominator, `x=(p-1)/2=12k`, always fails
both branches, even though `p-2=4x-p` is `3 (mod 4)` and thus has a
prime factor in that class. This rules out one fiber, not the prime. -/
theorem hard_last_candidate_no_types (k : ℕ) (hpp : (24 * k + 1).Prime) :
    ¬TypeI (24 * k + 1) (12 * k) ∧ ¬TypeII (24 * k + 1) (12 * k) := by
  have hk : 0 < k := by
    have := hpp.two_le
    omega
  apply hard_minus_one_supported_no_types k (12 * k) 1 hpp (by omega) (by omega)
  simp only [pow_one]
  exact ⟨2, by ring⟩

/-- A *genuine* factor-class guarantee from the shift `p-2`: when
`p=24k+1>1`, `p-2≡3 (mod 4)` has a prime factor `3 (mod 4)`.
Its congruence alone does not satisfy either Type-I or Type-II divisibility. -/
theorem hard_minus_two_has_three_mod_four_factor (k : ℕ) (hk : 0 < k) :
    ∃ q : ℕ, q.Prime ∧ q ∣ (24 * k + 1) - 2 ∧ q % 4 = 3 := by
  have hn4 : ((24 * k + 1) - 2) % 4 = 3 := by omega
  have hnodd : Odd ((24 * k + 1) - 2) := Nat.odd_iff.mpr (by omega)
  have hneg : jacobiSym (-1) ((24 * k + 1) - 2) = -1 := by
    rw [jacobiSym.at_neg_one hnodd, ZMod.χ₄_nat_three_mod_four hn4]
  obtain ⟨q, hq, hqd, hJ⟩ :=
    jacobiSym.eq_neg_one_at_prime_divisor_of_eq_neg_one hneg
  have hqodd : Odd q := by
    rcases hq.eq_two_or_odd' with htwo | hodd
    · subst q
      have hzero := Nat.mod_eq_zero_of_dvd hqd
      omega
    · exact hodd
  have hq4 : q % 4 = 3 := by
    rw [jacobiSym.at_neg_one hqodd] at hJ
    rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hqodd) with h1 | h3
    · rw [ZMod.χ₄_nat_one_mod_four h1] at hJ
      norm_num at hJ
    · exact h3
  exact ⟨q, hq, hqd, hq4⟩

/-- A `3 (mod 4)` divisor `q` of `p-2` gives an *eligible candidate*
`x=(p+q)/4`, with exact modulus `a=q`. This proves integrality and
range, not the missing Type-I/II square-divisor congruence. -/
theorem hard_minus_two_factor_gives_candidate (k q : ℕ) (hk : 0 < k)
    (hq4 : q % 4 = 3) (hdiv : q ∣ (24 * k + 1) - 2) :
    ∃ x : ℕ, 24 * k + 1 < 4 * x ∧ 2 * x < 24 * k + 1 ∧
      4 * x - (24 * k + 1) = q := by
  have hle : q ≤ (24 * k + 1) - 2 :=
    Nat.le_of_dvd (by omega) hdiv
  have h4 : (24 * k + 1 + q) % 4 = 0 := by omega
  have hfour : 4 ∣ 24 * k + 1 + q := Nat.dvd_of_mod_eq_zero h4
  let x := (24 * k + 1 + q) / 4
  have hx4 : 4 * x = 24 * k + 1 + q := Nat.mul_div_cancel' hfour
  exact ⟨x, by omega, by omega, by omega⟩

/-- For *every* `p=24k+1>1` there is such a prime factor and a first
denominator in the ordered range. The two exact divisor conditions are
not supplied; at `p=193` the only forced factor's candidate fails both. -/
theorem hard_minus_two_forced_prime_candidate (k : ℕ) (hk : 0 < k) :
    ∃ q x : ℕ, q.Prime ∧ q % 4 = 3 ∧ q ∣ (24 * k + 1) - 2 ∧
      24 * k + 1 < 4 * x ∧ 2 * x < 24 * k + 1 ∧
      4 * x - (24 * k + 1) = q := by
  obtain ⟨q, hq, hdiv, hmod⟩ := hard_minus_two_has_three_mod_four_factor k hk
  obtain ⟨x, hlo, hhi, ha⟩ := hard_minus_two_factor_gives_candidate k q hk hmod hdiv
  exact ⟨q, x, hq, hmod, hdiv, hlo, hhi, ha⟩

/-- Directly for every prescribed prime `p≡1 (mod 24)`: a guaranteed
`3 (mod 4)` *prime factor* of `p-2` gives a valid candidate modulus
`a=q` and first denominator `x`. This theorem does **not** assert
`TypeI p x`, `TypeII p x`, or `Good p`. -/
theorem hard_prime_forced_minus_two_candidate (p : ℕ)
    (hpp : p.Prime) (hmod : p % 24 = 1) :
    ∃ q x : ℕ, q.Prime ∧ q % 4 = 3 ∧ q ∣ p - 2 ∧
      p < 4 * x ∧ 2 * x < p ∧ 4 * x - p = q := by
  have heq : p = 24 * (p / 24) + 1 := by omega
  have hk : 0 < p / 24 := by
    have := hpp.two_le
    omega
  simpa only [← heq] using hard_minus_two_forced_prime_candidate (p / 24) hk

/-- An odd factor of `p+1` has character `(-1/ell)` modulo `p=24k+1`.
The odd prime factors `3 (mod 4)` are therefore nonresidues; the factors
`1 (mod 4)` are residues. -/
theorem hard_plus_one_odd_factor_character (k ell : ℕ) (hodd : Odd ell)
    (hdiv : ell ∣ 24 * k + 2) :
    jacobiSym (ell : ℤ) (24 * k + 1) = jacobiSym (-1) ell := by
  have hrec : jacobiSym (ell : ℤ) (24 * k + 1) =
      jacobiSym ((24 * k + 1 : ℕ) : ℤ) ell :=
    (jacobiSym.quadratic_reciprocity_one_mod_four
      (by omega : (24 * k + 1) % 4 = 1) hodd).symm
  obtain ⟨t, ht⟩ := hdiv
  have heq : ((24 * k + 1 : ℕ) : ℤ) + 1 = (ell : ℤ) * t := by
    exact_mod_cast ht
  have hmod : ((24 * k + 1 : ℕ) : ℤ) % ell = (-1 : ℤ) % ell := by
    calc
      ((24 * k + 1 : ℕ) : ℤ) % ell =
          (((24 * k + 1 : ℕ) : ℤ) + 1 - 1) % ell := by simp
      _ = ((ell : ℤ) * t - 1) % ell := by rw [heq]
      _ = ((ell : ℤ) * t + (-1 : ℤ)) % ell := by simp only [sub_eq_add_neg]
      _ = (-1 : ℤ) % ell := by simp [Int.add_emod]
  exact hrec.trans (jacobiSym.mod_left' hmod)

/-- If an odd prime factor of `p+1` is `1 (mod 4)`, it is a residue. -/
theorem hard_plus_one_prime_one_mod_four_residue (k ell : ℕ)
    (_hell : ell.Prime) (hmod4 : ell % 4 = 1) (hdiv : ell ∣ 24 * k + 2) :
    jacobiSym (ell : ℤ) (24 * k + 1) = 1 := by
  have hodd : Odd ell := Nat.odd_iff.mpr (by omega)
  rw [hard_plus_one_odd_factor_character k ell hodd hdiv,
    jacobiSym.at_neg_one hodd, ZMod.χ₄_nat_one_mod_four hmod4]

/-- The actual denominators behind the `p+1` construction. Keeping the
factor product explicit avoids hiding integrality in a generic `Good` proof. -/
theorem plus_one_product_ordered_triple (p m t : ℕ)
    (hp : 0 < p) (hm : 0 < m) (ht : 1 < t)
    (hproduct : p + 1 = (4 * m - 1) * t) :
    1 ≤ m * t ∧ m * t < p * m ∧ p * m < p * m * t ∧
      (4 / p : ℚ) = 1 / (m * t) + 1 / (p * m) + 1 / (p * m * t) := by
  have hq : (4 * m - 1) + 1 = 4 * m := by omega
  have hqge : 3 ≤ 4 * m - 1 := by omega
  have hthree : 3 * t ≤ (4 * m - 1) * t := Nat.mul_le_mul_right t hqge
  have htltp : t < p := by omega
  have hxy : m * t < p * m := by
    simpa only [mul_comm p m] using Nat.mul_lt_mul_of_pos_left htltp hm
  have hpm : 0 < p * m := Nat.mul_pos hp hm
  have hyz : p * m < p * m * t := by
    have h := Nat.mul_lt_mul_of_pos_left ht hpm
    simpa only [mul_one] using h
  have hpoly : 4 * m * t = p + t + 1 := by
    nlinarith only [hproduct, congrArg (fun n : ℕ => n * t) hq]
  have hpolyQ : (4 : ℚ) * m * t = p + t + 1 := by exact_mod_cast hpoly
  have hxpos : 0 < m * t := Nat.mul_pos hm (by omega)
  refine ⟨by omega, hxy, hyz, ?_⟩
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  have hmq : (m : ℚ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have htq : (t : ℚ) ≠ 0 := by exact_mod_cast (by omega : t ≠ 0)
  field_simp
  nlinarith only [hpolyQ]

/-- The same product gives an actual Type-II certificate at `x=mt`,
with `d=m` and `a=4x-p=t+1`. It does not require `p` prime. -/
theorem plus_one_product_typeII (p m t : ℕ)
    (hm : 0 < m) (ht : 1 < t) (hproduct : p + 1 = (4 * m - 1) * t) :
    TypeII p (m * t) := by
  have hq : (4 * m - 1) + 1 = 4 * m := by omega
  have hpoly : 4 * m * t = p + t + 1 := by
    nlinarith only [hproduct, congrArg (fun n : ℕ => n * t) hq]
  have ha : 4 * (m * t) - p = t + 1 := by
    have hprod : 4 * (m * t) = p + (t + 1) := by nlinarith only [hpoly]
    rw [hprod]
    omega
  refine ⟨m, hm, ?_, ?_, ?_⟩
  · have hlt := Nat.mul_lt_mul_of_pos_left ht hm
    simpa only [mul_one] using hlt
  · refine ⟨m * t ^ 2, ?_⟩
    ring
  · rw [ha]
    refine ⟨m, ?_⟩
    ring

/-- A divisor `q≡3 (mod 4)` of `p+1` gives a *strictly ordered* Type-II
construction, even if `q` is composite. Write `q=4m-1`, `p+1=qt`; then
`(x,y,z)=(mt,pm,pmt)`. The factor hypothesis is not universal. -/
theorem good_of_plus_one_three_mod_four (p q : ℕ)
    (hp4 : p % 4 = 1) (hq4 : q % 4 = 3) (hdiv : q ∣ p + 1) : Good p := by
  let m := (q + 1) / 4
  have hq : 4 * m - 1 = q := by dsimp [m]; omega
  have hm : 0 < m := by dsimp [m]; omega
  obtain ⟨t, ht⟩ := hdiv
  have htpos : 0 < t := by
    by_contra hn
    have hzero : t = 0 := by omega
    simp [hzero] at ht
  have htge : 2 ≤ t := by
    by_contra hn
    have hone : t = 1 := by omega
    rw [hone] at ht
    have heq : p + 1 = q := by simpa using ht
    omega
  have hproduct : p + 1 = (4 * m - 1) * t := by rw [hq]; exact ht
  obtain ⟨hx, hxy, hyz, heq⟩ :=
    plus_one_product_ordered_triple p m t (by omega) hm (by omega) hproduct
  refine ⟨m * t, p * m, p * m * t, hx, hxy, hyz, ?_⟩
  simpa only [Nat.cast_mul] using heq

/-- If `p+1` has no `3 (mod 4)` prime factor, *every* prime factor of
`p²-1=(p-1)(p+1)` is a quadratic residue modulo `p`. Thus no eligible
first denominator supported on these factors can satisfy either full
divisor condition. The hypothesis holds for soluble primes such as `193`. -/
theorem hard_square_minus_one_supported_no_types (k x e : ℕ)
    (hpp : (24 * k + 1).Prime)
    (hfactor : ¬∃ ell : ℕ, ell.Prime ∧ ell % 4 = 3 ∧ ell ∣ 24 * k + 2)
    (hlo : 24 * k + 1 < 4 * x) (hhi : x < 24 * k + 1)
    (hxdvd : x ∣ ((24 * k + 1) ^ 2 - 1) ^ e) :
    ¬TypeI (24 * k + 1) x ∧ ¬TypeII (24 * k + 1) x := by
  apply no_types_if_prime_factors_residue (24 * k + 1) x hpp (by omega) hlo hhi
  intro ell hell helld
  have hsquare : (24 * k + 1) ^ 2 - 1 = (24 * k) * (24 * k + 2) := by
    have heq : (24 * k + 1) ^ 2 = (24 * k) * (24 * k + 2) + 1 := by ring
    rw [heq, Nat.add_sub_cancel]
  have hbase : ell ∣ (24 * k) * (24 * k + 2) := by
    apply hell.dvd_of_dvd_pow (n := e)
    rw [← hsquare]
    exact dvd_trans helld hxdvd
  rcases (hell.dvd_mul).mp hbase with hminus | hplus
  · exact hard_minus_one_prime_factor_residue k ell hell hminus
  · rcases hell.eq_two_or_odd' with htwo | hodd
    · subst ell
      exact hard_two_jacobi_one k
    · rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hodd) with h1 | h3
      · exact hard_plus_one_prime_one_mod_four_residue k ell hell h1 hplus
      · exact False.elim (hfactor ⟨ell, hell, h3, hplus⟩)

/-- Either `p+1` supplies a `3 (mod 4)` prime factor and an ordered
solution, **or** every eligible candidate supported by the factors of
`p²-1` misses both full divisor targets. The second case is possible
(e.g. `p=193`); it is not a counterexample to the conjecture. -/
theorem hard_plus_one_solution_or_square_minus_one_barrier (k : ℕ)
    (hpp : (24 * k + 1).Prime) :
    Good (24 * k + 1) ∨
      ∀ x e : ℕ, 24 * k + 1 < 4 * x → x < 24 * k + 1 →
        x ∣ ((24 * k + 1) ^ 2 - 1) ^ e →
          ¬TypeI (24 * k + 1) x ∧ ¬TypeII (24 * k + 1) x := by
  by_cases hfactor : ∃ ell : ℕ, ell.Prime ∧ ell % 4 = 3 ∧ ell ∣ 24 * k + 2
  · obtain ⟨ell, _, hmod, hdiv⟩ := hfactor
    exact Or.inl (good_of_plus_one_three_mod_four (24 * k + 1) ell
      (by omega) hmod hdiv)
  · exact Or.inr (fun x e hlo hhi hxdvd =>
      hard_square_minus_one_supported_no_types k x e hpp hfactor hlo hhi hxdvd)
/-- The second (`p²-1` barrier) branch is real: `193+1=2·97`, with
both prime factors quadratic residues modulo `193`. The prime `193`
is nevertheless soluble at a first denominator containing another factor. -/
theorem no_plus_one_three_mod_four_prime_193 :
    ¬∃ q : ℕ, q.Prime ∧ q % 4 = 3 ∧ q ∣ 193 + 1 := by
  rintro ⟨q, hq, hmod, hdiv⟩
  have hfactor : q ∣ 2 * 97 := by simpa only [show 193 + 1 = 2 * 97 by norm_num] using hdiv
  rcases (hq.dvd_mul).mp hfactor with h2 | h97
  · have hqeq : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h2
    omega
  · have hqeq : q = 97 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h97
    omega

theorem hard_193_square_minus_one_supported_no_types (x e : ℕ)
    (hlo : 193 < 4 * x) (hhi : x < 193)
    (hxdvd : x ∣ (193 ^ 2 - 1) ^ e) :
    ¬TypeI 193 x ∧ ¬TypeII 193 x := by
  exact hard_square_minus_one_supported_no_types 8 x e (by norm_num)
    (by simpa only [show 24 * 8 + 2 = 193 + 1 by norm_num] using
      no_plus_one_three_mod_four_prime_193) hlo hhi (by simpa using hxdvd)

/-- The forced prime factor of `p-2` need not certify its own fiber:
`193-2=191` is prime `3 (mod 4)`, but `x=(193+191)/4=96`
fails *both* types. `193` works elsewhere. -/
theorem forced_pminus_two_193_endpoint_fails :
    Nat.Prime (193 - 2) ∧ (193 - 2) % 4 = 3 ∧
      ¬TypeI 193 96 ∧ ¬TypeII 193 96 ∧ Good 193 := by
  have hlast := hard_last_candidate_no_types 8 (by norm_num)
  exact ⟨by norm_num, by norm_num, by simpa using hlast.1,
    by simpa using hlast.2, test_193_good⟩



/-- A genuinely forced factor class: for every odd `p≥3`, `p²-2` has
a prime factor `7 (mod 8)`. The proof uses `p²-2≡7 (mod 8)` to
extract a `3 (mod 4)` prime factor; a `3 (mod 8)` factor would make
`2` a quadratic nonresidue while `p²≡2` modulo that factor.
This prime factor is NOT guaranteed to be less than `p`. -/
theorem square_minus_two_has_seven_mod_eight_factor (p : ℕ)
    (hpodd : Odd p) (hpge : 3 ≤ p) :
    ∃ q : ℕ, q.Prime ∧ q ∣ p ^ 2 - 2 ∧ q % 8 = 7 := by
  have hpmod : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by
    have h2 := Nat.odd_iff.mp hpodd
    omega
  have hp8 : p ^ 2 % 8 = 1 := by
    have heq := Nat.pow_mod p 2 8
    rcases hpmod with h | h | h | h <;> simp [heq, h]
  have hge2 : 2 ≤ p ^ 2 := by nlinarith
  have hsub : (p ^ 2 - 2) + 2 = p ^ 2 := Nat.sub_add_cancel hge2
  have hn8 : (p ^ 2 - 2) % 8 = 7 := by omega
  have hn4 : (p ^ 2 - 2) % 4 = 3 := by omega
  have hnodd : Odd (p ^ 2 - 2) := Nat.odd_iff.mpr (by omega)
  have hneg : jacobiSym (-1) (p ^ 2 - 2) = -1 := by
    rw [jacobiSym.at_neg_one hnodd, ZMod.χ₄_nat_three_mod_four hn4]
  obtain ⟨q, hq, hqd, hJ⟩ :=
    jacobiSym.eq_neg_one_at_prime_divisor_of_eq_neg_one hneg
  have hqodd : Odd q := by
    rcases hq.eq_two_or_odd' with htwo | hodd
    · subst q
      have hmodzero := Nat.mod_eq_zero_of_dvd hqd
      omega
    · exact hodd
  have hq4 : q % 4 = 3 := by
    rw [jacobiSym.at_neg_one hqodd] at hJ
    rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hqodd) with h1 | h3
    · rw [ZMod.χ₄_nat_one_mod_four h1] at hJ
      norm_num at hJ
    · exact h3
  have hq8 : q % 8 = 3 ∨ q % 8 = 7 := by omega
  rcases hq8 with hq3 | hq7
  · have hJ2 : jacobiSym (2 : ℤ) q = -1 := by
      rw [jacobiSym.at_two hqodd, ZMod.χ₈_nat_eq_if_mod_eight]
      have h2 : q % 2 = 1 := Nat.odd_iff.mp hqodd
      simp [h2, hq3]
    haveI : Fact q.Prime := ⟨hq⟩
    obtain ⟨t, ht⟩ := hqd
    have heqZ : (p : ℤ) ^ 2 = (q : ℤ) * t + 2 := by
      exact_mod_cast (show p ^ 2 = q * t + 2 by omega)
    have hdivZ : (q : ℤ) ∣ (p : ℤ) ^ 2 - 2 * (1 : ℤ) ^ 2 := by
      refine ⟨t, ?_⟩
      nlinarith [heqZ]
    have hqoneZ : (q : ℤ) ∣ (1 : ℤ) :=
      (jacobiSym.prime_dvd_of_eq_neg_one hJ2 hdivZ).2
    have hqone : q ∣ 1 := by exact_mod_cast hqoneZ
    have hqeq : q = 1 := Nat.dvd_one.mp hqone
    have := hq.two_le
    omega
  · exact ⟨q, hq, hqd, hq7⟩

/-- Another genuinely forced class: for every odd `p`, `p²+4` has a
prime factor `5 (mod 8)`. It is `1 (mod 4)`, so cannot directly be the
modulus `a=4x-p≡3 (mod 4)` of a hard-prime certificate. -/
theorem square_plus_four_has_five_mod_eight_factor (p : ℕ) (hpodd : Odd p) :
    ∃ q : ℕ, q.Prime ∧ q ∣ p ^ 2 + 4 ∧ q % 8 = 5 := by
  have hpmod : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by
    have h2 := Nat.odd_iff.mp hpodd
    omega
  have hp8 : p ^ 2 % 8 = 1 := by
    have heq := Nat.pow_mod p 2 8
    rcases hpmod with h | h | h | h <;> simp [heq, h]
  have hn8 : (p ^ 2 + 4) % 8 = 5 := by omega
  have hnodd : Odd (p ^ 2 + 4) := Nat.odd_iff.mpr (by omega)
  have hneg : jacobiSym (2 : ℤ) (p ^ 2 + 4) = -1 := by
    rw [jacobiSym.at_two hnodd, ZMod.χ₈_nat_eq_if_mod_eight]
    have h2 : (p ^ 2 + 4) % 2 = 1 := Nat.odd_iff.mp hnodd
    simp [h2, hn8]
  obtain ⟨q, hq, hqd, hJ⟩ :=
    jacobiSym.eq_neg_one_at_prime_divisor_of_eq_neg_one hneg
  have hqodd : Odd q := by
    rcases hq.eq_two_or_odd' with htwo | hodd
    · subst q
      have hmodzero := Nat.mod_eq_zero_of_dvd hqd
      omega
    · exact hodd
  have hq8 : q % 8 = 3 ∨ q % 8 = 5 := by
    rw [jacobiSym.at_two hqodd, ZMod.χ₈_nat_eq_if_mod_eight] at hJ
    have h2 : q % 2 = 1 := Nat.odd_iff.mp hqodd
    by_cases h17 : q % 8 = 1 ∨ q % 8 = 7
    · simp [h2, h17] at hJ
    · omega
  rcases hq8 with hq3 | hq5
  · have hq4 : q % 4 = 3 := by omega
    have hJneg : jacobiSym (-1) q = -1 := by
      rw [jacobiSym.at_neg_one hqodd, ZMod.χ₄_nat_three_mod_four hq4]
    haveI : Fact q.Prime := ⟨hq⟩
    obtain ⟨t, ht⟩ := hqd
    have heqZ : (p : ℤ) ^ 2 + 4 = (q : ℤ) * t := by exact_mod_cast ht
    have hdivZ : (q : ℤ) ∣ (p : ℤ) ^ 2 - (-1 : ℤ) * (2 : ℤ) ^ 2 := by
      refine ⟨t, ?_⟩
      nlinarith [heqZ]
    have hqd2Z : (q : ℤ) ∣ (2 : ℤ) :=
      (jacobiSym.prime_dvd_of_eq_neg_one hJneg hdivZ).2
    have hqd2 : q ∣ 2 := by exact_mod_cast hqd2Z
    have hqeq : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp hqd2
    omega
  · exact ⟨q, hq, hqd, hq5⟩

/-- The forced `7 (mod 8)` factor of `313²-2` can itself be prime and
larger than `p`; likewise `313²+4` is a prime `5 (mod 8)` larger than
`p`. Neither can be the eligible modulus `a<p`. These facts do not
exclude the existing solution at `p=313`. -/
theorem square_shift_313_factor_data :
    Nat.Prime 313 ∧ Nat.Prime (313 ^ 2 - 2) ∧ Nat.Prime (313 ^ 2 + 4) ∧
      313 ^ 2 - 2 > 313 ∧ (313 ^ 2 - 2) % 8 = 7 ∧
      313 ^ 2 + 4 > 313 ∧ (313 ^ 2 + 4) % 8 = 5 := by
  norm_num

/-- Even a *small* forced factor need not hit either target: `23` is
`7 (mod 8)` and divides `97²-2`, but using it as `a=4x-p` forces
`x=30`, where neither full criterion holds. The prime `97` works at
other first denominators, e.g. `good_97_far_typeI`. -/
theorem square_minus_two_97_small_factor_fiber_fails :
    Nat.Prime 97 ∧ Nat.Prime 23 ∧ 23 ∣ 97 ^ 2 - 2 ∧
      23 % 8 = 7 ∧ ¬TypeI 97 30 ∧ ¬TypeII 97 30 ∧ Good 97 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, ?_, ?_,
    good_97_far_typeI⟩
  · rintro ⟨c, hc, hcdvd, hadiv⟩
    have hc900 : c ∣ 900 := by simpa only [show (30 : ℕ) ^ 2 = 900 by norm_num] using hcdvd
    have hcmax : c ≤ 900 := Nat.le_of_dvd (by norm_num) hc900
    have h23 : 23 ∣ 4 * c + 1 := by
      simpa only [show 4 * (30 : ℕ) - 97 = 23 by norm_num] using hadiv
    have hres : c % 23 = 17 := by
      have hzero := Nat.mod_eq_zero_of_dvd h23
      omega
    have hcform : c = 17 + 23 * (c / 23) := by omega
    have hcindex : c / 23 < 39 := by omega
    have hnone : ∀ v : Fin 39, ¬ (17 + 23 * v.val ∣ 900) := by decide
    exact (hnone ⟨c / 23, hcindex⟩) (by simpa only [← hcform] using hc900)
  · rintro ⟨d, hd, hdx, hdsq, hadiv⟩
    have h23 : 23 ∣ 30 + d := by
      simpa only [show 4 * (30 : ℕ) - 97 = 23 by norm_num] using hadiv
    have hd16 : d = 16 := by
      have hzero := Nat.mod_eq_zero_of_dvd h23
      omega
    have hnot : ¬ (16 : ℕ) ∣ 30 ^ 2 := by norm_num
    exact hnot (by simpa only [hd16] using hdsq)

/-- The rightmost `j=6k-1` cannot carry Type I; the previously proved
sharp Type-II bound restricts that branch to `7j<6k`. Both remaining
existentials are still unproved for an arbitrary hard prime. -/
theorem good_iff_hard_omit_forced_endpoint (k : ℕ) (hpp : (24 * k + 1).Prime) :
    Good (24 * k + 1) ↔
      (∃ j : ℕ, j + 1 < 6 * k ∧ TypeI (24 * k + 1) (6 * k + 1 + j)) ∨
      (∃ j : ℕ, 7 * j < 6 * k ∧ TypeII (24 * k + 1) (6 * k + 1 + j)) := by
  rw [good_iff_hard_sharp_typeII k hpp]
  constructor
  · rintro (⟨j, hj, hI⟩ | ⟨j, hj, hII⟩)
    · by_cases hlast : j + 1 = 6 * k
      · have hx : 6 * k + 1 + j = 12 * k := by omega
        exact False.elim ((hard_last_candidate_no_types k hpp).1 (by simpa [hx] using hI))
      · exact Or.inl ⟨j, by omega, hI⟩
    · exact Or.inr ⟨j, hj, hII⟩
  · rintro (⟨j, hj, hI⟩ | ⟨j, hj, hII⟩)
    · exact Or.inl ⟨j, by omega, hI⟩
    · exact Or.inr ⟨j, hj, hII⟩

/-- Exact outstanding *universal* covering condition, with both divisor
alternatives explicit. Its right-hand side is not proved here. The
Type-I index loses the endpoint; the Type-II index has its sharp bound. -/
theorem all_good_iff_explicit_forced_factor_cover :
    (∀ n : ℕ, 2 < n → Good n) ↔
      ∀ k : ℕ, (24 * k + 1).Prime →
        (∃ j : ℕ, j + 1 < 6 * k ∧
          ∃ c : ℕ, 0 < c ∧ c ∣ (6 * k + 1 + j) ^ 2 ∧
            (4 * j + 3) ∣ 4 * c + 1) ∨
        (∃ j : ℕ, 7 * j < 6 * k ∧
          ∃ d : ℕ, 0 < d ∧ d < 6 * k + 1 + j ∧
            d ∣ (6 * k + 1 + j) ^ 2 ∧
            (4 * j + 3) ∣ 6 * k + 1 + j + d) := by
  have hcover : (∀ n : ℕ, 2 < n → Good n) ↔
      ∀ k : ℕ, (24 * k + 1).Prime →
        (∃ j : ℕ, j + 1 < 6 * k ∧ TypeI (24 * k + 1) (6 * k + 1 + j)) ∨
        (∃ j : ℕ, 7 * j < 6 * k ∧ TypeII (24 * k + 1) (6 * k + 1 + j)) := by
    constructor
    · intro hall k hpp
      exact (good_iff_hard_omit_forced_endpoint k hpp).mp (hall _ (by
        have := hpp.two_le
        omega))
    · intro hforall
      apply good_of_hard_primes
      intro p hpp hmod
      have heq : p = 24 * (p / 24) + 1 := by omega
      have hp' : (24 * (p / 24) + 1).Prime := by rwa [← heq]
      have hg := (good_iff_hard_omit_forced_endpoint (p / 24) hp').mpr
        (hforall (p / 24) hp')
      rwa [← heq] at hg
  simpa only [TypeI, TypeII, hard_shift_eq] using hcover

end Erdos242
