import Submission.BilinearFactor

/-!
# A reciprocity obstruction for the restricted auxiliary-factor family

For every square `24k+1=s²`, no auxiliary product can have
`q+1=(4i+3)t` and `(4i+3)(24k+1)+1=4qc`. Quadratic reciprocity
for Jacobi symbols forces the odd part of `q` to see `s²` as a
nonresidue, an impossibility. The argument is **not** a proof about
prime hard inputs, and it excludes only Type I with the additional
requirement `c∣x`, not all possible Type I or Type II witnesses.
`Submission.Spec` is neither imported nor changed.
-/

namespace Erdos242
private theorem sq_jacobi_ne_neg_one (s q : ℕ) :
    jacobiSym ((s : ℤ) ^ 2) q ≠ -1 := by
  rw [jacobiSym.pow_left]
  rcases jacobiSym.trichotomy (s : ℤ) q with h | h | h <;> rw [h] <;> norm_num

/-- An odd divisor of `h*p+1` whose symbol modulo `h≡3 (mod 4)` is
negative *forces* `p` to be a quadratic nonresidue in the Jacobi sense.
The modulus `q` need not be prime. -/
private theorem odd_aux_forces_jacobi_neg_one (h q p : ℕ) (hh : h % 4 = 3)
    (hqodd : Odd q) (hqchi : jacobiSym (q : ℤ) h = -1)
    (hqdiv : q ∣ h * p + 1) : jacobiSym (p : ℤ) q = -1 := by
  obtain ⟨r, hr⟩ := hqdiv
  have heqZ : (h : ℤ) * (p : ℤ) + 1 = (q : ℤ) * r := by exact_mod_cast hr
  have hmod : ((h : ℤ) * (p : ℤ)) % (q : ℤ) = (-1 : ℤ) % (q : ℤ) := by
    calc
      ((h : ℤ) * (p : ℤ)) % (q : ℤ) =
          (((h : ℤ) * (p : ℤ) + 1) - 1) % (q : ℤ) := by simp
      _ = ((q : ℤ) * (r : ℤ) - 1) % (q : ℤ) := by rw [heqZ]
      _ = (((q : ℤ) * (r : ℤ)) + (-1 : ℤ)) % (q : ℤ) := by simp only [sub_eq_add_neg]
      _ = (-1 : ℤ) % (q : ℤ) := by simp [Int.add_emod]
  have hmul : jacobiSym (h : ℤ) q * jacobiSym (p : ℤ) q =
      jacobiSym (-1) q := by
    rw [← jacobiSym.mul_left]
    exact jacobiSym.mod_left' hmod
  have hodd : Odd h := Nat.odd_iff.mpr (by omega)
  rcases (Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hqodd)) with hq1 | hq3
  · have hrec : jacobiSym (h : ℤ) q = jacobiSym (q : ℤ) h :=
      jacobiSym.quadratic_reciprocity_one_mod_four' hodd hq1
    have hJ : jacobiSym (h : ℤ) q = -1 := hrec.trans hqchi
    have hneg : jacobiSym (-1) q = 1 := by
      rw [jacobiSym.at_neg_one hqodd, ZMod.χ₄_nat_one_mod_four hq1]
    rw [hJ, hneg] at hmul
    omega
  · have hrec : jacobiSym (h : ℤ) q = -jacobiSym (q : ℤ) h :=
      jacobiSym.quadratic_reciprocity_three_mod_four hh hq3
    have hJ : jacobiSym (h : ℤ) q = 1 := by rw [hqchi] at hrec; simpa using hrec
    have hneg : jacobiSym (-1) q = -1 := by
      rw [jacobiSym.at_neg_one hqodd, ZMod.χ₄_nat_three_mod_four hq3]
    rwa [hJ, hneg, one_mul] at hmul

private theorem odd_aux_square_impossible (h q s : ℕ) (hh : h % 4 = 3)
    (hqodd : Odd q) (hqchi : jacobiSym (q : ℤ) h = -1)
    (hqdiv : q ∣ h * s ^ 2 + 1) : False := by
  have hJ := odd_aux_forces_jacobi_neg_one h q (s ^ 2) hh hqodd hqchi hqdiv
  exact (sq_jacobi_ne_neg_one s q) (by simpa only [Nat.cast_pow] using hJ)

private theorem jacobi_predecessor (h q t : ℕ) (hh : h % 4 = 3)
    (hqt : q + 1 = h * t) : jacobiSym (q : ℤ) h = -1 := by
  have hodd : Odd h := Nat.odd_iff.mpr (by omega)
  have hqtZ : (q : ℤ) + 1 = (h : ℤ) * t := by exact_mod_cast hqt
  have hmod : (q : ℤ) % (h : ℤ) = (-1 : ℤ) % (h : ℤ) := by
    calc
      (q : ℤ) % (h : ℤ) = ((h : ℤ) * t + (-1 : ℤ)) % (h : ℤ) := by
        congr 1
        omega
      _ = (-1 : ℤ) % (h : ℤ) := by simp [Int.add_emod]
  rw [jacobiSym.mod_left' hmod, jacobiSym.at_neg_one hodd,
    ZMod.χ₄_nat_three_mod_four hh]

/-- If `q|( (4i+3)(24k+1)+1 )/4` and `q≡-1 (mod 4i+3)`, its
**odd part** has negative Jacobi symbol modulo `4i+3`. The potentially
even `q` is handled by `M_i≡i+1 (mod 2)`: when `q` is even, `i` is
odd and `4i+3≡7 (mod 8)`, so extracting powers of `2` does not
alter the Jacobi sign. -/
private theorem auxiliary_odd_part_negative (k i q t : ℕ) (ht : 0 < t)
    (hqt : q + 1 = (4 * i + 3) * t)
    (hqdivM : q ∣ auxiliaryFactor k i) :
    Odd (ordCompl[2] q) ∧
      jacobiSym ((ordCompl[2] q : ℕ) : ℤ) (4 * i + 3) = -1 := by
  let h := 4 * i + 3
  let q0 := ordCompl[2] q
  have hhmod : h % 4 = 3 := by dsimp [h]; omega
  have hodd : Odd h := Nat.odd_iff.mpr (by omega)
  have hht : 3 ≤ h * t := by
    have hmul := Nat.mul_le_mul_left h (show 1 ≤ t by omega)
    dsimp [h] at *
    omega
  have hqpos : 0 < q := by dsimp [h] at hht hqt; omega
  have hqnonzero : q ≠ 0 := by omega
  have hno2q0 : ¬2 ∣ q0 := Nat.not_dvd_ordCompl (by norm_num) hqnonzero
  have hq0odd : Odd q0 := Nat.odd_iff.mpr (by
    have hq0mod : q0 % 2 ≠ 0 := by
      intro heq
      exact hno2q0 (Nat.dvd_of_mod_eq_zero heq)
    omega)
  have hdec := Nat.ordProj_mul_ordCompl_eq_self q 2
  have hJdec : jacobiSym (q : ℤ) h =
      jacobiSym (2 : ℤ) h ^ q.factorization 2 * jacobiSym (q0 : ℤ) h := by
    calc
      jacobiSym (q : ℤ) h =
          jacobiSym (((2 ^ q.factorization 2 * q0 : ℕ) : ℤ)) h := by rw [hdec]
      _ = jacobiSym (2 : ℤ) h ^ q.factorization 2 * jacobiSym (q0 : ℤ) h := by
        rw [Nat.cast_mul, Nat.cast_pow, jacobiSym.mul_left, jacobiSym.pow_left]
        norm_num
  have hpow : jacobiSym (2 : ℤ) h ^ q.factorization 2 = 1 := by
    by_cases hi0 : i % 2 = 0
    · have hparity : auxiliaryFactor k i =
          2 * ((4 * i + 3) * (3 * k)) + i + 1 := by
        unfold auxiliaryFactor
        ring
      have hM2 : auxiliaryFactor k i % 2 = 1 := by
        rw [hparity]
        omega
      have hqodd : ¬2 ∣ q := by
        intro hd
        have h2M : 2 ∣ auxiliaryFactor k i := dvd_trans hd hqdivM
        have hzero := Nat.mod_eq_zero_of_dvd h2M
        omega
      have hfaczero : q.factorization 2 = 0 :=
        Nat.factorization_eq_zero_of_not_dvd hqodd
      simp [hfaczero]
    · have hi1 : i % 2 = 1 := by omega
      have hh7 : h % 8 = 7 := by dsimp [h]; omega
      have hJ2 : jacobiSym (2 : ℤ) h = 1 := by
        rw [jacobiSym.at_two hodd, ZMod.χ₈_nat_eq_if_mod_eight]
        have hoddmod : h % 2 = 1 := by omega
        simp [hoddmod, hh7]
      rw [hJ2]
      simp
  have hJq : jacobiSym (q : ℤ) h = -1 :=
    jacobi_predecessor h q t hhmod hqt
  have hJq0 : jacobiSym (q0 : ℤ) h = -1 := by
    rw [hJdec, hpow, one_mul] at hJq
    exact hJq
  exact ⟨hq0odd, by simpa [h, q0] using hJq0⟩


/-- Square hard integers have no auxiliary factor product, even before one
requires the resulting first denominator to lie in the ordered interval. -/
theorem square_factor_product_impossible (k i q c t s : ℕ)
    (hsq : s ^ 2 = 24 * k + 1) (ht : 0 < t)
    (hqt : q + 1 = (4 * i + 3) * t)
    (hpc : (4 * i + 3) * (24 * k + 1) + 1 = 4 * q * c) : False := by
  let h := 4 * i + 3
  let q0 := ordCompl[2] q
  have hhmod : h % 4 = 3 := by dsimp [h]; omega
  have haux := auxiliaryFactor_identity k i
  have hM : auxiliaryFactor k i = q * c := by nlinarith only [haux, hpc]
  have hqdivM : q ∣ auxiliaryFactor k i := ⟨c, hM⟩
  obtain ⟨hq0odd, hJq0⟩ := auxiliary_odd_part_negative k i q t ht hqt hqdivM
  have hqdiv : q ∣ h * s ^ 2 + 1 := by
    have heq : h * s ^ 2 + 1 = 4 * q * c := by
      rw [hsq]
      exact hpc
    rw [heq]
    refine ⟨4 * c, ?_⟩
    ring
  have hq0div : q0 ∣ h * s ^ 2 + 1 :=
    dvd_trans (Nat.ordCompl_dvd q 2) hqdiv
  exact odd_aux_square_impossible h q0 s hhmod hq0odd hJq0 hq0div

/-- Every eligible auxiliary product `q+1=(4i+3)t`,
`(4i+3)(24k+1)+1=4qc` has Jacobi `(q/(24k+1))=-1`, including
**even or composite** `q`, and without assuming that `24k+1` is prime.
This is a *necessary sign* of a restricted Type-I certificate, not an
existence theorem; the sign alone does not force either full divisor
criterion at any first denominator. -/
theorem factor_product_jacobi_neg_one (k i q c t : ℕ) (ht : 0 < t)
    (hqt : q + 1 = (4 * i + 3) * t)
    (hpc : (4 * i + 3) * (24 * k + 1) + 1 = 4 * q * c) :
    jacobiSym (q : ℤ) (24 * k + 1) = -1 := by
  let h := 4 * i + 3
  let p := 24 * k + 1
  let q0 := ordCompl[2] q
  have hhmod : h % 4 = 3 := by dsimp [h]; omega
  have hpmod4 : p % 4 = 1 := by dsimp [p]; omega
  have hpmod8 : p % 8 = 1 := by dsimp [p]; omega
  have hpodd : Odd p := Nat.odd_iff.mpr (by omega)
  have haux := auxiliaryFactor_identity k i
  have hM : auxiliaryFactor k i = q * c := by nlinarith only [haux, hpc]
  have hqdivM : q ∣ auxiliaryFactor k i := ⟨c, hM⟩
  obtain ⟨hq0odd, hJq0h⟩ := auxiliary_odd_part_negative k i q t ht hqt hqdivM
  have hqdiv : q ∣ h * p + 1 := by
    change q ∣ (4 * i + 3) * (24 * k + 1) + 1
    rw [hpc]
    refine ⟨4 * c, ?_⟩
    ring
  have hq0div : q0 ∣ h * p + 1 := dvd_trans (Nat.ordCompl_dvd q 2) hqdiv
  have hJpq0 : jacobiSym (p : ℤ) q0 = -1 :=
    odd_aux_forces_jacobi_neg_one h q0 p hhmod hq0odd hJq0h hq0div
  have hrec : jacobiSym (p : ℤ) q0 = jacobiSym (q0 : ℤ) p :=
    jacobiSym.quadratic_reciprocity_one_mod_four hpmod4 hq0odd
  have hJq0p : jacobiSym (q0 : ℤ) p = -1 := hrec.symm.trans hJpq0
  have hJ2p : jacobiSym (2 : ℤ) p = 1 := by
    rw [jacobiSym.at_two hpodd, ZMod.χ₈_nat_eq_if_mod_eight]
    have hoddmod : p % 2 = 1 := by omega
    simp [hoddmod, hpmod8]
  have hdec := Nat.ordProj_mul_ordCompl_eq_self q 2
  have hJdec : jacobiSym (q : ℤ) p =
      jacobiSym (2 : ℤ) p ^ q.factorization 2 * jacobiSym (q0 : ℤ) p := by
    calc
      jacobiSym (q : ℤ) p =
          jacobiSym (((2 ^ q.factorization 2 * q0 : ℕ) : ℤ)) p := by rw [hdec]
      _ = jacobiSym (2 : ℤ) p ^ q.factorization 2 * jacobiSym (q0 : ℤ) p := by
        rw [Nat.cast_mul, Nat.cast_pow, jacobiSym.mul_left, jacobiSym.pow_left]
        norm_num
  change jacobiSym (q : ℤ) p = -1
  rw [hJdec, hJ2p, one_pow, one_mul]
  exact hJq0p

/-- The nonresidue conclusion applies directly to the bounded auxiliary
divisor test, including composite `q`. A *nonresidue* in the other
direction alone does not give the required factor or congruence. -/
theorem auxiliary_divisor_jacobi_neg_one (k i q : ℕ)
    (hq : 1 < q) (hdiv : q ∣ auxiliaryFactor k i)
    (hres : q % (4 * i + 3) = 4 * i + 2) :
    jacobiSym (q : ℤ) (24 * k + 1) = -1 := by
  obtain ⟨c, t, hc, ht, hqt, hpc⟩ :=
    factor_product_of_auxiliary_divisor k i q hq hdiv hres
  exact factor_product_jacobi_neg_one k i q c t ht hqt hpc

/-- In particular an eligible auxiliary divisor is a nonsquare modulo
`24k+1`; at a hard **prime**, it is a quadratic nonresidue. This is a
necessary condition for the restricted factor construction, not a
sufficient condition for any Egyptian-fraction witness. -/
theorem auxiliary_divisor_nonsquare (k i q : ℕ)
    (hq : 1 < q) (hdiv : q ∣ auxiliaryFactor k i)
    (hres : q % (4 * i + 3) = 4 * i + 2) :
    ¬IsSquare (q : ZMod (24 * k + 1)) := by
  simpa only [Int.cast_natCast] using
    (ZMod.nonsquare_of_jacobiSym_eq_neg_one
      (auxiliary_divisor_jacobi_neg_one k i q hq hdiv hres))



/-- The restricted `c∣x` Type-I family has no witness for ANY hard square
input, even if `x` is not initially required to be in the ordered range.
This makes no assertion about full Type I or Type II for squares. -/
theorem square_no_simple_typeI (k s : ℕ) (hsq : s ^ 2 = 24 * k + 1) :
    ¬∃ x c : ℕ, (24 * k + 1 < 4 * x) ∧ c ∣ x ∧
      (4 * x - (24 * k + 1)) ∣ 4 * c + 1 := by
  rintro ⟨x, c, hlo, hcx, hac⟩
  obtain ⟨i, q, t, ht, hq, hxt, hqt, hpc⟩ :=
    simple_typeI_factor_product (24 * k + 1) x c (by omega) hlo hcx hac
  exact square_factor_product_impossible k i q c t s hsq ht hqt hpc

/-- Consequently the exact bilinear representation of the restricted
subfamily does not exist for square values of `p=24k+1`. Primality cannot
be dropped from any putative universal prime existence theorem based solely
on the bilinear family. -/
theorem square_no_bilinear (k s : ℕ) (hsq : s ^ 2 = 24 * k + 1) :
    ¬∃ i t j : ℕ, 0 < t ∧
      6 * k + 1 = (3 * i + 2) * t + ((4 * i + 3) * t - 1) * j := by
  rintro ⟨i, t, j, ht, hrel⟩
  obtain ⟨q, c, hq, hc, hqt, hcform, hx, hpc⟩ :=
    factor_data_of_bilinear k i t j ht hrel
  exact square_factor_product_impossible k i q c t s hsq ht hqt hpc

/-- Unbounded square inputs `p=(24N+5)²=24k+1` fail the entire
restricted `c∣x`/bilinear factor test. They are composite for `N≥0`;
this does **not** exhibit a bad prime or rule out other solution types. -/
theorem arbitrarily_large_square_without_bilinear (N : ℕ) :
    ∃ k s : ℕ, N < k ∧ s ^ 2 = 24 * k + 1 ∧
      ¬∃ i t j : ℕ, 0 < t ∧
        6 * k + 1 = (3 * i + 2) * t + ((4 * i + 3) * t - 1) * j := by
  let k := 24 * N ^ 2 + 10 * N + 1
  let s := 24 * N + 5
  have hsq : s ^ 2 = 24 * k + 1 := by dsimp [s, k]; ring
  exact ⟨k, s, by dsimp [k]; omega, hsq, square_no_bilinear k s hsq⟩


end Erdos242
