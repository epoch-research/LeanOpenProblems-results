import Submission.PellBridge

/-!
# Uniform Pell endpoint saturation

Supporting formalization for Erdős problem 364, not a proof of EMW.
`Submission.Spec` is not imported. No existing helper is changed.

For a squarefree natural parameter, an even norm-one Pell point has both
signed endpoints powerful exactly when the parameter divides its y-coordinate.
At odd powers this applies to every seed whose x-coordinate is divisible by
four, without assuming canonical endpoint kernels or square/cube roots.

The exact saturation index is `d / Nat.gcd d ε.y.natAbs`. For every positive
parameter and every natural exponent (including zero), parameter-divisibility
of the powered y-coordinate is equivalent to divisibility of the exponent by
this index. The proof is a power recurrence modulo the parameter followed by
cancellation of a unit and a natural gcd divisibility identity. Squarefreeness,
y-positivity, and the residue class of the parameter are not needed for this
index theorem.

Nothing here makes the middle entry powerful. The least-full consequences
explicitly assume full powerfulness and use the existing squarefree-index
result only after those hypotheses have been supplied.
-/

namespace Erdos364.PellSaturation

open Erdos364.PowerfulStructure Erdos364.ChebyshevDescent Erdos364.PellBridge

/-- Prime divisibility detects divisibility by a squarefree natural number.
The proof multiplies distinct prime divisors; no valuation API is used. -/
theorem squarefree_dvd_iff_prime_dvd {d y : ℕ} (hd : Squarefree d) :
    d ∣ y ↔ ∀ p : ℕ, p.Prime → p ∣ d → p ∣ y := by
  constructor
  · intro h p _ hpd
    exact dvd_trans hpd h
  · intro h
    rw [← Nat.prod_primeFactors_of_squarefree hd]
    apply Finset.prod_dvd_of_isRelPrime
    · intro p hp q hq hpq
      apply Nat.coprime_iff_isRelPrime.mp
      apply (Nat.prime_of_mem_primeFactors hp).coprime_iff_not_dvd.mpr
      intro hpqd
      exact hpq ((Nat.prime_dvd_prime_iff_eq
        (Nat.prime_of_mem_primeFactors hp) (Nat.prime_of_mem_primeFactors hq)).mp hpqd)
    · intro p hp
      exact h p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)

/-- A squarefree kernel times a square is powerful exactly when the kernel
already divides the square root. This includes the root zero. -/
theorem powerful_squarefree_mul_sq_iff {d y : ℕ} (hd : Squarefree d) :
    Nat.Powerful (d * y ^ 2) ↔ d ∣ y := by
  constructor
  · intro h
    apply (squarefree_dvd_iff_prime_dvd hd).mpr
    intro p hp hpd
    have hs : p ^ 2 ∣ d * y ^ 2 :=
      (powerful_iff_prime_sq_divides _).mp h p hp (dvd_mul_of_dvd_left hpd _)
    have hpy : p ∣ y ^ 2 := by
      simpa only [pow_one] using
        hd.pow_dvd_of_squarefree_of_pow_succ_dvd_mul_right hp.prime hs
    exact hp.dvd_of_dvd_pow hpy
  · rintro ⟨a, rfl⟩
    have heq : d * (d * a) ^ 2 = d ^ 3 * a ^ 2 := by ring
    rw [heq]
    exact powerful_mul (powerful_cube d) (powerful_square a)

/-- Signed version of the squarefree-kernel saturation criterion. -/
theorem powerful_int_squarefree_mul_sq_iff {d : ℕ} (hd : Squarefree d) (y : ℤ) :
    Powerful ((d : ℤ) * y ^ 2) ↔ (d : ℤ) ∣ y := by
  simpa only [Powerful, Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_pow,
    Int.natCast_dvd] using (powerful_squarefree_mul_sq_iff (y := y.natAbs) hd)

/-- Even signed centers have coprime endpoint absolute values, regardless of
sign. The Bezout coefficients are constructed explicitly. -/
theorem even_center_endpoints_coprime {x : ℤ} (hx : Even x) :
    Nat.Coprime (x - 1).natAbs (x + 1).natAbs := by
  have hc : IsCoprime (x - 1) (x + 1) := by
    obtain ⟨k, rfl⟩ := hx
    exact ⟨-(k + 1), k, by ring⟩
  exact Int.isCoprime_iff_gcd_eq_one.mp hc

/-- For an even signed center, powerfulness of the endpoint product is
precisely powerfulness of both endpoints. -/
theorem powerful_endpoints_iff_product {x : ℤ} (hx : Even x) :
    (Powerful (x - 1) ∧ Powerful (x + 1)) ↔ Powerful ((x - 1) * (x + 1)) := by
  simpa only [Powerful, Int.natAbs_mul] using
    (powerful_mul_iff_of_coprime (even_center_endpoints_coprime hx)).symm

/-- Uniform endpoint criterion for a raw even Pell point. No fundamental-unit
or canonical-decomposition assumption is made. -/
theorem pell_endpoints_iff_dvd_y {d : ℕ} (hd : Squarefree d)
    (ε : Pell.Solution₁ (d : ℤ)) (hx : Even ε.x) :
    (Powerful (ε.x - 1) ∧ Powerful (ε.x + 1)) ↔ (d : ℤ) ∣ ε.y := by
  rw [powerful_endpoints_iff_product hx]
  have heq : (ε.x - 1) * (ε.x + 1) = (d : ℤ) * ε.y ^ 2 := by
    linear_combination ε.prop
  rw [heq]
  exact powerful_int_squarefree_mul_sq_iff hd ε.y

/-- Odd powers preserve four-divisibility of the raw seed's x-coordinate. -/
theorem pell_x_pow_four_dvd {d : ℤ} (ε : Pell.Solution₁ d)
    (hx : (4 : ℤ) ∣ ε.x) {n : ℕ} (hn : Odd n) : (4 : ℤ) ∣ (ε ^ n).x := by
  rw [pell_x_pow_eq_cheb]
  exact dvd_cheb_of_dvd hn hx

/-- The requested odd-power endpoint criterion. Positivity of d and y, the
residue d ≡ 7 mod 8, and a separate n > 0 assumption can all be omitted. -/
theorem pell_pow_endpoints_iff_dvd_y {d : ℕ} (hd : Squarefree d)
    (ε : Pell.Solution₁ (d : ℤ)) (hx : (4 : ℤ) ∣ ε.x) {n : ℕ} (hn : Odd n) :
    (Powerful ((ε ^ n).x - 1) ∧ Powerful ((ε ^ n).x + 1)) ↔
      (d : ℤ) ∣ (ε ^ n).y := by
  apply pell_endpoints_iff_dvd_y hd
  exact even_iff_two_dvd.mpr
    (dvd_trans (by norm_num : (2 : ℤ) ∣ 4) (pell_x_pow_four_dvd ε hx hn))

/-- Modulo any divisor of the parameter, the x-coordinate of a Pell power
is the corresponding power of the seed's x-coordinate. -/
theorem pell_x_pow_zmod {d m : ℕ} (ε : Pell.Solution₁ (d : ℤ)) (hm : m ∣ d) (n : ℕ) :
    ((ε ^ n).x : ZMod m) = (ε.x : ZMod m) ^ n := by
  have hd0 : (d : ZMod m) = 0 := by
    simpa only [Int.cast_natCast] using
      (ZMod.intCast_zmod_eq_zero_iff_dvd (d : ℤ) m).mpr (by exact_mod_cast hm)
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Pell.Solution₁.x_mul]
    push_cast
    rw [hd0, zero_mul, add_zero, ih, pow_succ]

/-- The exact y-coordinate recurrence modulo any divisor of d. In particular,
at a prime p | d it is (n+1) x^n y modulo p. -/
theorem pell_y_pow_succ_zmod {d m : ℕ} (ε : Pell.Solution₁ (d : ℤ))
    (hm : m ∣ d) (n : ℕ) :
    ((ε ^ (n + 1)).y : ZMod m) = (n + 1 : ℕ) * (ε.x : ZMod m) ^ n * (ε.y : ZMod m) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show n + 1 + 1 = (n + 1) + 1 by omega, pow_succ, Pell.Solution₁.y_mul]
    push_cast
    rw [pell_x_pow_zmod ε hm (n + 1), ih]
    simp only [pow_succ, Nat.cast_add, Nat.cast_one]
    ring

/-- Positive-index form of the y-coordinate congruence, with the precise
exponent n-1. The modulus need not be prime. -/
theorem pell_y_pow_zmod {d m : ℕ} (ε : Pell.Solution₁ (d : ℤ))
    (hm : m ∣ d) {n : ℕ} (hn : 0 < n) :
    ((ε ^ n).y : ZMod m) = (n : ZMod m) * (ε.x : ZMod m) ^ (n - 1) * (ε.y : ZMod m) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel] using pell_y_pow_succ_zmod ε hm k

/-- Norm one makes x a unit modulo every divisor of the parameter; no field
assumption on the modulus is required. -/
theorem pell_x_isUnit_zmod {d m : ℕ} (ε : Pell.Solution₁ (d : ℤ)) (hm : m ∣ d) :
    IsUnit (ε.x : ZMod m) := by
  have hnorm := congrArg (fun z : ℤ => (z : ZMod m)) ε.prop
  have hd0 : (d : ZMod m) = 0 := by
    simpa only [Int.cast_natCast] using
      (ZMod.intCast_zmod_eq_zero_iff_dvd (d : ℤ) m).mpr (by exact_mod_cast hm)
  push_cast at hnorm
  rw [hd0, zero_mul, sub_zero, pow_two] at hnorm
  exact IsUnit.of_mul_eq_one (ε.x : ZMod m) hnorm

/-- Modulo any divisor of d, a powered y-coordinate vanishes exactly when
n times the initial y does. The cancellation uses norm one, not a field. -/
theorem pell_dvd_y_pow_iff_dvd_mul_of_dvd {d m : ℕ} (ε : Pell.Solution₁ (d : ℤ))
    (hm : m ∣ d) (n : ℕ) :
    (m : ℤ) ∣ (ε ^ n).y ↔ (m : ℤ) ∣ (n : ℤ) * ε.y := by
  cases n with
  | zero => simp
  | succ n =>
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd _ m,
      ← ZMod.intCast_zmod_eq_zero_iff_dvd _ m]
    rw [pell_y_pow_succ_zmod ε hm n]
    push_cast
    have hu := (pell_x_isUnit_zmod ε hm).pow n
    calc
      (n + 1 : ZMod m) * (ε.x : ZMod m) ^ n * (ε.y : ZMod m) = 0 ↔
          (ε.x : ZMod m) ^ n * ((n + 1 : ZMod m) * (ε.y : ZMod m)) = 0 := by ring_nf
      _ ↔ (n + 1 : ZMod m) * (ε.y : ZMod m) = 0 := hu.mul_right_eq_zero

/-- Pure integer divisibility for every natural exponent. This does not require
d to be squarefree or positive, nor y to be positive. -/
theorem pell_dvd_y_pow_iff_dvd_mul {d : ℕ} (ε : Pell.Solution₁ (d : ℤ)) (n : ℕ) :
    (d : ℤ) ∣ (ε ^ n).y ↔ (d : ℤ) ∣ (n : ℤ) * ε.y :=
  pell_dvd_y_pow_iff_dvd_mul_of_dvd ε (dvd_refl d) n

/-- At a prime divisor of d, y-power divisibility is precisely p | n or
p | y. In particular an unsaturated seed forces p | n. -/
theorem pell_prime_dvd_y_pow_iff {d p : ℕ} (ε : Pell.Solution₁ (d : ℤ))
    (hp : p.Prime) (hpd : p ∣ d) (n : ℕ) :
    (p : ℤ) ∣ (ε ^ n).y ↔ p ∣ n ∨ (p : ℤ) ∣ ε.y := by
  rw [pell_dvd_y_pow_iff_dvd_mul_of_dvd ε hpd, Int.natCast_dvd,
    Int.natAbs_mul, Int.natAbs_natCast, hp.dvd_mul, Int.natCast_dvd]

/-- Natural gcd cancellation, including a zero initial multiplier. -/
theorem nat_dvd_mul_iff_div_gcd_dvd {d y n : ℕ} (hd : 0 < d) :
    d ∣ n * y ↔ d / Nat.gcd d y ∣ n := by
  symm
  calc
    d / Nat.gcd d y ∣ n ↔ d ∣ Nat.gcd d y * n :=
      Nat.div_dvd_iff_dvd_mul (Nat.gcd_dvd_left d y) (Nat.gcd_pos_of_pos_left y hd)
    _ ↔ d ∣ n * Nat.gcd d y := by rw [mul_comm]
    _ ↔ d ∣ n * y := Nat.dvd_mul_gcd_iff_dvd_mul

/-- The exact saturation index for the parameter and initial y-coordinate. -/
def saturationIndex {d : ℕ} (ε : Pell.Solution₁ (d : ℤ)) : ℕ :=
  d / Nat.gcd d ε.y.natAbs

/-- The saturation index is a positive divisor of every positive parameter. -/
theorem saturationIndex_pos_dvd {d : ℕ} (hd : 0 < d) (ε : Pell.Solution₁ (d : ℤ)) :
    0 < saturationIndex ε ∧ saturationIndex ε ∣ d := by
  refine ⟨?_, Nat.div_dvd_of_dvd (Nat.gcd_dvd_left d ε.y.natAbs)⟩
  exact Nat.div_pos (Nat.gcd_le_left _ hd) (Nat.gcd_pos_of_pos_left _ hd)

/-- For squarefree d the saturation index is squarefree as well. -/
theorem saturationIndex_squarefree {d : ℕ} (hd : Squarefree d)
    (ε : Pell.Solution₁ (d : ℤ)) : Squarefree (saturationIndex ε) := by
  exact hd.squarefree_of_dvd (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left d ε.y.natAbs))

/-- Exact saturation for all natural exponents, including zero. No parity,
squarefreeness, fundamentalness, or sign hypothesis on either coordinate is used. -/
theorem pell_dvd_y_pow_iff_index_dvd {d : ℕ} (hd : 0 < d)
    (ε : Pell.Solution₁ (d : ℤ)) (n : ℕ) :
    (d : ℤ) ∣ (ε ^ n).y ↔ saturationIndex ε ∣ n := by
  rw [pell_dvd_y_pow_iff_dvd_mul, Int.natCast_dvd, Int.natAbs_mul, Int.natAbs_natCast]
  exact nat_dvd_mul_iff_div_gcd_dvd hd

/-- Signed-exponent version of exact saturation. Negative powers negate the
y-coordinate, so the same index detects every integer exponent as well. -/
theorem pell_dvd_y_zpow_iff_index_dvd {d : ℕ} (hd : 0 < d)
    (ε : Pell.Solution₁ (d : ℤ)) (n : ℤ) :
    (d : ℤ) ∣ (ε ^ n).y ↔ (saturationIndex ε : ℤ) ∣ n := by
  cases n with
  | ofNat n =>
    change (d : ℤ) ∣ (ε ^ (n : ℤ)).y ↔ (saturationIndex ε : ℤ) ∣ (n : ℤ)
    rw [zpow_natCast, Int.natCast_dvd_natCast]
    exact pell_dvd_y_pow_iff_index_dvd hd ε n
  | negSucc n =>
    simpa only [zpow_negSucc, Pell.Solution₁.y_inv, dvd_neg, Int.natCast_dvd,
      Int.natAbs_negSucc, Nat.succ_eq_add_one] using
      pell_dvd_y_pow_iff_index_dvd hd ε (n + 1)

/-- Thus the positive saturation index really is the least positive exponent
whose y-coordinate is divisible by the parameter. -/
theorem saturationIndex_is_least {d : ℕ} (hd : 0 < d)
    (ε : Pell.Solution₁ (d : ℤ)) :
    0 < saturationIndex ε ∧ (d : ℤ) ∣ (ε ^ saturationIndex ε).y ∧
      ∀ n : ℕ, 0 < n → (d : ℤ) ∣ (ε ^ n).y → saturationIndex ε ≤ n := by
  refine ⟨(saturationIndex_pos_dvd hd ε).1,
    (pell_dvd_y_pow_iff_index_dvd hd ε _).mpr (dvd_refl _), ?_⟩
  intro n hn hdiv
  exact Nat.le_of_dvd hn ((pell_dvd_y_pow_iff_index_dvd hd ε n).mp hdiv)

/-- Uniform endpoint criterion with its exact arithmetic progression of odd
indices. This conclusion concerns only the endpoints, not full powerfulness. -/
theorem pell_pow_endpoints_iff_index_dvd {d : ℕ} (hdpos : 0 < d) (hd : Squarefree d)
    (ε : Pell.Solution₁ (d : ℤ)) (hx : (4 : ℤ) ∣ ε.x) {n : ℕ} (hn : Odd n) :
    (Powerful ((ε ^ n).x - 1) ∧ Powerful ((ε ^ n).x + 1)) ↔ saturationIndex ε ∣ n :=
  (pell_pow_endpoints_iff_dvd_y hd ε hx hn).trans (pell_dvd_y_pow_iff_index_dvd hdpos ε n)

/-- At a least full center, the existing squarefree-index theorem and the
endpoint criterion give n = I*m with squarefree, coprime factors. The full
center hypothesis is essential and is explicitly supplied. -/
theorem least_full_index_decomposition {d : ℕ} (hdpos : 0 < d) (hd : Squarefree d)
    (ε : Pell.Solution₁ (d : ℤ)) (hx : 4 ≤ ε.x) (hx4 : (4 : ℤ) ∣ ε.x)
    {t : ℤ} {n : ℕ} (hn : Odd n) (ht : LeastFull t) (heq : t = cheb n ε.x) :
    saturationIndex ε ∣ n ∧ ∃ m : ℕ, n = saturationIndex ε * m ∧
      Squarefree (saturationIndex ε) ∧ Squarefree m ∧ Nat.Coprime (saturationIndex ε) m := by
  have hpow : (ε ^ n).x = t := (pell_x_pow_eq_cheb ε n).trans heq.symm
  have hends : Powerful ((ε ^ n).x - 1) ∧ Powerful ((ε ^ n).x + 1) := by
    rw [hpow]
    exact ⟨ht.2.1.1, ht.2.1.2.2⟩
  have hdiv := (pell_pow_endpoints_iff_index_dvd hdpos hd ε hx4 hn).mp hends
  have hsf : Squarefree n := least_full_index_squarefree hx hn ht heq
  obtain ⟨m, hm⟩ := hdiv
  have hfac := Nat.squarefree_mul_iff.mp (hm ▸ hsf)
  exact ⟨⟨m, hm⟩, m, hm, hfac.2.1, hfac.2.2, hfac.1⟩

/-- An actual least natural full center supplies a fundamental Pell seed with
the exact saturated-index decomposition. This is only a conditional structural
consequence, not an existence or nonexistence theorem for powerful triples. -/
theorem leastNatFull_exists_saturated_index {t : ℕ} (ht : LeastNatFull t) :
    ∃ d : ℕ, 0 < d ∧ Squarefree d ∧ d % 8 = 7 ∧ ¬IsSquare (d : ℤ) ∧
      ∃ ε : Pell.Solution₁ (d : ℤ), Pell.IsFundamental ε ∧
        4 ≤ ε.x ∧ (4 : ℤ) ∣ ε.x ∧ 0 < ε.y ∧
        ∃ n : ℕ, 0 < n ∧ Odd n ∧ Squarefree n ∧ (t : ℤ) = cheb n ε.x ∧
          saturationIndex ε ∣ n ∧ ∃ m : ℕ, n = saturationIndex ε * m ∧
            Squarefree (saturationIndex ε) ∧ Squarefree m ∧ Nat.Coprime (saturationIndex ε) m := by
  obtain ⟨d, hdpos, hd, hdmod, hdns, ε, hfund, hx, hx4, hy, n, hnpos, hn, hnsf, heq⟩ :=
    leastNatFull_exists_odd_squarefree_index ht
  have hdec := least_full_index_decomposition hdpos hd ε hx hx4 hn
    (leastNatFull_iff_leastFull.mp ht) heq
  exact ⟨d, hdpos, hd, hdmod, hdns, ε, hfund, hx, hx4, hy, n, hnpos, hn, hnsf, heq, hdec⟩

end Erdos364.PellSaturation

-- Exhaustive audit of every public definition and theorem in this helper.
#print axioms Erdos364.PellSaturation.squarefree_dvd_iff_prime_dvd
#print axioms Erdos364.PellSaturation.powerful_squarefree_mul_sq_iff
#print axioms Erdos364.PellSaturation.powerful_int_squarefree_mul_sq_iff
#print axioms Erdos364.PellSaturation.even_center_endpoints_coprime
#print axioms Erdos364.PellSaturation.powerful_endpoints_iff_product
#print axioms Erdos364.PellSaturation.pell_endpoints_iff_dvd_y
#print axioms Erdos364.PellSaturation.pell_x_pow_four_dvd
#print axioms Erdos364.PellSaturation.pell_pow_endpoints_iff_dvd_y
#print axioms Erdos364.PellSaturation.pell_x_pow_zmod
#print axioms Erdos364.PellSaturation.pell_y_pow_succ_zmod
#print axioms Erdos364.PellSaturation.pell_y_pow_zmod
#print axioms Erdos364.PellSaturation.pell_x_isUnit_zmod
#print axioms Erdos364.PellSaturation.pell_dvd_y_pow_iff_dvd_mul_of_dvd
#print axioms Erdos364.PellSaturation.pell_dvd_y_pow_iff_dvd_mul
#print axioms Erdos364.PellSaturation.pell_prime_dvd_y_pow_iff
#print axioms Erdos364.PellSaturation.nat_dvd_mul_iff_div_gcd_dvd
#print axioms Erdos364.PellSaturation.saturationIndex
#print axioms Erdos364.PellSaturation.saturationIndex_pos_dvd
#print axioms Erdos364.PellSaturation.saturationIndex_squarefree
#print axioms Erdos364.PellSaturation.pell_dvd_y_pow_iff_index_dvd
#print axioms Erdos364.PellSaturation.pell_dvd_y_zpow_iff_index_dvd
#print axioms Erdos364.PellSaturation.saturationIndex_is_least
#print axioms Erdos364.PellSaturation.pell_pow_endpoints_iff_index_dvd
#print axioms Erdos364.PellSaturation.least_full_index_decomposition
#print axioms Erdos364.PellSaturation.leastNatFull_exists_saturated_index
