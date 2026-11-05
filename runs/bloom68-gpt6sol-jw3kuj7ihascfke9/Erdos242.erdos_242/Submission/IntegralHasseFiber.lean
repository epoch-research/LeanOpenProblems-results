import Submission.Classification

/-!
# An everywhere-locally soluble ordered Erdős–Straus fiber without positive integer points

This file does not import or change `Submission/Spec.lean`.  Its statements concern
only the *fixed first denominator* `x = 49` at the hard prime `p = 193`.
It does not supply a counterexample to the Erdős–Straus conjecture: the same
prime has ordered solutions with a different first denominator.
-/

namespace Erdos242

/-- The local-to-global test case is a genuine hard prime, with the
minimal eligible first denominator. -/
theorem hard_prime_193_and_first_49 :
    Nat.Prime 193 ∧ 193 % 24 = 1 ∧ 49 = (193 + 3) / 4 := by norm_num


private theorem divisor_product_prime_powers_mod_three (p q i j d : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hp3 : p % 3 = 1) (hq3 : q % 3 = 1)
    (hd : d ∣ p ^ i * q ^ j) : d % 3 = 1 := by
  classical
  have hmem : d ∈ (p ^ i * q ^ j).divisors :=
    Nat.mem_divisors.mpr ⟨hd, by have hpp := hp.pos; have hqq := hq.pos; positivity⟩
  rw [Nat.divisors_mul] at hmem
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.mem_mul.mp hmem
  have hu' : u ∣ p ^ i := (Nat.mem_divisors.mp hu).1
  have hv' : v ∣ q ^ j := (Nat.mem_divisors.mp hv).1
  obtain ⟨r, _, hr⟩ := (Nat.dvd_prime_pow hp).mp hu'
  obtain ⟨s, _, hs⟩ := (Nat.dvd_prime_pow hq).mp hv'
  have humod : u % 3 = 1 := by simp [hr, Nat.pow_mod, hp3]
  have hvmod : v % 3 = 1 := by simp [hs, Nat.pow_mod, hq3]
  rw [← huv, Nat.mul_mod, humod, hvmod]

private theorem divisor_of_9457_sq_mod_three (d : ℕ) (hd : d ∣ 9457 ^ 2) :
    d % 3 = 1 := by
  have hfac : 9457 ^ 2 = 7 ^ 4 * 193 ^ 2 := by norm_num
  exact divisor_product_prime_powers_mod_three 7 193 4 2 d
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by rwa [hfac] at hd)

/-- Both branches of the *exact* ordered divisor criterion fail at the
minimal candidate `x=49` for `p=193`.  This says nothing about the
remaining `47` candidate first denominators of this prime. -/
theorem no_typeI_or_typeII_193_49 : ¬ TypeI 193 49 ∧ ¬ TypeII 193 49 := by
  have hdiv : 49 ^ 2 ∣ 9457 ^ 2 := by norm_num
  constructor
  · rintro ⟨c, _, hc, hac⟩
    have hres : c % 3 = 1 := divisor_of_9457_sq_mod_three c (dvd_trans hc hdiv)
    have hthree : 3 ∣ 4 * c + 1 := by simpa only [show 4 * 49 - 193 = 3 by norm_num] using hac
    have hzero : (4 * c + 1) % 3 = 0 := Nat.mod_eq_zero_of_dvd hthree
    omega
  · rintro ⟨d, _, _, hd, had⟩
    have hres : d % 3 = 1 := divisor_of_9457_sq_mod_three d (dvd_trans hd hdiv)
    have hthree : 3 ∣ 49 + d := by simpa only [show 4 * 49 - 193 = 3 by norm_num] using had
    have hzero : (49 + d) % 3 = 0 := Nat.mod_eq_zero_of_dvd hthree
    omega

/-- The fiber `3*y*z = (193*49)*(y+z)` has no point with `y,z>0`.
The key is `(3y-9457)(3z-9457)=9457²` and the fact that all positive
divisors of `9457² = 7⁴*193²` are `1 (mod 3)`. -/
theorem no_positive_integral_fiber_193_49 :
    ¬ ∃ y z : ℕ, 0 < y ∧ 0 < z ∧ 3 * y * z = 9457 * (y + z) := by
  rintro ⟨y, z, hy, hz, heq⟩
  have hylt : 9457 < 3 * y := by
    apply (Nat.mul_lt_mul_right hz).mp
    nlinarith only [heq, hy]
  have hzlt : 9457 < 3 * z := by
    apply (Nat.mul_lt_mul_right hy).mp
    nlinarith only [heq, hz]
  let d := 3 * y - 9457
  let e := 3 * z - 9457
  have hd : d + 9457 = 3 * y := by dsimp [d]; omega
  have he : e + 9457 = 3 * z := by dsimp [e]; omega
  have hprod : d * e = 9457 ^ 2 := by nlinarith only [heq, hd, he]
  have hdvd : d ∣ 9457 ^ 2 := by rw [← hprod]; exact dvd_mul_right d e
  have hmod := divisor_of_9457_sq_mod_three d hdvd
  norm_num at hmod
  omega

/-- In the exact rational equation from `Spec.lean`, the prime `193`
cannot have `49` as its first denominator (in fact no positive `y,z` work). -/
theorem no_ordered_first_49_at_193 :
    ¬ ∃ y z : ℕ, 49 < y ∧ y < z ∧
      (4 / 193 : ℚ) = 1 / 49 + 1 / y + 1 / z := by
  rintro ⟨y, z, hxy, hyz, heq⟩
  have hy : 0 < y := by omega
  have hz : 0 < z := by omega
  have hyq : (y : ℚ) ≠ 0 := by exact_mod_cast (by omega : y ≠ 0)
  have hzq : (z : ℚ) ≠ 0 := by exact_mod_cast (by omega : z ≠ 0)
  have hpolyQ : 3 * (y : ℚ) * z = 9457 * (y + z) := by
    field_simp at heq
    nlinarith only [heq]
  have hpoly : 3 * y * z = 9457 * (y + z) := by exact_mod_cast hpolyQ
  exact no_positive_integral_fiber_193_49 ⟨y, z, hy, hz, hpoly⟩

/-- There is nevertheless a positive, strictly ordered *rational* point on
this very fiber.  It is the rational section `y=px/2, z=px`. -/
theorem ordered_rational_fiber_193_49 :
    (49 : ℚ) < 9457 / 2 ∧ (9457 / 2 : ℚ) < 9457 ∧
      (4 / 193 : ℚ) = 1 / 49 + 1 / (9457 / 2 : ℚ) + 1 / 9457 := by
  constructor
  · norm_num
  constructor
  · norm_num
  · norm_num

/-- The *next* candidate `x=50` has a type-I certificate `c=5`,
so the prime `193` itself is decidedly not a counterexample. -/
theorem typeI_193_at_50 : TypeI 193 50 := by
  refine ⟨5, by norm_num, by norm_num, ?_⟩
  norm_num

theorem ordered_193_at_50 :
    (50 : ℕ) < 1450 ∧ (1450 : ℕ) < 27985 ∧
      (4 / 193 : ℚ) = 1 / 50 + 1 / 1450 + 1 / 27985 := by norm_num

/-- A second certified, strictly ordered triple for the same hard prime. -/
theorem ordered_193_elsewhere :
    (52 : ℕ) < 772 ∧ (772 : ℕ) < 5018 ∧
      (4 / 193 : ℚ) = 1 / 52 + 1 / 772 + 1 / 5018 := by norm_num

/-- An exact integral solution outside the positive cone.  Its Jacobian
entry `3*y-9457` is `-1`, hence a unit modulo every positive modulus.
This gives smooth integral points at every finite place, not an ordered
positive integer solution. -/
theorem signed_integer_fiber_193_49 :
    (49 : ℤ) < 3152 ∧ (-29808464 : ℤ) < 0 ∧
      3 * (3152 : ℤ) * (-29808464) =
        9457 * (3152 + (-29808464) : ℤ) ∧
      3 * (3152 : ℤ) - 9457 = -1 := by norm_num

/-- For *every* modulus, the equation has an ordered natural-number
solution modulo that modulus with an invertible derivative in `z`.
Indeed `3*y-9457=-1`, and the exact defect is `m*29811617`.
This does NOT assert the fraction equation holds over positive integers. -/
theorem smooth_ordered_approximation_193_49 (m : ℕ) (hm : 0 < m) :
    ∃ y z : ℕ, 49 < y ∧ y < z ∧
      9457 = 3 * y + 1 ∧
      9457 * (y + z) = 3 * y * z + m * 29811617 := by
  refine ⟨3152, 3153 + (m - 1) * 29811617, by omega, ?_, by norm_num, ?_⟩
  · omega
  · have heq : m - 1 + 1 = m := by omega
    dsimp
    omega


/-- Uniform version of the local calculation.  At the minimal candidate
`x=6*k+1` for `p=24*k+1`, put `N=p*x` and `y=(N-1)/3`.
For every positive modulus `m` there is `z>y>x` with
`N*(y+z)-3*y*z = m*((N+1)*y+1)`, while `N=3*y+1` makes the
`z`-derivative of `3*y*z-N*(y+z)` equal to `-1`.
This is an *approximate* solution at each modulus, not an exact one. -/
theorem hard_first_fiber_smooth_approximation (k m : ℕ)
    (hk : 0 < k) (hm : 0 < m) :
    ∃ y z : ℕ, 6 * k + 1 < y ∧ y < z ∧
      (24 * k + 1) * (6 * k + 1) = 3 * y + 1 ∧
      (24 * k + 1) * (6 * k + 1) * (y + z) =
        3 * y * z + m * (((24 * k + 1) * (6 * k + 1) + 1) * y + 1) := by
  let N := (24 * k + 1) * (6 * k + 1)
  let y := 48 * k ^ 2 + 10 * k
  let T := (N + 1) * y + 1
  let z := y + 1 + (m - 1) * T
  have hksq : k ≤ k ^ 2 := by
    simpa only [one_mul, pow_two] using Nat.mul_le_mul_right k (by omega : 1 ≤ k)
  have hxy : 6 * k + 1 < y := by dsimp [y]; omega
  have hyz : y < z := by dsimp [z]; omega
  have hN : N = 3 * y + 1 := by dsimp [N, y]; ring
  have hT : N * y + z = m * T := by
    calc
      N * y + z = N * y + (y + 1 + (m - 1) * T) := rfl
      _ = T + (m - 1) * T := by dsimp [T]; ring
      _ = (m - 1 + 1) * T := by ring
      _ = m * T := by
        have heq : m - 1 + 1 = m := by omega
        rw [heq]
  have hpoly : N * (y + z) = 3 * y * z + m * T := by
    calc
      N * (y + z) = N * y + N * z := by ring
      _ = N * y + (3 * y + 1) * z := by rw [hN]
      _ = 3 * y * z + (N * y + z) := by ring
      _ = 3 * y * z + m * T := by rw [hT]
  exact ⟨y, z, hxy, hyz, hN, hpoly⟩

/-- Explicit failure of a *positive-ordered* integral local-to-global
implication on the fiber `p=193,x=49`: for every modulus there is a
strictly ordered congruence solution with `9457=3*y+1` (unit derivative),
but there is no positive integer solution to the exact equation.
This is not a counterexample to `Good 193` or to ordinary Hasse for the
unrestricted affine variety. -/
theorem ordered_local_not_positive_global_193_49 :
    (∀ m : ℕ, 0 < m → ∃ y z : ℕ, 49 < y ∧ y < z ∧
      9457 = 3 * y + 1 ∧ m ∣ (9457 * (y + z) - 3 * y * z)) ∧
    ¬ ∃ y z : ℕ, 0 < y ∧ 0 < z ∧ 3 * y * z = 9457 * (y + z) := by
  constructor
  · intro m hm
    obtain ⟨y, z, hxy, hyz, hunit, heq⟩ := smooth_ordered_approximation_193_49 m hm
    refine ⟨y, z, hxy, hyz, hunit, ?_⟩
    have hsub : 9457 * (y + z) - 3 * y * z = m * 29811617 := by omega
    rw [hsub]
    exact dvd_mul_right m _
  · exact no_positive_integral_fiber_193_49



end Erdos242
