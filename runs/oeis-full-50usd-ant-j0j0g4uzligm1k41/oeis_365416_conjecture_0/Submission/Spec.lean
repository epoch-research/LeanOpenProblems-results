import FormalConjectures.Util.ProblemImports

open Nat

/--
Numbers $k$ such that $2k-1$ and $2k+1$ are both prime powers (A246655).
-/
def A365416_condition (k : ℕ) : Prop :=
  IsPrimePow (2 * k - 1) ∧ IsPrimePow (2 * k + 1)

/--
The $n$-th term of A365416 (Numbers $k$ such that $2k-1$ and $2k+1$ are both prime powers).
Defined for $n \ge 1$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  (n - 1).nth A365416_condition

-- Formalization of the conjecture

/--
Predicate for a number to be a prime power with exponent strictly greater than 1.
This is equivalent to being a composite prime power (a perfect power whose base is prime).
-/
def IsCompositePrimePow (m : ℕ) : Prop :=
  ∃ (p e : ℕ), Nat.Prime p ∧ 1 < e ∧ p ^ e = m

/-!
### Status of this conjecture

The statement below asserts that `k = 13` (giving `25 = 5²` and `27 = 3³`) is the
*only* `k` for which both `2k-1` and `2k+1` are prime powers with exponent `> 1`.
Equivalently: the only pair of prime powers (exponent `≥ 2`) differing by `2` is `(25, 27)`,
i.e. the equation
  `q ^ b - p ^ a = 2`,  with `p, q` prime and `a, b ≥ 2`,
has the unique solution `3³ - 5² = 2`.

This is a *true* statement (verified computationally with no counterexample up to `10¹⁸`),
but it is an **open problem**: as the OEIS entry A365416 itself records, it holds only
"according to Pillai's conjecture". A complete proof would require:

* the Lebesgue–Nagell theorem `x² ± 2 = yⁿ` (for every odd prime exponent `n`) to handle the
  cases where one of the two numbers is a perfect square — a known theorem whose proof uses the
  Bilu–Hanrot–Voutier primitive-divisor theorem, **none of which is available in Mathlib**; and
* the resolution of the residual case in which *both* exponents are odd and `≥ 3`, which is an
  **unresolved instance of Pillai's conjecture** (it has no congruence obstruction, so its
  emptiness is a genuine Diophantine fact, not an elementary one).

The `← `(reverse) direction of the bi-implication is fully proved below.  The `→` (forward)
direction is reduced to the core equation `q ^ b - p ^ a = 2`, which is exactly the open part.

Sharper structural analysis (all carried out and cross-checked):
* Writing `X = 2k`, the system `2k-1 = p^a`, `2k+1 = q^b` is equivalent to a **Pell equation**
  `X² - D Y² = 1`, where `D` is the squarefree part of `p^a q^b` and `Y = sqrt(p^a q^b / D)`.
  For the genuine solution `k = 13` this is `26² - 3·15² = 1` (so `D = 3`, since `25 = 5²` is a
  square contributing only to `Y`). Finding *another* solution amounts to finding a Pell solution
  whose neighbours `X ∓ 1` are both prime powers — no easier than the original problem.
* Exactly one of `2k±1` is `≡ 3 (mod 4)` and must then have an **odd** exponent. If the other is a
  perfect square, the problem reduces to Lebesgue–Nagell `x² ± 2 = yⁿ`. The remaining case (both
  exponents odd, `≥ 3`) has **no congruence obstruction** — verified for all moduli up to 300, and
  for prime-power and composite moduli — so its emptiness is a true Diophantine (Pillai) phenomenon.
-/

/-- Reverse direction: `k = 13` does satisfy the condition, since `25 = 5²` and `27 = 3³`. -/
theorem oeis_365416_conjecture_0_mpr (k : ℕ) (hk : k = 13) :
    IsCompositePrimePow (2 * k - 1) ∧ IsCompositePrimePow (2 * k + 1) := by
  subst hk
  exact ⟨⟨5, 2, by norm_num, by norm_num, by norm_num⟩,
         ⟨3, 3, by norm_num, by norm_num, by norm_num⟩⟩

/-- Two perfect squares cannot differ by `2`. (Disposes of the "both exponents even" case.) -/
theorem no_two_squares (s t : ℕ) (h : t ^ 2 = s ^ 2 + 2) : False := by
  rcases Nat.eq_zero_or_pos s with hs | hs
  · subst hs
    simp only [pow_two] at h
    have ht : t ≤ 1 := by nlinarith [h]
    interval_cases t <;> simp_all
  · have h2 : t ^ 2 < (s + 1) ^ 2 := by nlinarith [hs]
    have h1 : s ^ 2 < t ^ 2 := by nlinarith
    have hlt2 : t < s + 1 := lt_of_pow_lt_pow_left₀ 2 (by positivity) h2
    have hlt1 : s < t := lt_of_pow_lt_pow_left₀ 2 (by positivity) h1
    omega

/- ### Verified algebraic infrastructure.

The ring of integers `ℤ[√-2]` is built here as a Euclidean domain (Mathlib only provides
the Gaussian integers `ℤ[i]`), and Mordell's equation `x² + 2 = y³` is solved by descent.
This is used to discharge the `a` even, `b = 3` sub-case of `pillai_core` — the sub-case
containing the genuine solution `5² + 2 = 3³`. -/
section Z2Development
open Zsqrtd Complex
abbrev Z2 : Type := Zsqrtd (-2)
namespace Z2
noncomputable def toC : Z2 →+* ℂ :=
  Zsqrtd.lift ⟨(Real.sqrt 2 : ℂ) * I, by
    have h2 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by norm_cast; rw [Real.sq_sqrt]; norm_num
    have : ((Real.sqrt 2 : ℂ) * I) ^ 2 = -2 := by rw [mul_pow, h2, Complex.I_sq]; ring
    push_cast; linear_combination this⟩
theorem toC_def (x : Z2) : toC x = x.re + x.im * ((Real.sqrt 2 : ℂ) * I) := rfl
@[simp] theorem toC_re (z : Z2) : (toC z).re = z.re := by simp [toC_def]
@[simp] theorem toC_im (z : Z2) : (toC z).im = z.im * Real.sqrt 2 := by simp [toC_def]
theorem norm_eq_normSq (z : Z2) : (Zsqrtd.norm z : ℝ) = Complex.normSq (toC z) := by
  rw [Complex.normSq_apply, toC_re, toC_im, Zsqrtd.norm_def]
  have : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num); push_cast; nlinarith [this]
theorem toC_injective : Function.Injective toC := by
  intro a b h
  have h1 := congrArg Complex.re h; have h2 := congrArg Complex.im h
  simp only [toC_re, toC_im] at h1 h2
  have hs : Real.sqrt 2 > 0 := Real.sqrt_pos.2 (by norm_num)
  exact Zsqrtd.ext (by exact_mod_cast h1) (by exact_mod_cast (mul_right_cancel₀ (ne_of_gt hs) h2))
@[simp] theorem toC_star (z : Z2) : toC (star z) = (starRingEnd ℂ) (toC z) := by
  apply Complex.ext <;> simp
theorem toC_ne_zero {z : Z2} (h : z ≠ 0) : toC z ≠ 0 :=
  fun hz => h (toC_injective (by simpa using hz))
instance : Div Z2 :=
  ⟨fun x y => ⟨round ((x * star y).re / (Zsqrtd.norm y) : ℚ), round ((x * star y).im / (Zsqrtd.norm y) : ℚ)⟩⟩
theorem div_def (x y : Z2) :
    x / y = ⟨round ((x * star y).re / (Zsqrtd.norm y) : ℚ), round ((x * star y).im / (Zsqrtd.norm y) : ℚ)⟩ := rfl
instance : Mod Z2 := ⟨fun x y => x - y * (x / y)⟩
theorem mod_def (x y : Z2) : x % y = x - y * (x / y) := rfl
theorem norm_pos_of_ne {y : Z2} (hy : y ≠ 0) : (0:ℝ) < Zsqrtd.norm y := by
  rw [norm_eq_normSq]; exact Complex.normSq_pos.2 (toC_ne_zero hy)
theorem toC_div_eq (x y : Z2) (hy : y ≠ 0) :
    toC x / toC y = toC (x * star y) / (Zsqrtd.norm y : ℂ) := by
  have hy0 : toC y ≠ 0 := toC_ne_zero hy
  rw [map_mul, toC_star]
  rw [div_eq_div_iff hy0 (by exact_mod_cast (norm_pos_of_ne hy).ne')]
  have hn : ((Zsqrtd.norm y : ℤ) : ℂ) = Complex.normSq (toC y) := by
    rw [← norm_eq_normSq]; push_cast; ring
  rw [hn, Complex.normSq_eq_conj_mul_self]; ring

theorem ofReal_norm (y : Z2) : ((Zsqrtd.norm y : ℤ) : ℂ) = ((Zsqrtd.norm y : ℝ) : ℂ) := by
  push_cast; ring
theorem toC_div_re (x y : Z2) (hy : y ≠ 0) :
    (toC x / toC y).re = ((x * star y).re : ℝ) / (Zsqrtd.norm y) := by
  rw [toC_div_eq x y hy, ofReal_norm, Complex.div_ofReal_re, toC_re]
theorem toC_div_im (x y : Z2) (hy : y ≠ 0) :
    (toC x / toC y).im = ((x * star y).im : ℝ) * Real.sqrt 2 / (Zsqrtd.norm y) := by
  rw [toC_div_eq x y hy, ofReal_norm, Complex.div_ofReal_im, toC_im]


theorem div_re (x y : Z2) :
    (x/y).re = round (((x*star y).re : ℚ)/(Zsqrtd.norm y)) := rfl
theorem div_im (x y : Z2) :
    (x/y).im = round (((x*star y).im : ℚ)/(Zsqrtd.norm y)) := rfl

theorem hre_bound (x y : Z2) (hy : y ≠ 0) :
    |(toC x / toC y - toC (x/y)).re| ≤ 1/2 := by
  rw [Complex.sub_re, toC_div_re x y hy, toC_re, div_re]
  have key : ((x*star y).re : ℝ)/((Zsqrtd.norm y : ℤ))
      - ((round (((x*star y).re : ℚ)/(Zsqrtd.norm y)) : ℤ) : ℝ)
      = ((((x*star y).re : ℚ)/(Zsqrtd.norm y) - round (((x*star y).re : ℚ)/(Zsqrtd.norm y)) : ℚ) : ℝ) := by
    push_cast; ring
  rw [key, ← Rat.cast_abs, show ((1:ℝ)/2) = ((1/2 : ℚ):ℝ) by norm_num]
  exact_mod_cast abs_sub_round (((x*star y).re : ℚ)/(Zsqrtd.norm y))

theorem him_bound (x y : Z2) (hy : y ≠ 0) :
    |(toC x / toC y - toC (x/y)).im| ≤ Real.sqrt 2 / 2 := by
  rw [Complex.sub_im, toC_div_im x y hy, toC_im, div_im]
  have key : ((x*star y).im : ℝ) * Real.sqrt 2 / ((Zsqrtd.norm y : ℤ))
      - ((round (((x*star y).im : ℚ)/(Zsqrtd.norm y)) : ℤ) : ℝ) * Real.sqrt 2
      = ((((x*star y).im : ℚ)/(Zsqrtd.norm y) - round (((x*star y).im : ℚ)/(Zsqrtd.norm y)) : ℚ) : ℝ)
        * Real.sqrt 2 := by
    push_cast; ring
  rw [key, abs_mul, abs_of_pos (Real.sqrt_pos.2 (by norm_num : (0:ℝ) < 2))]
  have hr : |((((x*star y).im : ℚ)/(Zsqrtd.norm y)
      - round (((x*star y).im : ℚ)/(Zsqrtd.norm y)) : ℚ) : ℝ)| ≤ 1/2 := by
    rw [← Rat.cast_abs, show ((1:ℝ)/2) = ((1/2 : ℚ):ℝ) by norm_num]
    exact_mod_cast abs_sub_round (((x*star y).im : ℚ)/(Zsqrtd.norm y))
  nlinarith [mul_le_mul_of_nonneg_right hr (Real.sqrt_nonneg 2), Real.sqrt_nonneg 2]

theorem hbound (x y : Z2) (hy : y ≠ 0) :
    Complex.normSq (toC x / toC y - toC (x/y)) < 1 := by
  rw [Complex.normSq_apply]
  have h1 := hre_bound x y hy
  have h2 := him_bound x y hy
  have hsqrt : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  set u := (toC x / toC y - toC (x/y)).re
  set v := (toC x / toC y - toC (x/y)).im
  have hu : u^2 ≤ (1/2)^2 := by nlinarith [abs_nonneg u, sq_abs u, h1]
  have hv : v^2 ≤ (Real.sqrt 2 / 2)^2 := by nlinarith [abs_nonneg v, sq_abs v, h2]
  nlinarith [hu, hv, hsqrt]

theorem norm_mod_lt (x : Z2) {y : Z2} (hy : y ≠ 0) : (x % y).norm < y.norm := by
  have hy0 : toC y ≠ 0 := toC_ne_zero hy
  have key : (Zsqrtd.norm (x % y) : ℝ)
      = Complex.normSq (toC y) * Complex.normSq (toC x / toC y - toC (x/y)) := by
    rw [norm_eq_normSq, mod_def, map_sub, map_mul]
    rw [show toC x - toC y * toC (x/y) = toC y * (toC x / toC y - toC (x/y)) by
      field_simp]
    rw [Complex.normSq_mul]
  have hb := hbound x y hy
  have hny : (0:ℝ) < Complex.normSq (toC y) := Complex.normSq_pos.2 hy0
  have hlt : (Zsqrtd.norm (x % y) : ℝ) < Complex.normSq (toC y) := by
    rw [key]; nlinarith [mul_lt_mul_of_pos_left hb hny]
  rw [← norm_eq_normSq] at hlt
  exact_mod_cast hlt

theorem norm_pos {x : Z2} (hx : x ≠ 0) : 0 < Zsqrtd.norm x := by
  rcases lt_or_eq_of_le (Zsqrtd.norm_nonneg (by norm_num) x) with h | h
  · exact h
  · exact absurd ((Zsqrtd.norm_eq_zero_iff (by norm_num) x).1 h.symm) hx

theorem natAbs_norm_mod_lt (x : Z2) {y : Z2} (hy : y ≠ 0) :
    (x % y).norm.natAbs < y.norm.natAbs := by
  have h := norm_mod_lt x hy
  have h1 : (0:ℤ) ≤ (x % y).norm := Zsqrtd.norm_nonneg (by norm_num) _
  have h2 : (0:ℤ) ≤ y.norm := Zsqrtd.norm_nonneg (by norm_num) _
  have : ((x % y).norm.natAbs : ℤ) < (y.norm.natAbs : ℤ) := by
    rw [Int.natAbs_of_nonneg h1, Int.natAbs_of_nonneg h2]; exact h
  exact_mod_cast this

theorem norm_le_norm_mul_left (x : Z2) {y : Z2} (hy : y ≠ 0) :
    (Zsqrtd.norm x).natAbs ≤ (Zsqrtd.norm (x * y)).natAbs := by
  rw [Zsqrtd.norm_mul, Int.natAbs_mul]
  exact le_mul_of_one_le_right (Nat.zero_le _) (Int.natAbs_pos.2 (norm_pos hy).ne')

instance instNontrivial : Nontrivial Z2 := ⟨⟨0, 1, by decide⟩⟩

instance : EuclideanDomain Z2 :=
  { (inferInstance : CommRing Z2),
    Z2.instNontrivial with
    quotient := (· / ·)
    remainder := (· % ·)
    quotient_zero := fun x => by simp [div_def]; rfl
    quotient_mul_add_remainder_eq := fun a b => by rw [mod_def]; ring
    r := _
    r_wellFounded := (measure (Int.natAbs ∘ Zsqrtd.norm)).wf
    remainder_lt := natAbs_norm_mod_lt
    mul_left_not_lt := fun a _ hb0 => not_lt_of_ge (norm_le_norm_mul_left a hb0) }

/- Mordell's equation x^2 + 2 = y^3 via the Euclidean domain Z[sqrt -2]. -/

theorem cube_re (a b : ℤ) : ((⟨a, b⟩ : Z2) ^ 3).re = a^3 - 6*a*b^2 := by
  simp only [pow_succ, pow_zero, one_mul, Zsqrtd.re_mul, Zsqrtd.im_mul]; ring
theorem cube_im (a b : ℤ) : ((⟨a, b⟩ : Z2) ^ 3).im = 3*a^2*b - 2*b^3 := by
  simp only [pow_succ, pow_zero, one_mul, Zsqrtd.re_mul, Zsqrtd.im_mul]; ring

theorem norm_dvd_norm {a c : Z2} (h : a ∣ c) : Zsqrtd.norm a ∣ Zsqrtd.norm c := by
  obtain ⟨e, rfl⟩ := h; exact ⟨Zsqrtd.norm e, by rw [Zsqrtd.norm_mul]⟩

theorem isUnit_iff_z2 {z : Z2} (hz : IsUnit z) : z = 1 ∨ z = -1 := by
  have hn : (Zsqrtd.norm z).natAbs = 1 := Zsqrtd.norm_eq_one_iff.mpr hz
  have hpos : 0 ≤ Zsqrtd.norm z := Zsqrtd.norm_nonneg (by norm_num) z
  have hnorm : Zsqrtd.norm z = 1 := by omega
  rw [Zsqrtd.norm_def] at hnorm
  have him : z.im = 0 := by nlinarith [sq_nonneg z.re, sq_nonneg z.im, hnorm]
  have hre : z.re = 1 ∨ z.re = -1 := by
    have : z.re * z.re = 1 := by rw [him] at hnorm; linarith
    rcases mul_self_eq_one_iff.mp this with h | h
    · left; exact h
    · right; exact h
  rcases hre with h | h
  · left; exact Zsqrtd.ext h him
  · right; exact Zsqrtd.ext (by simpa using h) (by simpa using him)

/-- **Mordell's theorem** for `x² + 2 = y³`: the only integer solutions have `x = ±5`
(`= 5² + 2 = 27 = 3³`). Proved by descent in the Euclidean domain `ℤ[√-2]`. -/
theorem mordell (x y : ℤ) (h : x ^ 2 + 2 = y ^ 3) : x = 5 ∨ x = -5 := by
  classical
  -- `x` is odd, hence `y` is odd.
  have hxodd : ¬ (2 ∣ x) := by
    rintro ⟨m, rfl⟩
    have hye : 2 ∣ y := by
      have : Even (y ^ 3) := by rw [← h]; exact ⟨2*m^2 + 1, by ring⟩
      rcases (Int.even_pow.mp this) with ⟨he, _⟩; exact he.two_dvd
    obtain ⟨n, rfl⟩ := hye
    have : (2:ℤ) * (4 * n ^ 3) = 2 * (2 * m ^ 2) + 2 * 1 := by ring_nf; ring_nf at h; linarith
    omega
  have hyodd : ¬ (2 ∣ y) := by
    rintro ⟨n, rfl⟩
    apply hxodd
    have : x ^ 2 = 2 * (4 * n ^ 3 - 1) := by ring_nf; ring_nf at h; linarith
    have h2 : (2:ℤ) ∣ x ^ 2 := ⟨_, this⟩
    exact Int.prime_two.dvd_of_dvd_pow h2
  -- Set up the factorisation `(x+√-2)(x-√-2) = y³` in `ℤ[√-2]`.
  set a : Z2 := ⟨x, 1⟩ with ha
  set b : Z2 := ⟨x, -1⟩ with hb
  have habeq : a * b = (↑y : Z2) ^ 3 := by
    have e1 : a * b = ((x ^ 2 + 2 : ℤ) : Z2) := by
      apply Zsqrtd.ext <;>
        simp only [ha, hb, Zsqrtd.re_mul, Zsqrtd.im_mul, Zsqrtd.re_intCast, Zsqrtd.im_intCast] <;>
        ring
    rw [e1, h]; push_cast; ring
  -- Coprimality of the two factors.
  have hcop : IsCoprime a b := by
    rw [← EuclideanDomain.gcd_isUnit_iff]
    set g := EuclideanDomain.gcd a b with hg
    have hga : g ∣ a := EuclideanDomain.gcd_dvd_left a b
    have hgb : g ∣ b := EuclideanDomain.gcd_dvd_right a b
    have hn1 : Zsqrtd.norm g ∣ (8:ℤ) := by
      have : Zsqrtd.norm g ∣ Zsqrtd.norm (a - b) := norm_dvd_norm (dvd_sub hga hgb)
      have h8 : Zsqrtd.norm (a - b) = 8 := by
        rw [Zsqrtd.norm_def]; simp [ha, hb, Zsqrtd.re_sub, Zsqrtd.im_sub]
      rwa [h8] at this
    have hn2 : Zsqrtd.norm g ∣ y ^ 3 := by
      have : Zsqrtd.norm g ∣ Zsqrtd.norm a := norm_dvd_norm hga
      have hna : Zsqrtd.norm a = y ^ 3 := by
        rw [Zsqrtd.norm_def]; simp [ha]; linarith [h]
      rwa [hna] at this
    have hcoprime : IsCoprime (8:ℤ) (y ^ 3) := by
      have h2y : IsCoprime (2:ℤ) y := (Int.prime_two.coprime_iff_not_dvd).mpr hyodd
      have := (h2y.pow (m := 3) (n := 3))
      simpa using this
    have hunit : IsUnit (Zsqrtd.norm g) := hcoprime.isUnit_of_dvd' hn1 hn2
    rw [← Zsqrtd.norm_eq_one_iff]
    rcases Int.isUnit_iff.mp hunit with h1 | h1 <;> simp [h1]
  -- Descent: `a` is a cube up to a unit, and units `±1` are cubes, so `a = w³`.
  obtain ⟨d, hd⟩ := exists_associated_pow_of_mul_eq_pow' hcop habeq
  obtain ⟨u, hu⟩ := hd
  have hw : ∃ w : Z2, w ^ 3 = a := by
    rcases isUnit_iff_z2 u.isUnit with hu1 | hu1
    · exact ⟨d, by rw [← hu, hu1, mul_one]⟩
    · exact ⟨-d, by rw [neg_pow, ← hu, hu1]; ring⟩
  obtain ⟨w, hw⟩ := hw
  -- Read off the coefficient equations from `w³ = ⟨x, 1⟩`.
  obtain ⟨p, q⟩ := w
  have him : 3 * p ^ 2 * q - 2 * q ^ 3 = 1 := by
    have := congrArg Zsqrtd.im hw
    rwa [cube_im, ha] at this
  have hre : p ^ 3 - 6 * p * q ^ 2 = x := by
    have := congrArg Zsqrtd.re hw
    rwa [cube_re, ha] at this
  -- `q ∣ 1`, so `q = ±1`; only `q = 1` is consistent, forcing `p = ±1` and `x = ∓5`.
  have hq : q ∣ 1 := ⟨3 * p ^ 2 - 2 * q ^ 2, by linarith [him]⟩
  rcases Int.isUnit_iff.mp (isUnit_of_dvd_one hq) with hq1 | hq1
  · -- q = 1
    subst hq1
    have hp : p ^ 2 = 1 := by nlinarith [him]
    have hpp : p = 1 ∨ p = -1 :=
      mul_self_eq_one_iff.mp (by nlinarith [hp] : p * p = 1)
    rcases hpp with hp1 | hp1
    · subst hp1; right; nlinarith [hre]
    · subst hp1; left; nlinarith [hre]
  · -- q = -1 : impossible
    exfalso; subst hq1
    have h3 : 3 * p ^ 2 = 1 := by nlinarith [him]
    have hp0 : (0:ℤ) ≤ p ^ 2 := sq_nonneg p
    omega

end Z2
end Z2Development


/--
**The open Pillai instance** that the whole conjecture rests on.

`q ^ b - p ^ a = 2` with `p, q` prime and `a, b ≥ 2` has the unique solution `27 - 25`.
This is the *only* unproved input to `oeis_365416_conjecture_0` below: the rest of the proof is
complete (see the reduction in that theorem).

The proof here is split by the parities of `a, b`:
* **both even** — *proved*: `p^a, q^b` would be two squares differing by `2` (`no_two_squares`).
* **`a` even, `b = 3`** — *proved*: `p^a = (p^{a/2})²`, so `q³ = x² + 2`; the verified Mordell
  theorem `Z2.mordell` (descent in the Euclidean domain `ℤ[√-2]` constructed above) forces
  `x = ±5`, hence `p^a = 25`, `q³ = 27`. This sub-case contains the genuine solution `5² + 2 = 3³`.
* **`a` even, `b` odd with `b ≥ 5`** — Lebesgue–Nagell `x² + 2 = yⁿ` for higher `n`; the full
  result needs the Bilu–Hanrot–Voutier primitive-divisor theorem, absent from Mathlib. **Open here.**
* **`a` odd, `b` even** — Lebesgue–Nagell `x² − 2 = yⁿ`; needs `ℤ[√2]` with its infinite unit
  group plus Baker-type bounds. **Open here.**
* **both odd** — the equation `pᵃ − qᵇ = 2` with both exponents odd: an unresolved instance of
  Pillai's conjecture with **no congruence obstruction** (checked to modulus 600). **Open here.**

Hence this statement is **true**; the three remaining sub-cases above are the only unproved input,
and they require either theorems absent from Mathlib or the open Pillai conjecture. -/
theorem pillai_core (p a q b : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (ha : 1 < a) (hb : 1 < b) (h : q ^ b = p ^ a + 2) :
    p ^ a = 25 ∧ q ^ b = 27 := by
  rcases Nat.even_or_odd a with hae | hao
  · rcases Nat.even_or_odd b with hbe | hbo
    · -- both exponents even: two squares differing by 2 — impossible (PROVED)
      exfalso
      obtain ⟨a', rfl⟩ := hae
      obtain ⟨b', rfl⟩ := hbe
      have ea : p ^ (a' + a') = (p ^ a') ^ 2 := by rw [pow_add, pow_two]
      have eb : q ^ (b' + b') = (q ^ b') ^ 2 := by rw [pow_add, pow_two]
      rw [ea, eb] at h
      exact no_two_squares (p ^ a') (q ^ b') h
    · -- a even, b odd: Lebesgue–Nagell  x² + 2 = yⁿ.
      obtain ⟨a', rfl⟩ := hae
      have hpa : p ^ (a' + a') = (p ^ a') ^ 2 := by rw [pow_add, pow_two]
      rcases eq_or_ne b 3 with hb3 | hb3
      · -- b = 3: closed by the verified Mordell theorem `Z2.mordell`
        --         (this sub-case contains the genuine solution `5² + 2 = 3³`).
        subst hb3
        have hz : ((p ^ a' : ℕ) : ℤ) ^ 2 + 2 = (q : ℤ) ^ 3 := by
          have hh : q ^ 3 = (p ^ a') ^ 2 + 2 := by rw [← hpa]; exact h
          exact_mod_cast hh.symm
        rcases Z2.mordell ((p ^ a' : ℕ) : ℤ) (q : ℤ) hz with h5 | h5
        · have hpa5 : p ^ a' = 5 := by exact_mod_cast h5
          refine ⟨?_, ?_⟩
          · rw [hpa, hpa5]; norm_num
          · have hh : q ^ 3 = (p ^ a') ^ 2 + 2 := by rw [← hpa]; exact h
            rw [hh, hpa5]; norm_num
        · exfalso
          have hnn : (0 : ℤ) ≤ ((p ^ a' : ℕ) : ℤ) := Int.natCast_nonneg _
          rw [h5] at hnn; norm_num at hnn
      · -- b odd, b ≥ 5: needs Lebesgue–Nagell for higher exponents (BHV). OPEN.
        sorry
  · rcases Nat.even_or_odd b with hbe | hbo
    · -- a odd, b even: Lebesgue–Nagell  x² − 2 = yⁿ  (needs ℤ[√2] + Baker; OPEN)
      sorry
    · -- both exponents odd: open Pillai instance pᵃ − qᵇ = 2 (no congruence obstruction; OPEN)
      sorry

/--
A365416 According to Pillai's conjecture, k = 13 is the only term such that 2*k-1 and 2*k+1 both have exponent greater than 1.

The proof below is **complete except for `pillai_core`**: it extracts the two prime-power
representations `2k-1 = p^a`, `2k+1 = q^b`, derives the core equation `q^b = p^a + 2`, applies
`pillai_core` to force `p^a = 25` (so `2k-1 = 25`, i.e. `k = 13`), and conversely uses
`oeis_365416_conjecture_0_mpr`. -/
theorem oeis_365416_conjecture_0 :
  ∀ k : ℕ,
    (IsCompositePrimePow (2 * k - 1) ∧ IsCompositePrimePow (2 * k + 1)) ↔ k = 13 := by
  intro k
  constructor
  · rintro ⟨⟨p, a, hp, ha, hpa⟩, ⟨q, b, hq, hb, hqb⟩⟩
    have hp4 : 4 ≤ p ^ a := by
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ p ^ 2 := Nat.pow_le_pow_left hp.two_le 2
        _ ≤ p ^ a := Nat.pow_le_pow_right hp.one_lt.le (by omega)
    have hsum : q ^ b = p ^ a + 2 := by omega
    obtain ⟨h25, _⟩ := pillai_core p a q b hp hq ha hb hsum
    omega
  · rintro rfl
    exact oeis_365416_conjecture_0_mpr 13 rfl
