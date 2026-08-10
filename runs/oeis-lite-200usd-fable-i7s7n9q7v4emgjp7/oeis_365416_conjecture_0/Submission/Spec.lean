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

/-
### Reduction of the conjecture

The conjecture states that the only pair of composite prime powers differing by 2 is
`(25, 27)`.  Writing `2k - 1 = q ^ b` and `2k + 1 = p ^ a` with `p, q` (odd) primes and
`a, b ≥ 2`, and splitting according to the parities of the exponents `a, b`, the statement
reduces to the following irreducible Diophantine statements:

1. `x² + 2 = yⁿ` (odd `n ≥ 3`) has only the solution `5² + 2 = 3³`.  This is a classical
   theorem going back to Fermat and Nagell (the Lebesgue–Nagell equation with `D = 2`).
   It is proved *completely, from scratch* below (`nagell_sq_add_two`): after factoring in
   the Euclidean domain `ℤ[√-2]` it reduces to `Im((c + √-2)ⁿ) = ±1` for odd `c`, which is
   settled by an elementary argument combining behaviour mod 8, a lifting-the-exponent
   step for the 2-adic valuation, and a Pell-equation descent.

2. `x² - 2 = yʳ` (odd prime `r`) has no solutions with `y ≥ 2`.  This is an **open
   problem** (the Lebesgue–Ramanujan–Nagell equation with negative `D`, beyond current
   techniques because of the infinite unit group of `ℤ[√2]`); stated as
   `no_sq_sub_two_pow_prime` with `sorry`.

3. `xʳ - yˢ = 2` with distinct odd primes `r, s` has no solutions with `x, y ≥ 2`.  This
   is an **open case of Pillai's conjecture**; stated as
   `no_pow_sub_two_pow_distinct_odd_primes` with `sorry`.

All remaining bookkeeping (the parity case analysis, the impossibility of two squares or
two equal prime-exponent powers differing by 2, and the reduction of composite exponents
to prime exponents) is proved completely below without `sorry`.
-/

/-
### The ring `ℤ[√-2]` and the Fermat–Nagell theorem
-/

section ZsqrtNeg2

open Zsqrtd

local notation "ℤ√₋₂" => Zsqrtd (-2)

namespace Zneg2

theorem norm_def' (x : ℤ√₋₂) : x.norm = x.re ^ 2 + 2 * x.im ^ 2 := by
  rw [Zsqrtd.norm_def]; ring

theorem norm_nonneg' (x : ℤ√₋₂) : 0 ≤ x.norm :=
  Zsqrtd.norm_nonneg (by norm_num) x

theorem norm_eq_zero' {x : ℤ√₋₂} : x.norm = 0 ↔ x = 0 :=
  Zsqrtd.norm_eq_zero_iff (by norm_num) x

theorem norm_pos' {x : ℤ√₋₂} (hx : x ≠ 0) : 0 < x.norm :=
  lt_of_le_of_ne (norm_nonneg' x) (fun h => hx (norm_eq_zero'.mp h.symm))

noncomputable instance : Div ℤ√₋₂ :=
  ⟨fun x y =>
    ⟨round (((x * star y).re : ℚ) / (y.norm : ℚ)),
     round (((x * star y).im : ℚ) / (y.norm : ℚ))⟩⟩

theorem div_def (x y : ℤ√₋₂) :
    x / y = ⟨round (((x * star y).re : ℚ) / (y.norm : ℚ)),
             round (((x * star y).im : ℚ) / (y.norm : ℚ))⟩ := rfl

noncomputable instance : Mod ℤ√₋₂ :=
  ⟨fun x y => x - y * (x / y)⟩

theorem mod_def (x y : ℤ√₋₂) : x % y = x - y * (x / y) := rfl

/-- Key rounding estimate: `(2(a - round(a/n) n))² ≤ n²` for `n ≠ 0`. -/
theorem sq_le_of_round (a n : ℤ) (hn : n ≠ 0) :
    (2 * (a - round ((a : ℚ) / (n : ℚ)) * n)) ^ 2 ≤ n ^ 2 := by
  have hnQ : (n : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hn
  have h1 : |(a : ℚ) / (n : ℚ) - round ((a : ℚ) / (n : ℚ))| ≤ 1 / 2 := abs_sub_round _
  have h2 : |(a : ℚ) - round ((a : ℚ) / (n : ℚ)) * (n : ℚ)| ≤ |(n : ℚ)| / 2 := by
    have h3 : (a : ℚ) - round ((a : ℚ) / (n : ℚ)) * (n : ℚ)
        = ((a : ℚ) / (n : ℚ) - round ((a : ℚ) / (n : ℚ))) * (n : ℚ) := by
      field_simp
    rw [h3, abs_mul]
    calc |(a : ℚ) / (n : ℚ) - round ((a : ℚ) / (n : ℚ))| * |(n : ℚ)|
        ≤ (1 / 2) * |(n : ℚ)| := by
          exact mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
      _ = |(n : ℚ)| / 2 := by ring
  -- square the inequality
  have h4 : ((a : ℚ) - round ((a : ℚ) / (n : ℚ)) * (n : ℚ)) ^ 2 ≤ ((n : ℚ) / 2) ^ 2 := by
    obtain ⟨hl, hr⟩ := abs_le.mp h2
    have hs : ((n : ℚ) / 2) ^ 2 = (|(n : ℚ)| / 2) ^ 2 := by
      rw [div_pow, div_pow, sq_abs]
    rw [hs]
    nlinarith [abs_nonneg (n : ℚ)]
  -- conclude over ℤ
  have h6 : ((2 * (a - round ((a : ℚ) / (n : ℚ)) * n) : ℤ) : ℚ) ^ 2 ≤ ((n : ℤ) : ℚ) ^ 2 := by
    push_cast
    nlinarith [h4]
  exact_mod_cast h6

/-- The crucial division estimate: `norm (x % y) < norm y`. -/
theorem norm_mod_lt' (x : ℤ√₋₂) {y : ℤ√₋₂} (hy : y ≠ 0) : (x % y).norm < y.norm := by
  set n := y.norm with hn
  have hn0 : 0 < n := norm_pos' hy
  set a := (x * star y).re with ha
  set b := (x * star y).im with hb
  set q := x / y with hq
  -- (x - y*q) * star y = ⟨a - q.re * n, b - q.im * n⟩
  have key : (x % y) * star y = ⟨a - q.re * n, b - q.im * n⟩ := by
    rw [mod_def]
    have h1 : (x - y * q) * star y = x * star y - q * (y * star y) := by ring
    have h2 : y * star y = (n : ℤ√₋₂) := by
      rw [hn, ← Zsqrtd.norm_eq_mul_conj]
    rw [h1, h2]
    have h3 : q * ((n : ℤ) : ℤ√₋₂) = ⟨n * q.re, n * q.im⟩ := by
      rw [mul_comm]
      exact Zsqrtd.smul_val n q.re q.im
    rw [h3, ha, hb]
    ext
    · simp [Zsqrtd.re_sub]
      ring
    · simp [Zsqrtd.im_sub]
      ring
  -- take norms
  have hnorm : (x % y).norm * n = (a - q.re * n) ^ 2 + 2 * (b - q.im * n) ^ 2 := by
    have := congrArg Zsqrtd.norm key
    rw [Zsqrtd.norm_mul] at this
    have hsy : (star y).norm = n := by
      rw [hn]
      simp [norm_def']
    rw [hsy] at this
    rw [this, norm_def']
  -- the estimates
  have e1 : (2 * (a - q.re * n)) ^ 2 ≤ n ^ 2 := by
    have : q.re = round ((a : ℚ) / (n : ℚ)) := by rw [hq, div_def]
    rw [this]
    exact sq_le_of_round a n (ne_of_gt hn0)
  have e2 : (2 * (b - q.im * n)) ^ 2 ≤ n ^ 2 := by
    have : q.im = round ((b : ℚ) / (n : ℚ)) := by rw [hq, div_def]
    rw [this]
    exact sq_le_of_round b n (ne_of_gt hn0)
  -- combine : 4 * (norm(x%y) * n) ≤ 3 n² < 4 n²
  nlinarith [hnorm, e1, e2, hn0]

theorem natAbs_norm_mod_lt' (x : ℤ√₋₂) {y : ℤ√₋₂} (hy : y ≠ 0) :
    (x % y).norm.natAbs < y.norm.natAbs := by
  have h := norm_mod_lt' x hy
  have h1 := norm_nonneg' (x % y)
  have h2 := norm_nonneg' y
  omega

theorem norm_le_norm_mul_left' (x : ℤ√₋₂) {y : ℤ√₋₂} (hy : y ≠ 0) :
    (Zsqrtd.norm x).natAbs ≤ (Zsqrtd.norm (x * y)).natAbs := by
  rw [Zsqrtd.norm_mul, Int.natAbs_mul]
  have h2 : 1 ≤ y.norm.natAbs := by
    have := norm_pos' hy
    omega
  exact Nat.le_mul_of_pos_right _ (by omega)

instance : Nontrivial ℤ√₋₂ :=
  ⟨⟨0, 1, by
    intro h
    have := congrArg Zsqrtd.re h
    simp at this⟩⟩

noncomputable instance euclideanDomain : EuclideanDomain ℤ√₋₂ :=
  { (inferInstance : CommRing ℤ√₋₂), (inferInstance : Nontrivial ℤ√₋₂) with
    quotient := (· / ·)
    remainder := (· % ·)
    quotient_zero := fun x => by
      rw [div_def]
      ext <;> simp
    quotient_mul_add_remainder_eq := fun x y => by rw [mod_def]; ring
    r := fun a b => a.norm.natAbs < b.norm.natAbs
    r_wellFounded := (measure fun x : ℤ√₋₂ => x.norm.natAbs).wf
    remainder_lt := fun a b hb => natAbs_norm_mod_lt' a hb
    mul_left_not_lt := fun a b hb0 => not_lt_of_ge (norm_le_norm_mul_left' a hb0) }

/-- The units of `ℤ√-2` are `±1`. -/
theorem isUnit_iff {u : ℤ√₋₂} : IsUnit u ↔ u = 1 ∨ u = -1 := by
  constructor
  · intro h
    have h1 : u.norm.natAbs = 1 := (Zsqrtd.norm_eq_one_iff).mpr h
    have h2 : u.norm = 1 := by
      have := norm_nonneg' u
      omega
    rw [norm_def'] at h2
    have him2 : u.im ^ 2 = 0 := by nlinarith [sq_nonneg u.re, sq_nonneg u.im]
    have him : u.im = 0 := pow_eq_zero_iff (n := 2) (by omega) |>.mp him2
    have hre2 : u.re ^ 2 = 1 := by rw [him] at h2; linarith
    have hre : (u.re - 1) * (u.re + 1) = 0 := by ring_nf; linarith [hre2]
    rcases mul_eq_zero.mp hre with h | h
    · left; ext <;> simp [him] <;> omega
    · right; ext <;> simp [him] <;> omega
  · rintro (rfl | rfl)
    · exact isUnit_one
    · exact IsUnit.neg isUnit_one

theorem intCast_mk (k : ℤ) : ((k : ℤ) : ℤ√₋₂) = ⟨k, 0⟩ := by
  ext <;> simp

/-- `im γ` divides `im (γ ^ k)`. -/
theorem im_dvd_im_pow (γ : ℤ√₋₂) (k : ℕ) : γ.im ∣ (γ ^ k).im := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Zsqrtd.im_mul]
    exact dvd_add (Dvd.dvd.mul_left dvd_rfl _) (ih.mul_right _)

/-- Powers with the same odd exponent and nonneg bases are injective. -/
theorem pow_inj_of_nonneg {a b : ℤ} {n : ℕ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hn : n ≠ 0)
    (h : a ^ n = b ^ n) : a = b := by
  rcases lt_trichotomy a b with hlt | heq | hgt
  · exfalso
    have := pow_lt_pow_left₀ hlt ha hn
    omega
  · exact heq
  · exfalso
    have := pow_lt_pow_left₀ hgt hb hn
    omega

/-- Main factorization: if `x² + 2 = yⁿ` with `n` odd, `n ≥ 3`, then
`y = c² + 2` for some odd `c` with `Im((c + √-2)ⁿ) = 1`. -/
theorem exists_c (x y : ℤ) (n : ℕ) (hn : Odd n) (h3 : 3 ≤ n)
    (h : x ^ 2 + 2 = y ^ n) : ∃ c : ℤ, Odd c ∧ y = c ^ 2 + 2 ∧
      (((⟨c, 1⟩ : ℤ√₋₂) ^ n).im = 1 ∨ ((⟨c, 1⟩ : ℤ√₋₂) ^ n).im = -1) := by
  have hn0 : n ≠ 0 := by omega
  -- x is odd
  have hxodd : Odd x := by
    by_contra hx
    rw [Int.not_odd_iff_even] at hx
    obtain ⟨t, ht⟩ := hx
    have hyeven : Even y := by
      by_contra hy
      rw [Int.not_even_iff_odd] at hy
      have h1 : Odd (y ^ n) := hy.pow
      rw [← h] at h1
      have h2 : Even (x ^ 2 + 2) := by
        subst ht
        exact ⟨2 * t ^ 2 + 1, by ring⟩
      exact (Int.not_even_iff_odd.mpr h1) h2
    obtain ⟨s, hs⟩ := hyeven
    have h4 : (4 : ℤ) ∣ y ^ n := by
      have : y ^ n = (s + s) ^ n := by rw [hs]
      rw [this]
      have h5 : (s + s) ^ n = 2 ^ n * s ^ n := by
        rw [← two_mul, mul_pow]
      rw [h5]
      have h6 : (4 : ℤ) ∣ 2 ^ n := by
        have : (2:ℤ) ^ 2 ∣ 2 ^ n := pow_dvd_pow 2 (by omega)
        norm_num at this
        exact this
      exact h6.mul_right _
    rw [← h, ht] at h4
    obtain ⟨w, hw⟩ := h4
    have h5 : 2 * t ^ 2 + 1 = 2 * w := by nlinarith [hw]
    omega
  -- y is odd and positive
  have hyn_odd : Odd (y ^ n) := by
    rw [← h]
    rcases hxodd with ⟨t, ht⟩
    refine ⟨2*t^2 + 2*t + 1, by subst ht; ring⟩
  have hyodd : Odd y := by
    by_contra hy
    rw [Int.not_odd_iff_even] at hy
    have h1 : Even (y ^ n) := Int.even_pow.mpr ⟨hy, hn0⟩
    exact (Int.not_even_iff_odd.mpr hyn_odd) h1
  have hypos : 0 < y := by
    by_contra hy
    push_neg at hy
    have h1 : y ^ n ≤ 0 := Odd.pow_nonpos hn hy
    have h2 : (0:ℤ) < x ^ 2 + 2 := by positivity
    rw [h] at h2
    linarith
  -- the factorization in ℤ√-2
  set α : ℤ√₋₂ := ⟨x, 1⟩ with hα
  set β : ℤ√₋₂ := ⟨x, -1⟩ with hβ
  have hmul : α * β = ((y : ℤ√₋₂)) ^ n := by
    have h1 : α * β = ((x ^ 2 + 2 : ℤ) : ℤ√₋₂) := by
      rw [intCast_mk]
      ext
      · simp [hα, hβ, Zsqrtd.re_mul]
        ring
      · simp [hα, hβ, Zsqrtd.im_mul]
    rw [h1, h]
    push_cast
    rfl
  -- coprimality
  have hcop : IsCoprime α β := by
    -- Bezout in ℤ : u (x²+2) + v 8 = 1
    have hodd : Odd (x ^ 2 + 2) := by
      rcases hxodd with ⟨t, ht⟩
      exact ⟨2*t^2 + 2*t + 1, by subst ht; ring⟩
    have hcopz : IsCoprime (x ^ 2 + 2 : ℤ) (8 : ℤ) := by
      have h2 : IsCoprime (x ^ 2 + 2 : ℤ) (2 : ℤ) := by
        rcases hodd with ⟨t, ht⟩
        exact ⟨1, -t, by rw [ht]; ring⟩
      have h8 : (8 : ℤ) = 2 ^ 3 := by norm_num
      rw [h8]
      exact h2.pow_right
    obtain ⟨u, v, huv⟩ := hcopz
    -- lift to ℤ√-2 : 8 = -(α - β)², x²+2 = αβ
    have hd : α - β = ⟨0, 2⟩ := by
      ext <;> simp [hα, hβ]
    have h8R : ((8 : ℤ) : ℤ√₋₂) = -(α - β) ^ 2 := by
      rw [hd, intCast_mk]
      ext
      · simp [Zsqrtd.re_mul, pow_two]
      · simp [Zsqrtd.im_mul, pow_two]
    have hYR : ((x ^ 2 + 2 : ℤ) : ℤ√₋₂) = α * β := by
      rw [intCast_mk]
      ext
      · simp [hα, hβ, Zsqrtd.re_mul]
        ring
      · simp [hα, hβ, Zsqrtd.im_mul]
    refine ⟨(u : ℤ√₋₂) * β - (v : ℤ√₋₂) * (α - β), (v : ℤ√₋₂) * (α - β), ?_⟩
    have hcast : ((u : ℤ) : ℤ√₋₂) * ((x^2+2 : ℤ) : ℤ√₋₂) + ((v : ℤ) : ℤ√₋₂) * ((8:ℤ) : ℤ√₋₂)
        = ((1 : ℤ) : ℤ√₋₂) := by
      rw [← Int.cast_mul, ← Int.cast_mul, ← Int.cast_add, huv]
    rw [hYR, h8R] at hcast
    push_cast at hcast ⊢
    linear_combination hcast
  -- extract the n-th power
  obtain ⟨δ, hδ⟩ := exists_associated_pow_of_mul_eq_pow' hcop hmul
  obtain ⟨w, hw⟩ := hδ
  -- α = δ^n · w with w = ±1 ; absorb the sign (n odd)
  have hγ : ∃ γ : ℤ√₋₂, γ ^ n = α := by
    rcases isUnit_iff.mp w.isUnit with h1 | h1
    · refine ⟨δ, ?_⟩
      have h2 : (w : ℤ√₋₂) = 1 := by rw [h1]
      rw [← hw, h2, mul_one]
    · refine ⟨-δ, ?_⟩
      have hne : (-δ) ^ n = -(δ ^ n) := Odd.neg_pow hn δ
      have h2 : (w : ℤ√₋₂) = -1 := by rw [h1]
      rw [hne, ← hw, h2]
      ring
  obtain ⟨γ, hγn⟩ := hγ
  -- γ.im = ±1
  have him : γ.im ∣ 1 := by
    have h1 := im_dvd_im_pow γ n
    rw [hγn] at h1
    simpa [hα] using h1
  have him1 : γ.im = 1 ∨ γ.im = -1 := by
    rcases Int.isUnit_iff.mp (isUnit_of_dvd_one him) with h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
  -- produce c with Im((c + √-2)ⁿ) = ±1
  have hc : ∃ c : ℤ, ((⟨c, 1⟩ : ℤ√₋₂) ^ n) = (⟨x, 1⟩ : ℤ√₋₂) ∨
      ((⟨c, 1⟩ : ℤ√₋₂) ^ n) = (⟨x, -1⟩ : ℤ√₋₂) := by
    rcases him1 with h1 | h1
    · refine ⟨γ.re, Or.inl ?_⟩
      have h2 : γ = (⟨γ.re, 1⟩ : ℤ√₋₂) := by ext <;> simp [h1]
      rw [← h2, hγn, hα]
    · refine ⟨γ.re, Or.inr ?_⟩
      have hsγ : (⟨γ.re, 1⟩ : ℤ√₋₂) = star γ := by
        ext <;> simp [h1]
      rw [hsγ, ← star_pow, hγn]
      ext <;> simp [hα]
  obtain ⟨c, hcn⟩ := hc
  -- norm computation : y = c² + 2
  have hnormγ : ((c ^ 2 + 2) : ℤ) ^ n = y ^ n := by
    have h1 : Zsqrtd.norm (⟨c, 1⟩ : ℤ√₋₂) = c ^ 2 + 2 := by
      rw [norm_def']
      norm_num
    have h2 : Zsqrtd.norm ((⟨c, 1⟩ : ℤ√₋₂) ^ n) = (c ^ 2 + 2) ^ n := by
      rw [← h1]
      exact map_pow Zsqrtd.normMonoidHom _ n
    have h3 : Zsqrtd.norm ((⟨c, 1⟩ : ℤ√₋₂) ^ n) = x ^ 2 + 2 := by
      rcases hcn with h4 | h4 <;> rw [h4] <;> rw [norm_def'] <;> ring
    rw [← h2, h3, h]
  have hy : y = c ^ 2 + 2 := by
    have h1 : (0:ℤ) ≤ c ^ 2 + 2 := by positivity
    exact (pow_inj_of_nonneg h1 (le_of_lt hypos) hn0 hnormγ).symm
  -- c odd
  have hcodd : Odd c := by
    by_contra hc2
    rw [Int.not_odd_iff_even] at hc2
    obtain ⟨t, ht⟩ := hc2
    rcases hyodd with ⟨s, hs⟩
    rw [hy] at hs
    subst ht
    have h5 : (t + t) ^ 2 + 2 = 2 * (2 * t ^ 2 + 1) := by ring
    omega
  refine ⟨c, hcodd, hy, ?_⟩
  rcases hcn with h4 | h4
  · exact Or.inl (by rw [h4])
  · exact Or.inr (by rw [h4])

/-- `θ c = c + √-2`. -/
def th (c : ℤ) : ℤ√₋₂ := ⟨c, 1⟩

/-- `u c k = Im ((c + √-2)^k)`. -/
def useq (c : ℤ) (k : ℕ) : ℤ := ((th c) ^ k).im

/-- `v c k = Re ((c + √-2)^k)`. -/
def vseq (c : ℤ) (k : ℕ) : ℤ := ((th c) ^ k).re

@[simp] theorem useq_zero (c : ℤ) : useq c 0 = 0 := by simp [useq]
@[simp] theorem vseq_zero (c : ℤ) : vseq c 0 = 1 := by simp [vseq]
@[simp] theorem useq_one (c : ℤ) : useq c 1 = 1 := by simp [useq, th]
@[simp] theorem vseq_one (c : ℤ) : vseq c 1 = c := by simp [vseq, th]

theorem useq_succ (c : ℤ) (k : ℕ) : useq c (k + 1) = vseq c k + c * useq c k := by
  simp only [useq, vseq, pow_succ, Zsqrtd.im_mul, th]
  ring

theorem vseq_succ (c : ℤ) (k : ℕ) : vseq c (k + 1) = c * vseq c k - 2 * useq c k := by
  simp only [useq, vseq, pow_succ, Zsqrtd.re_mul, th]
  ring

/-- Components of a power decompose products: `θ^(j+k) = θ^j * θ^k`. -/
theorem useq_add (c : ℤ) (j k : ℕ) :
    useq c (j + k) = vseq c j * useq c k + useq c j * vseq c k := by
  simp only [useq, vseq, pow_add, Zsqrtd.im_mul]

theorem vseq_add (c : ℤ) (j k : ℕ) :
    vseq c (j + k) = vseq c j * vseq c k - 2 * useq c j * useq c k := by
  simp only [useq, vseq, pow_add, Zsqrtd.re_mul]
  ring

/-- Norm relation: `v² + 2u² = (c²+2)^k`. -/
theorem vseq_sq_add (c : ℤ) (k : ℕ) :
    vseq c k ^ 2 + 2 * useq c k ^ 2 = (c ^ 2 + 2) ^ k := by
  have h1 : Zsqrtd.norm ((th c) ^ k) = (Zsqrtd.norm (th c)) ^ k :=
    map_pow Zsqrtd.normMonoidHom _ k
  have h2 : Zsqrtd.norm (th c) = c ^ 2 + 2 := by
    rw [Zsqrtd.norm_def, th]
    ring
  have h3 : Zsqrtd.norm ((th c) ^ k) = vseq c k ^ 2 + 2 * useq c k ^ 2 := by
    rw [Zsqrtd.norm_def]
    simp only [useq, vseq]
    ring
  rw [← h2, ← h3, h1]

/-- The two-step linear recurrence for `u`. -/
theorem useq_rec (c : ℤ) (k : ℕ) :
    useq c (k + 2) = 2 * c * useq c (k + 1) - (c ^ 2 + 2) * useq c k := by
  rw [useq_succ, vseq_succ, useq_succ]
  ring

/-- Explicit small powers. -/
theorem th_pow2 (c : ℤ) : (th c) ^ 2 = ⟨c ^ 2 - 2, 2 * c⟩ := by
  rw [pow_two, th]
  ext
  · rw [Zsqrtd.re_mul]; ring
  · rw [Zsqrtd.im_mul]; ring

theorem th_pow3 (c : ℤ) : (th c) ^ 3 = ⟨c ^ 3 - 6 * c, 3 * c ^ 2 - 2⟩ := by
  have h : (3 : ℕ) = 2 + 1 := rfl
  rw [h, pow_add, th_pow2, pow_one, th]
  ext
  · rw [Zsqrtd.re_mul]; ring
  · rw [Zsqrtd.im_mul]; ring

theorem th_pow4 (c : ℤ) : (th c) ^ 4 = ⟨c ^ 4 - 12 * c ^ 2 + 4, 4 * c ^ 3 - 8 * c⟩ := by
  have h : (4 : ℕ) = 2 * 2 := rfl
  rw [h, pow_mul, th_pow2]
  rw [pow_two]
  ext
  · rw [Zsqrtd.re_mul]; ring
  · rw [Zsqrtd.im_mul]; ring

theorem th_pow5 (c : ℤ) : (th c) ^ 5 = ⟨c ^ 5 - 20 * c ^ 3 + 20 * c,
    5 * c ^ 4 - 20 * c ^ 2 + 4⟩ := by
  have h : (5 : ℕ) = 4 + 1 := rfl
  rw [h, pow_add, th_pow4, pow_one, th]
  ext
  · rw [Zsqrtd.re_mul]; ring
  · rw [Zsqrtd.im_mul]; ring

theorem th_pow7 (c : ℤ) : (th c) ^ 7 = ⟨c ^ 7 - 42 * c ^ 5 + 140 * c ^ 3 - 56 * c,
    7 * c ^ 6 - 70 * c ^ 4 + 84 * c ^ 2 - 8⟩ := by
  have h : (7 : ℕ) = 4 + 3 := rfl
  rw [h, pow_add, th_pow4, th_pow3]
  ext
  · rw [Zsqrtd.re_mul]; ring
  · rw [Zsqrtd.im_mul]; ring

theorem th_pow8 (c : ℤ) : (th c) ^ 8 =
    ⟨(c ^ 4 - 12 * c ^ 2 + 4) ^ 2 - 2 * (4 * c ^ 3 - 8 * c) ^ 2,
     2 * (c ^ 4 - 12 * c ^ 2 + 4) * (4 * c ^ 3 - 8 * c)⟩ := by
  have h : (8 : ℕ) = 4 * 2 := rfl
  rw [h, pow_mul, th_pow4, pow_two]
  ext
  · rw [Zsqrtd.re_mul]; ring
  · rw [Zsqrtd.im_mul]; ring

/-- For odd `c`, `c² = 1 + 8 H`. -/
theorem sq_odd (c : ℤ) (hodd : Odd c) : ∃ H : ℤ, c ^ 2 = 1 + 8 * H := by
  obtain ⟨t, ht⟩ := hodd
  obtain ⟨r, hr⟩ := Int.even_mul_succ_self t
  refine ⟨r, ?_⟩
  subst ht
  have h2 : t * (t + 1) = 2 * r := by omega
  linear_combination 4 * h2

/-- The key `θ⁸` decomposition: `θ⁸ = 1 + 16 a + 8 b √-2` with `b` odd. -/
theorem th8_form (c : ℤ) (hodd : Odd c) :
    ∃ a b : ℤ, (th c) ^ 8 = ⟨1 + 16 * a, 8 * b⟩ ∧ Odd b := by
  obtain ⟨H, hH⟩ := sq_odd c hodd
  have hc4 : c ^ 4 = 1 + 16 * (H + 4 * H ^ 2) := by
    have h1 : c ^ 4 = (c ^ 2) ^ 2 := by ring
    rw [h1, hH]
    ring
  set K := H + 4 * H ^ 2 with hK
  set p := 2 * K - 12 * H - 1 with hpdef
  set q := 4 * p + 1 with hqdef
  have hp : c ^ 4 - 12 * c ^ 2 + 4 = 1 + 8 * p := by
    rw [hpdef]
    linarith [hH, hc4]
  have hq : c ^ 4 - 12 * c ^ 2 + 4 = 2 * q - 1 := by
    rw [hqdef]
    linarith [hp]
  refine ⟨p * q - 2 * (c * (c ^ 2 - 2)) ^ 2,
    (c ^ 4 - 12 * c ^ 2 + 4) * (c * (c ^ 2 - 2)), ?_, ?_⟩
  · rw [th_pow8]
    ext
    · show (c ^ 4 - 12 * c ^ 2 + 4) ^ 2 - 2 * (4 * c ^ 3 - 8 * c) ^ 2 = _
      linear_combination (c ^ 4 - 12 * c ^ 2 + 4 + 1) * hp + 8 * p * hq
    · show 2 * (c ^ 4 - 12 * c ^ 2 + 4) * (4 * c ^ 3 - 8 * c) = _
      ring
  · -- product of three odd factors
    have h1 : Odd (c ^ 4 - 12 * c ^ 2 + 4) := by
      have h2 : Odd (c ^ 4) := hodd.pow
      have h3 : Even (12 * c ^ 2 : ℤ) := ⟨6 * c ^ 2, by ring⟩
      exact (h2.sub_even h3).add_even ⟨2, by norm_num⟩
    have h5 : Odd (c ^ 2 - 2) := (hodd.pow).sub_even ⟨1, by norm_num⟩
    exact h1.mul (hodd.mul h5)

/- ### Values of `u` at small odd indices -/

theorem useq_three (c : ℤ) : useq c 3 = 3 * c ^ 2 - 2 := by rw [useq, th_pow3]

theorem vseq_three (c : ℤ) : vseq c 3 = c ^ 3 - 6 * c := by rw [vseq, th_pow3]

theorem useq_five (c : ℤ) : useq c 5 = 5 * c ^ 4 - 20 * c ^ 2 + 4 := by rw [useq, th_pow5]

theorem useq_seven (c : ℤ) : useq c 7 = 7 * c ^ 6 - 70 * c ^ 4 + 84 * c ^ 2 - 8 := by
  rw [useq, th_pow7]

/- ### Behaviour of `u` modulo 8 -/

theorem useq_add8 (c : ℤ) (hodd : Odd c) (k : ℕ) :
    (8 : ℤ) ∣ useq c (k + 8) - useq c k := by
  obtain ⟨a, b, h8, hb⟩ := th8_form c hodd
  have h1 : useq c 8 = 8 * b := by rw [useq, h8]
  have h2 : vseq c 8 = 1 + 16 * a := by rw [vseq, h8]
  have h3 := useq_add c k 8
  rw [h1, h2] at h3
  exact ⟨vseq c k * b + useq c k * (2 * a), by linear_combination h3⟩

theorem useq_mod8_reduce (c : ℤ) (hodd : Odd c) (r m : ℕ) :
    (8 : ℤ) ∣ useq c (r + 8 * m) - useq c r := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 := useq_add8 c hodd (r + 8 * m)
    have h2 : r + 8 * (m + 1) = (r + 8 * m) + 8 := by ring
    rw [h2]
    have h3 := dvd_add h1 ih
    rwa [show useq c (r + 8 * m + 8) - useq c (r + 8 * m) + (useq c (r + 8 * m) - useq c r)
        = useq c (r + 8 * m + 8) - useq c r from by ring] at h3

theorem useq_mod8_cases (c : ℤ) (hodd : Odd c) (n : ℕ) (hn : Odd n) :
    ((n % 8 = 1 ∨ n % 8 = 3) ∧ (8 : ℤ) ∣ useq c n - 1) ∨
    ((n % 8 = 5 ∨ n % 8 = 7) ∧ (8 : ℤ) ∣ useq c n - 5) := by
  obtain ⟨H, hH⟩ := sq_odd c hodd
  have hc4 : c ^ 4 = 1 + 8 * (2 * H + 8 * H ^ 2) := by
    have h0 : c ^ 4 = c ^ 2 * c ^ 2 := by ring
    rw [h0, hH]; ring
  set K := 2 * H + 8 * H ^ 2 with hK
  have hc6 : c ^ 6 = 1 + 8 * (K + H + 8 * K * H) := by
    have h0 : c ^ 6 = c ^ 4 * c ^ 2 := by ring
    rw [h0, hc4, hH]; ring
  set L := K + H + 8 * K * H with hL
  have hd : n % 8 + 8 * (n / 8) = n := by omega
  have hmod2 : n % 2 = 1 := Nat.odd_iff.mp hn
  have hr : n % 8 = 1 ∨ n % 8 = 3 ∨ n % 8 = 5 ∨ n % 8 = 7 := by omega
  have hred := useq_mod8_reduce c hodd (n % 8) (n / 8)
  rw [hd] at hred
  rcases hr with h | h | h | h
  · left
    refine ⟨Or.inl h, ?_⟩
    rw [h, useq_one] at hred
    exact hred
  · left
    refine ⟨Or.inr h, ?_⟩
    rw [h, useq_three] at hred
    obtain ⟨t, ht⟩ := hred
    exact ⟨t + 3 * H, by linear_combination ht + 3 * hH⟩
  · right
    refine ⟨Or.inl h, ?_⟩
    rw [h, useq_five] at hred
    obtain ⟨t, ht⟩ := hred
    exact ⟨t + 5 * K - 20 * H - 2, by linear_combination ht + 5 * hc4 - 20 * hH⟩
  · right
    refine ⟨Or.inr h, ?_⟩
    rw [h, useq_seven] at hred
    obtain ⟨t, ht⟩ := hred
    exact ⟨t + 7 * L - 70 * K + 84 * H + 1, by
      linear_combination ht + 7 * hc6 - 70 * hc4 + 84 * hH⟩

theorem useq_ne_neg_one (c : ℤ) (hodd : Odd c) {n : ℕ} (hn : Odd n) :
    useq c n ≠ -1 := by
  intro h
  rcases useq_mod8_cases c hodd n hn with ⟨_, t, ht⟩ | ⟨_, t, ht⟩ <;> rw [h] at ht <;> omega

theorem useq_eq_one_mod8 (c : ℤ) (hodd : Odd c) {n : ℕ} (hn : Odd n)
    (h : useq c n = 1) : n % 8 = 1 ∨ n % 8 = 3 := by
  rcases useq_mod8_cases c hodd n hn with ⟨h13, _⟩ | ⟨_, t, ht⟩
  · exact h13
  · rw [h] at ht; omega

/- ### Lifting the exponent: the shape of `θ ^ (2^k · odd)` for `k ≥ 3` -/

theorem theta_pow_8two (c : ℤ) (hodd : Odd c) (t : ℕ) : ∃ a b : ℤ,
    (th c) ^ (8 * 2 ^ t) = ⟨1 + 16 * 2 ^ t * a, 8 * 2 ^ t * b⟩ ∧ Odd b := by
  induction t with
  | zero => simpa using th8_form c hodd
  | succ t ih =>
    obtain ⟨a, b, heq, hb⟩ := ih
    refine ⟨a + 8 * 2 ^ t * a ^ 2 - 4 * 2 ^ t * b ^ 2, b * (1 + 16 * 2 ^ t * a), ?_,
      hb.mul ⟨8 * 2 ^ t * a, by ring⟩⟩
    have hexp : 8 * 2 ^ (t + 1) = (8 * 2 ^ t) * 2 := by ring
    rw [hexp, pow_mul, heq, sq]
    ext
    · rw [Zsqrtd.re_mul]; ring
    · rw [Zsqrtd.im_mul]; ring

theorem theta_pow_8two_mul_odd (c : ℤ) (hodd : Odd c) (t : ℕ) : ∀ j : ℕ, ∃ A B : ℤ,
    (th c) ^ (8 * 2 ^ t * (2 * j + 1)) = ⟨1 + 16 * 2 ^ t * A, 8 * 2 ^ t * B⟩ ∧ Odd B := by
  intro j
  induction j with
  | zero => simpa using theta_pow_8two c hodd t
  | succ j ih =>
    obtain ⟨A, B, hAB, hB⟩ := ih
    obtain ⟨a, b, hab, hb⟩ := theta_pow_8two c hodd (t + 1)
    have hexp : 8 * 2 ^ t * (2 * (j + 1) + 1) = 8 * 2 ^ t * (2 * j + 1) + 8 * 2 ^ (t + 1) := by
      ring
    refine ⟨A + 2 * a + 32 * 2 ^ t * A * a - 16 * 2 ^ t * B * b,
      B + (2 * b + 32 * 2 ^ t * (A * b + B * a)), ?_, ?_⟩
    · rw [hexp, pow_add, hAB, hab]
      ext
      · rw [Zsqrtd.re_mul]; ring
      · rw [Zsqrtd.im_mul]; ring
    · exact hB.add_even ⟨b + 16 * 2 ^ t * (A * b + B * a), by ring⟩

/-- The key "kill" lemma: if `n > j`, `8 ∣ n - j` and `v j` is odd, then `u n ≠ u j`. -/
theorem useq_kill (c : ℤ) (hodd : Odd c) (j n : ℕ) (hjn : j < n) (h8 : (8 : ℕ) ∣ n - j)
    (hV : Odd (vseq c j)) : useq c n ≠ useq c j := by
  obtain ⟨k, w, hw, hkw⟩ := Nat.exists_eq_two_pow_mul_odd (show n - j ≠ 0 by omega)
  have hwodd : w % 2 = 1 := Nat.odd_iff.mp hw
  have hk3 : 3 ≤ k := by
    by_contra hk
    push_neg at hk
    interval_cases k <;> omega
  obtain ⟨A, B, hAB, hB⟩ := theta_pow_8two_mul_odd c hodd (k - 3) (w / 2)
  have h8p : (8 : ℕ) * 2 ^ (k - 3) = 2 ^ k := by
    rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_add]
    congr 1
    omega
  have hidx : 8 * 2 ^ (k - 3) * (2 * (w / 2) + 1) = n - j := by
    rw [h8p, show 2 * (w / 2) + 1 = w from by omega]
    exact hkw.symm
  have hsplit : n = j + (n - j) := by omega
  have hun : useq c n = vseq c j * useq c (n - j) + useq c j * vseq c (n - j) := by
    conv_lhs => rw [hsplit]
    exact useq_add c j (n - j)
  have hu' : useq c (n - j) = 8 * 2 ^ (k - 3) * B := by
    rw [useq, ← hidx, hAB]
  have hv' : vseq c (n - j) = 1 + 16 * 2 ^ (k - 3) * A := by
    rw [vseq, ← hidx, hAB]
  rw [hu', hv'] at hun
  intro heq
  rw [heq] at hun
  have h0 : (8 * 2 ^ (k - 3) : ℤ) * (vseq c j * B + 2 * useq c j * A) = 0 := by
    linear_combination -hun
  rcases mul_eq_zero.mp h0 with h1 | h1
  · have := pow_pos (show (0:ℤ) < 2 by norm_num) (k - 3)
    linarith
  · have hOdd : Odd (vseq c j * B + 2 * useq c j * A) :=
      (hV.mul hB).add_even ⟨useq c j * A, by ring⟩
    rw [h1] at hOdd
    simp [Int.odd_iff] at hOdd

/- ### The Pell bridge and descent -/

/-- Bridge identity: `u(m+1)² - (c²+2)·u(m)² = u(2m+1)`. -/
theorem bridge (c : ℤ) (m : ℕ) :
    useq c (m + 1) ^ 2 - (c ^ 2 + 2) * useq c m ^ 2 = useq c (2 * m + 1) := by
  have hE3 := vseq_sq_add c m
  have hE4 := vseq_sq_add c (m + 1)
  have hE1 : useq c (m + 1) * vseq c m - vseq c (m + 1) * useq c m = (c ^ 2 + 2) ^ m := by
    rw [useq_succ, vseq_succ]
    linear_combination hE3
  have hE2 : useq c (2 * m + 1) = vseq c (m + 1) * useq c m + useq c (m + 1) * vseq c m := by
    have h0 : 2 * m + 1 = (m + 1) + m := by ring
    rw [h0, useq_add]
  have hkey : (c ^ 2 + 2) ^ m *
      (useq c (m + 1) ^ 2 - (c ^ 2 + 2) * useq c m ^ 2 - useq c (2 * m + 1)) = 0 := by
    linear_combination (-(useq c (m + 1) ^ 2)) * hE3 + useq c m ^ 2 * hE4 +
      (vseq c (m + 1) * useq c m + useq c (m + 1) * vseq c m) * hE1 - (c ^ 2 + 2) ^ m * hE2
  have hN : ((c ^ 2 + 2) ^ m : ℤ) ≠ 0 := by positivity
  rcases mul_eq_zero.mp hkey with h | h
  · exact absurd h hN
  · linarith

/-- Pell descent: any solution of `A² = (C²+2)B² + 1` has `C ∣ B`. -/
theorem pell_dvd (C : ℤ) (hC : 1 ≤ C) (N : ℕ) : ∀ A B : ℤ, B.natAbs = N →
    A ^ 2 = (C ^ 2 + 2) * B ^ 2 + 1 → C ∣ B := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro A B hN h
    by_cases hB0 : B = 0
    · simp [hB0]
    set A' := |A| with hA'
    set B' := |B| with hB'
    have h' : A' ^ 2 = (C ^ 2 + 2) * B' ^ 2 + 1 := by
      rw [hA', hB', sq_abs, sq_abs]; exact h
    have hB'pos : 0 < B' := abs_pos.mpr hB0
    have hA'nn : 0 ≤ A' := abs_nonneg A
    have hgt : C * B' < A' := by
      have h2 : (C * B') ^ 2 < A' ^ 2 := by nlinarith [hB'pos]
      exact lt_of_pow_lt_pow_left₀ 2 hA'nn h2
    set D := A' - C * B' with hD
    have hD1 : 1 ≤ D := by
      have := Int.add_one_le_iff.mpr hgt
      rw [hD]; linarith
    have hkey : 2 * C * B' * D + D ^ 2 = 2 * B' ^ 2 + 1 := by
      rw [hD]; linear_combination h'
    have hBC : C ≤ B' := by
      have hint1 : 0 ≤ 2 * C * B' * (D - 1) := by
        have : (0:ℤ) ≤ 2 * C * B' := by positivity
        exact mul_nonneg this (by linarith)
      have hint2 : 1 ≤ D ^ 2 := by nlinarith [hD1]
      by_contra hlt
      push_neg at hlt
      nlinarith [mul_pos (show (0:ℤ) < C - B' by linarith) hB'pos]
    set A'' := (C ^ 2 + 1) * A' - C * (C ^ 2 + 2) * B' with hA''
    set B'' := (C ^ 2 + 1) * B' - C * A' with hB''
    have h'' : A'' ^ 2 = (C ^ 2 + 2) * B'' ^ 2 + 1 := by
      rw [hA'', hB'']
      linear_combination h'
    have hB''0 : 0 ≤ B'' := by
      by_contra hneg
      push_neg at hneg
      have h1 : (C ^ 2 + 1) * B' < C * A' := by
        rw [hB''] at hneg; linarith
      have h2 : (0:ℤ) ≤ (C ^ 2 + 1) * B' := by positivity
      have h3 : ((C ^ 2 + 1) * B') ^ 2 < (C * A') ^ 2 := by nlinarith [h1, h2]
      have h4 : C ^ 2 * A' ^ 2 = C ^ 2 * ((C ^ 2 + 2) * B' ^ 2 + 1) := by rw [h']
      have h5 : C * C ≤ B' * B' :=
        mul_self_le_mul_self (by linarith) hBC
      nlinarith [h3, h4, h5]
    have hB''lt : B'' < B' := by
      have h1 : C * (C * B') < C * A' :=
        mul_lt_mul_of_pos_left hgt (by linarith : (0:ℤ) < C)
      rw [hB'']; nlinarith [h1]
    have hlt : B''.natAbs < N := by
      have e1 : B'.natAbs = N := by rw [hB', Int.natAbs_abs, hN]
      omega
    have hdvd'' : C ∣ B'' := ih B''.natAbs hlt A'' B'' rfl h''
    have hfin : C ∣ B' := by
      have h5 : B' = B'' + C * D := by rw [hB'', hD]; ring
      rw [h5]
      exact dvd_add hdvd'' (dvd_mul_right C D)
    rwa [hB', dvd_abs] at hfin

/-- Along odd indices, `u (2i+1) ≡ (-2)^i  (mod c)`. -/
theorem useq_odd_mod_c (c : ℤ) : ∀ i : ℕ, c ∣ useq c (2 * i + 1) - (-2) ^ i := by
  intro i
  induction i with
  | zero => simp
  | succ i ih =>
    have hrec := useq_rec c (2 * i + 1)
    have h1 : 2 * (i + 1) + 1 = (2 * i + 1) + 2 := by ring
    rw [h1, hrec]
    obtain ⟨k, hk⟩ := ih
    exact ⟨2 * useq c (2 * i + 1 + 1) - c * useq c (2 * i + 1) - 2 * k, by
      linear_combination (-2) * hk⟩

/- ### The core theorem -/

/-- If `c` is odd, `n` odd with `n ≥ 3`, and `Im((c + √-2)ⁿ) = ±1`, then `n = 3` and
`c² = 1`. -/
theorem core (c : ℤ) (hodd : Odd c) (n : ℕ) (hn : Odd n) (h3 : 3 ≤ n)
    (h : useq c n = 1 ∨ useq c n = -1) : n = 3 ∧ c ^ 2 = 1 := by
  have h1 : useq c n = 1 := by
    rcases h with h | h
    · exact h
    · exact absurd h (useq_ne_neg_one c hodd hn)
  rcases useq_eq_one_mod8 c hodd hn h1 with hm1 | hm3
  · -- n ≡ 1 (mod 8) is impossible for n ≥ 3
    exfalso
    have hkill := useq_kill c hodd 1 n (by omega) (by omega : (8:ℕ) ∣ n - 1)
      (by rw [vseq_one]; exact hodd)
    rw [useq_one] at hkill
    exact hkill h1
  · -- n ≡ 3 (mod 8)
    set m := n / 2 with hmdef
    have hm : n = 2 * m + 1 := by omega
    have hbr := bridge c m
    rw [← hm, h1] at hbr
    have hc0 : c ≠ 0 := by rcases hodd with ⟨t, ht⟩; omega
    have hC1 : 1 ≤ |c| := by
      rcases abs_cases c with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rcases hodd with ⟨t, ht⟩ <;> omega
    have hA : useq c (m + 1) ^ 2 = (|c| ^ 2 + 2) * useq c m ^ 2 + 1 := by
      rw [sq_abs]; linarith [hbr]
    have hdvdB := pell_dvd |c| hC1 (useq c m).natAbs (useq c (m + 1)) (useq c m) rfl hA
    have hdvdB' : c ∣ useq c m := (abs_dvd c _).mp hdvdB
    have hi : m = 2 * (m / 2) + 1 := by omega
    set i := m / 2 with hidef
    have hmodc := useq_odd_mod_c c i
    rw [← hi] at hmodc
    have hdvd2 : c ∣ (-2 : ℤ) ^ i := by
      have h5 := dvd_sub hdvdB' hmodc
      rwa [sub_sub_cancel] at h5
    have hcop : IsCoprime c ((-2 : ℤ) ^ i) := by
      obtain ⟨t, ht⟩ := hodd
      have h2 : IsCoprime c (-2 : ℤ) := ⟨1, t, by rw [ht]; ring⟩
      exact h2.pow_right
    have hunit : IsUnit c := hcop.isUnit_of_dvd hdvd2
    have hc2 : c ^ 2 = 1 := by
      rcases Int.isUnit_iff.mp hunit with h6 | h6 <;> rw [h6] <;> norm_num
    refine ⟨?_, hc2⟩
    by_contra hne
    have h3lt : 3 < n := by omega
    have hkill := useq_kill c hodd 3 n h3lt (by omega : (8:ℕ) ∣ n - 3)
      (by rw [vseq_three]; exact (hodd.pow).sub_even ⟨3 * c, by ring⟩)
    rw [useq_three, hc2] at hkill
    norm_num at hkill
    exact hkill h1


/-- **Fermat–Nagell over `ℤ`**: if `x² + 2 = yⁿ` with `n` odd, `n ≥ 3`, then `y = 3` and
`n = 3`. -/
theorem nagell_int (x y : ℤ) (n : ℕ) (hn : Odd n) (h3 : 3 ≤ n)
    (h : x ^ 2 + 2 = y ^ n) : y = 3 ∧ n = 3 := by
  obtain ⟨c, hcodd, hy, him⟩ := exists_c x y n hn h3 h
  have him' : useq c n = 1 ∨ useq c n = -1 := him
  obtain ⟨hn3, hc2⟩ := core c hcodd n hn h3 him'
  refine ⟨?_, hn3⟩
  rw [hy, hc2]
  norm_num

end Zneg2

end ZsqrtNeg2

/--
**Open (Lebesgue–Ramanujan–Nagell with negative coefficient).**  The equation
$x^2 - 2 = y^r$ has no solutions in natural numbers with $y \ge 2$ and $r$ an odd prime.

This is a well-known open problem.  Bugeaud, Mignotte and Siksek (*Classical and modular
approaches to exponential Diophantine equations II: the Lebesgue–Nagell equation*,
Compos. Math. 142 (2006)) solved $x^2 + D = y^n$ for $1 \le D \le 100$; the case of
negative $D$ (here $D = -2$) is beyond both the classical method (the unit group of
$\mathbb{Z}[\sqrt{2}]$ is infinite, and odd-power maps are $2$-adic bijections on units,
so no congruence obstruction exists) and the modular method.  Schinzel–Tijdeman gives an
effective but astronomically large bound on $r$; the determination has never been
completed.  Verified: no solutions with $y^r \le 10^{43}$.
-/
theorem no_sq_sub_two_pow_prime (x y r : ℕ) (hy : 2 ≤ y) (hr : Nat.Prime r) (hro : Odd r)
    (h : y ^ r + 2 = x ^ 2) : False := sorry

/--
**Open (case of Pillai's conjecture).**  No perfect powers with distinct odd prime
exponents differ by 2.

Pillai conjectured (1945) that $x^p - y^q = c$ has finitely many solutions for each
$c \ge 1$; for $c = 2$ even finiteness is open (the only proved case is $c = 1$,
Mihailescu's theorem, whose cyclotomic method is specific to difference $1$).  Results of
Scott and Styer (J. Number Theory, 2004) on $p^x - q^y = c$ bound the number of solutions
for *fixed* prime bases only.  Verified: no solutions with $x^r \le 10^{43}$.
-/
theorem no_pow_sub_two_pow_distinct_odd_primes (x y r s : ℕ) (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hr : Nat.Prime r) (hs : Nat.Prime s) (hro : Odd r) (hso : Odd s) (hrs : r ≠ s)
    (h : y ^ s + 2 = x ^ r) : False := sorry

/-- No two positive squares differ by exactly 2. -/
theorem no_sq_sub_two_sq (x y : ℕ) (hy : 1 ≤ y) (h : y ^ 2 + 2 = x ^ 2) : False := by
  have hxy : y < x := by nlinarith
  have : y + 1 ≤ x := hxy
  nlinarith

/-- No two powers with the same exponent `r ≥ 2` (and bases `≥ 2`) differ by exactly 2. -/
theorem no_pow_sub_two_same_exp (x y r : ℕ) (hy : 2 ≤ y) (hr : 2 ≤ r)
    (h : y ^ r + 2 = x ^ r) : False := by
  have hyx : y < x := by
    have hlt : y ^ r < x ^ r := by omega
    exact Nat.pow_lt_pow_iff_left (by omega : r ≠ 0) |>.mp hlt
  have hstep : y ^ (r - 1) + 1 ≤ (y + 1) ^ (r - 1) := by
    have := Nat.pow_lt_pow_left (show y < y + 1 by omega) (n := r - 1) (by omega)
    omega
  have hyx1 : y + 1 ≤ x := hyx
  have h1 : (y + 1) ^ r ≤ x ^ r := Nat.pow_le_pow_left hyx1 r
  have h2 : (y ^ (r - 1) + 1) * (y + 1) ≤ (y + 1) ^ (r - 1) * (y + 1) :=
    Nat.mul_le_mul_right _ hstep
  have h3 : (y + 1) ^ (r - 1) * (y + 1) = (y + 1) ^ r := by
    rw [← pow_succ]
    congr 1
    omega
  have h4 : y ^ (r - 1) * y = y ^ r := by
    rw [← pow_succ]
    congr 1
    omega
  nlinarith [pow_pos (show 0 < y by omega) (r - 1), pow_pos (show 0 < y by omega) r]

/-- The least prime factor of an odd number `≥ 3` is an odd prime `≥ 3`. -/
theorem minFac_odd_prime {n : ℕ} (hn : Odd n) (h3 : 3 ≤ n) :
    Nat.Prime n.minFac ∧ Odd n.minFac ∧ 3 ≤ n.minFac := by
  have hne : n ≠ 1 := by omega
  have hp := Nat.minFac_prime hne
  have hodd : Odd n.minFac := by
    rcases hp.eq_two_or_odd' with h2 | ho
    · exfalso
      have : (2 : ℕ) ∣ n := h2 ▸ Nat.minFac_dvd n
      rcases hn with ⟨t, ht⟩
      omega
    · exact ho
  exact ⟨hp, hodd, by
    have := hp.two_le
    rcases hodd with ⟨t, ht⟩
    omega⟩

/-- Rewriting a power along its least prime factor. -/
theorem pow_minFac_eq (y n : ℕ) :
    (y ^ (n / n.minFac)) ^ n.minFac = y ^ n := by
  rw [← pow_mul, Nat.div_mul_cancel (Nat.minFac_dvd n)]

/-- **Fermat--Nagell** for arbitrary odd exponents `n ≥ 3`: the only solution of
`x² + 2 = yⁿ` in natural numbers is `5² + 2 = 3³`.  Proved completely above. -/
theorem nagell_sq_add_two (x y n : ℕ) (hn : Odd n) (h3 : 3 ≤ n)
    (h : x ^ 2 + 2 = y ^ n) : x = 5 ∧ y = 3 ∧ n = 3 := by
  have hz : (x : ℤ) ^ 2 + 2 = (y : ℤ) ^ n := by exact_mod_cast h
  obtain ⟨hy3, hn3⟩ := Zneg2.nagell_int x y n hn h3 hz
  have hyn : y = 3 := by exact_mod_cast hy3
  subst hn3
  rw [hyn] at h
  have h27 : x ^ 2 + 2 = 27 := by norm_num at h ⊢; exact h
  have hx2 : x ^ 2 = 25 := by linarith
  have hx5 : x = 5 :=
    Nat.pow_left_injective (by norm_num) (by norm_num [hx2] : x ^ 2 = 5 ^ 2)
  exact ⟨hx5, hyn, rfl⟩

/-- The open equation `x² - 2 = yⁿ`, reduced to prime exponents. -/
theorem no_sq_sub_two_pow (x y n : ℕ) (hy : 2 ≤ y) (hn : Odd n) (h3 : 3 ≤ n)
    (h : y ^ n + 2 = x ^ 2) : False := by
  obtain ⟨hp, ho, hp3⟩ := minFac_odd_prime hn h3
  have hd : 0 < n / n.minFac := Nat.div_pos (Nat.minFac_le (by omega)) (by omega)
  have hY : 2 ≤ y ^ (n / n.minFac) := by
    calc (2:ℕ) = 2 ^ 1 := (pow_one 2).symm
    _ ≤ y ^ 1 := Nat.pow_le_pow_left hy 1
    _ ≤ y ^ (n / n.minFac) := Nat.pow_le_pow_right (by omega) hd
  exact no_sq_sub_two_pow_prime x (y ^ (n / n.minFac)) n.minFac hY hp ho
    (by rw [pow_minFac_eq]; exact h)

/-- The open Pillai case `xᵐ - yⁿ = 2`, reduced to prime exponents. -/
theorem no_odd_pow_sub_two_pow (x y m n : ℕ) (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hm : Odd m) (hn : Odd n) (hm3 : 3 ≤ m) (hn3 : 3 ≤ n)
    (h : y ^ n + 2 = x ^ m) : False := by
  obtain ⟨hpm, hom, hm3'⟩ := minFac_odd_prime hm hm3
  obtain ⟨hpn, hon, hn3'⟩ := minFac_odd_prime hn hn3
  have hdm : 0 < m / m.minFac := Nat.div_pos (Nat.minFac_le (by omega)) (by omega)
  have hdn : 0 < n / n.minFac := Nat.div_pos (Nat.minFac_le (by omega)) (by omega)
  have hX : 2 ≤ x ^ (m / m.minFac) := by
    calc (2:ℕ) = 2 ^ 1 := (pow_one 2).symm
    _ ≤ x ^ 1 := Nat.pow_le_pow_left hx 1
    _ ≤ x ^ (m / m.minFac) := Nat.pow_le_pow_right (by omega) hdm
  have hY : 2 ≤ y ^ (n / n.minFac) := by
    calc (2:ℕ) = 2 ^ 1 := (pow_one 2).symm
    _ ≤ y ^ 1 := Nat.pow_le_pow_left hy 1
    _ ≤ y ^ (n / n.minFac) := Nat.pow_le_pow_right (by omega) hdn
  have hred : (y ^ (n / n.minFac)) ^ n.minFac + 2 = (x ^ (m / m.minFac)) ^ m.minFac := by
    rw [pow_minFac_eq, pow_minFac_eq]; exact h
  rcases eq_or_ne m.minFac n.minFac with heq | hne
  · exact no_pow_sub_two_same_exp (x ^ (m / m.minFac)) (y ^ (n / n.minFac)) m.minFac hY
      (by omega) (by rw [heq] at hred ⊢; exact hred)
  · exact no_pow_sub_two_pow_distinct_odd_primes (x ^ (m / m.minFac)) (y ^ (n / n.minFac))
      m.minFac n.minFac hX hY hpm hpn hom hon hne hred

/--
A365416 According to Pillai's conjecture, k = 13 is the only term such that 2*k-1 and 2*k+1 both have exponent greater than 1.
-/
theorem oeis_365416_conjecture_0 :
  ∀ k : ℕ,
    (IsCompositePrimePow (2 * k - 1) ∧ IsCompositePrimePow (2 * k + 1)) ↔ k = 13 := by
  intro k
  constructor
  · rintro ⟨⟨q, b, hq, hb, hqb⟩, ⟨p, a, hp, ha, hpa⟩⟩
    -- rule out k = 0
    have hk1 : 1 ≤ k := by
      by_contra hk
      have hk0 : k = 0 := by omega
      subst hk0
      simp only [Nat.mul_zero, Nat.zero_sub] at hqb
      have h0 := pow_eq_zero_iff (by omega : b ≠ 0) |>.mp hqb
      exact absurd h0 hq.ne_zero
    -- the key equation
    have hkey : q ^ b + 2 = p ^ a := by omega
    -- case analysis on parities of a and b
    rcases Nat.even_or_odd a with hae | hao
    · -- a even : p ^ a = (p ^ (a/2))²
      obtain ⟨c, hc⟩ := hae
      have hc' : a = 2 * c := by omega
      have hcpos : 1 ≤ c := by omega
      have hpa2 : (p ^ c) ^ 2 = p ^ a := by
        rw [← pow_mul, hc']; ring_nf
      rcases Nat.even_or_odd b with hbe | hbo
      · -- b even : two squares differing by 2, impossible
        obtain ⟨d, hd⟩ := hbe
        have hd' : b = 2 * d := by omega
        have hdpos : 1 ≤ d := by omega
        have hqb2 : (q ^ d) ^ 2 = q ^ b := by
          rw [← pow_mul, hd']; ring_nf
        have h2 : (q ^ d) ^ 2 + 2 = (p ^ c) ^ 2 := by rw [hqb2, hpa2]; exact hkey
        exact absurd h2 (fun h2 => no_sq_sub_two_sq (p ^ c) (q ^ d)
          (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ hq.ne_zero)) h2)
      · -- b odd (≥ 3) : x² - 2 = q ^ b, open case
        have hb3 : 3 ≤ b := by
          rcases hbo with ⟨t, ht⟩; omega
        exact (no_sq_sub_two_pow (p ^ c) q b hq.two_le hbo hb3
          (by rw [hpa2]; exact hkey)).elim
    · -- a odd (≥ 3)
      have ha3 : 3 ≤ a := by
        rcases hao with ⟨t, ht⟩; omega
      rcases Nat.even_or_odd b with hbe | hbo
      · -- b even : Nagell's equation x² + 2 = p ^ a
        obtain ⟨d, hd⟩ := hbe
        have hd' : b = 2 * d := by omega
        have hdpos : 1 ≤ d := by omega
        have hqb2 : (q ^ d) ^ 2 = q ^ b := by
          rw [← pow_mul, hd']; ring_nf
        obtain ⟨hx5, hp3, ha3'⟩ := nagell_sq_add_two (q ^ d) p a hao ha3
          (by rw [hqb2]; exact hkey)
        -- p ^ a = 27, hence 2k + 1 = 27, k = 13
        have : p ^ a = 27 := by rw [hp3, ha3']; norm_num
        omega
      · -- both odd : Pillai case
        have hb3 : 3 ≤ b := by
          rcases hbo with ⟨t, ht⟩; omega
        exact (no_odd_pow_sub_two_pow p q a b hp.two_le hq.two_le
          hao hbo ha3 hb3 hkey).elim
  · rintro rfl
    exact ⟨⟨5, 2, by norm_num⟩, ⟨3, 3, by norm_num⟩⟩
