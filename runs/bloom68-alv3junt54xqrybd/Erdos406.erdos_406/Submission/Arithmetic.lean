import FormalConjecturesUtil

/-!
# Unconditional arithmetic helpers for Erdős problem 406

This file does not import the conjecture or its proposed disproof.  All results
below concern base-three digits and powers of two, without assuming either
answer to the finiteness question.  `Nat.digits` lists digits least significant
first.
-/

namespace Erdos406.Arithmetic

/-- A power of two whose base-three digits all belong to `{0, 1}`. -/
def good (n : ℕ) : Prop :=
  n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0, 1]

/-- An exponent giving a power of two with no base-three digit `2`. -/
def goodExponent (k : ℕ) : Prop :=
  Nat.digits 3 (2 ^ k) ⊆ [0, 1]

instance (k : ℕ) : Decidable (goodExponent k) :=
  inferInstanceAs (Decidable (Nat.digits 3 (2 ^ k) ⊆ [0, 1]))

/-- Every base-three digit is `0`, `1`, or `2`, so goodness is precisely absence of `2`. -/
theorem digits_good_iff_two_absent (n : ℕ) :
    Nat.digits 3 n ⊆ [0, 1] ↔ 2 ∉ Nat.digits 3 n := by
  constructor
  · intro h htwo
    have hbad := h htwo
    simp at hbad
  · intro h digit hdigit
    have hsmall := Nat.digits_lt_base (by decide : 1 < 3) hdigit
    have hne : digit ≠ 2 := by
      intro heq
      subst digit
      exact h hdigit
    simp only [List.mem_cons]
    omega

theorem goodExponent_iff_two_absent (k : ℕ) :
    goodExponent k ↔ 2 ∉ Nat.digits 3 (2 ^ k) :=
  digits_good_iff_two_absent (2 ^ k)

/-- Passing to the next base-three digit preserves goodness. -/
theorem digits_good_div_three (n : ℕ) (h : Nat.digits 3 n ⊆ [0, 1]) :
    Nat.digits 3 (n / 3) ⊆ [0, 1] := by
  by_cases hn : n = 0
  · simp [hn]
  · rw [Nat.digits_eq_cons_digits_div (by decide : 1 < 3) hn] at h
    intro digit hdigit
    exact h (List.mem_cons_of_mem _ hdigit)

/-- Truncating any number of low base-three digits preserves goodness. -/
theorem digits_good_div_three_pow (n r : ℕ) (h : Nat.digits 3 n ⊆ [0, 1]) :
    Nat.digits 3 (n / 3 ^ r) ⊆ [0, 1] := by
  induction r with
  | zero => simpa using h
  | succ r ih =>
    rw [pow_succ, ← Nat.div_div_eq_div_mul]
    exact digits_good_div_three _ ih

/-- The digit at any position of a good number is not `2`, including zero padding. -/
theorem digits_good_digit_ne_two (n r : ℕ) (h : Nat.digits 3 n ⊆ [0, 1]) :
    n / 3 ^ r % 3 ≠ 2 := by
  have hquot := digits_good_div_three_pow n r h
  by_cases hzero : n / 3 ^ r = 0
  · simp [hzero]
  · intro heq
    have hmem : n / 3 ^ r % 3 ∈ Nat.digits 3 (n / 3 ^ r) := by
      rw [Nat.digits_eq_cons_digits_div (by decide : 1 < 3) hzero]
      exact List.mem_cons_self
    rw [heq] at hmem
    exact (digits_good_iff_two_absent _).mp hquot hmem

/-- The natural-number formulation is the injective image of the good exponents. -/
theorem good_set_image :
    {n : ℕ | good n} = (fun k : ℕ => 2 ^ k) '' {k | goodExponent k} := by
  ext n
  constructor
  · rintro ⟨⟨k, rfl⟩, hdigits⟩
    exact ⟨k, hdigits, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨k, rfl⟩, hk⟩

/-- Finiteness in the original question is equivalent to bounded good exponents. -/
theorem finite_iff_bounded_goodExponents :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0, 1]}.Finite ↔
      ∃ K : ℕ, ∀ k : ℕ, goodExponent k → k ≤ K := by
  change {n : ℕ | good n}.Finite ↔ _
  rw [good_set_image,
    Set.finite_image_iff (Nat.pow_right_injective (by decide : 2 ≤ 2)).injOn,
    Set.finite_iff_bddAbove]
  rfl

/-- Equivalently, every sufficiently large exponent produces a digit `2`. -/
theorem finite_iff_eventually_digit_two :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0, 1]}.Finite ↔
      ∃ K : ℕ, ∀ k : ℕ, K ≤ k → 2 ∈ Nat.digits 3 (2 ^ k) := by
  rw [finite_iff_bounded_goodExponents]
  constructor
  · rintro ⟨K, hK⟩
    refine ⟨K + 1, ?_⟩
    intro k hk
    by_contra htwo
    have hgood : goodExponent k := (goodExponent_iff_two_absent _).mpr htwo
    have hbound := hK k hgood
    omega
  · rintro ⟨K, hK⟩
    refine ⟨K, ?_⟩
    intro k hk
    by_contra hbound
    have htwo := hK k (by omega)
    exact (goodExponent_iff_two_absent _).mp hk htwo

/-- The negation of finiteness is equivalent to arbitrarily large good exponents. -/
theorem not_finite_iff_arbitrarily_large_goodExponents :
    ¬ {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0, 1]}.Finite ↔
      ∀ K : ℕ, ∃ k : ℕ, K < k ∧ goodExponent k := by
  rw [finite_iff_bounded_goodExponents]
  simp only [not_exists, not_forall, Nat.not_le]
  constructor
  · intro h K
    obtain ⟨k, hk, hlarge⟩ := h K
    exact ⟨k, hlarge, hk⟩
  · intro h K
    obtain ⟨k, hlarge, hk⟩ := h K
    exact ⟨k, hk, hlarge⟩

/-- Powers of two modulo three depend only on the parity of the exponent. -/
theorem two_pow_mod_three (k : ℕ) :
    2 ^ k % 3 = 2 ^ (k % 2) % 3 := by
  calc
    2 ^ k % 3 = 2 ^ (2 * (k / 2) + k % 2) % 3 := by
      have hk : k = 2 * (k / 2) + k % 2 := by omega
      exact congrArg (fun e : ℕ => 2 ^ e % 3) hk
    _ = ((2 ^ 2) ^ (k / 2) * 2 ^ (k % 2)) % 3 := by
      rw [pow_add, pow_mul]
    _ = 2 ^ (k % 2) % 3 := by
      rw [Nat.mul_mod, Nat.pow_mod]
      norm_num

/-- A good exponent must be even: an odd exponent already has units digit `2`. -/
theorem goodExponent_even (k : ℕ) (hgood : goodExponent k) :
    k % 2 = 0 := by
  have hmodlt : k % 2 < 2 := Nat.mod_lt _ (by decide)
  by_contra hodd
  have hmod : k % 2 = 1 := by omega
  have htwo : 2 ^ k % 3 = 2 := by
    rw [two_pow_mod_three, hmod]
    decide
  have hpos : 0 < (2 : ℕ) ^ k := by positivity
  have hmember : 2 ^ k % 3 ∈ Nat.digits 3 (2 ^ k) := by
    rw [Nat.digits_of_two_le_of_pos (by decide : 2 ≤ 3) hpos]
    exact List.mem_cons_self
  rw [htwo] at hmember
  exact (goodExponent_iff_two_absent _).mp hgood hmember

theorem goodExponent_even' (k : ℕ) (hgood : goodExponent k) : Even k := by
  exact (even_iff_two_dvd).mpr (Nat.dvd_of_mod_eq_zero (goodExponent_even k hgood))

/-- The three known good exponents, checked by reduction in the kernel. -/
theorem goodExponent_zero : goodExponent 0 := by decide +kernel

theorem goodExponent_two : goodExponent 2 := by decide +kernel

theorem goodExponent_eight : goodExponent 8 := by decide +kernel

theorem good_one : good 1 := ⟨⟨0, by norm_num⟩, goodExponent_zero⟩

theorem good_four : good 4 := ⟨⟨2, by norm_num⟩, goodExponent_two⟩

theorem good_256 : good 256 := ⟨⟨8, by norm_num⟩, goodExponent_eight⟩

/-- Factor out exactly the powers of three from `2^d - 1`.

Only existence of the first nonzero base-three digit is needed, not an LTE
formula for its position.  The positive even exponent ensures `r > 0`.
-/
theorem two_pow_even_step_factor (d : ℕ) (hd : 0 < d) (heven : d % 2 = 0) :
    ∃ r c : ℕ, 0 < r ∧ ¬3 ∣ c ∧ 2 ^ d = 1 + 3 ^ r * c := by
  have hmod : 2 ^ d % 3 = 1 := by
    rw [two_pow_mod_three, heven]
    decide
  have hlarge : 1 < 2 ^ d := Nat.one_lt_two_pow (by omega)
  have hnonzero : 2 ^ d - 1 ≠ 0 := by omega
  obtain ⟨r, c, hc, hfactor⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd hnonzero 3 (by decide)
  have hpow : 2 ^ d = 1 + 3 ^ r * c := by omega
  have hr : 0 < r := by
    by_contra h
    have hrzero : r = 0 := by omega
    rw [hrzero, pow_zero, one_mul] at hpow
    have hcmod : c % 3 ≠ 0 := by
      intro hcmod
      exact hc (Nat.dvd_of_mod_eq_zero hcmod)
    omega
  exact ⟨r, c, hr, hc, hpow⟩

/-- Multiplication by `1 + P*c` shifts the digit above `P` by `x*c`. -/
theorem first_digit_shift (x P c : ℕ) (hP : 0 < P) :
    x * (1 + P * c) / P % 3 = (x / P + x * c) % 3 := by
  have hx : x * (1 + P * c) = x + P * (x * c) := by ring
  rw [hx, Nat.add_mul_div_left _ _ hP]

/-- If `3` divides `P`, the quadratic term makes no contribution to that digit. -/
theorem second_digit_shift (x P c : ℕ) (hP : 0 < P) (hdiv : 3 ∣ P) :
    x * (1 + P * c) ^ 2 / P % 3 = (x / P + 2 * (x * c)) % 3 := by
  have hx : x * (1 + P * c) ^ 2 =
      x + P * (2 * (x * c) + P * x * c ^ 2) := by ring
  rw [hx, Nat.add_mul_div_left _ _ hP]
  have hzero : (P * x * c ^ 2) % 3 = 0 := by
    apply Nat.mod_eq_zero_of_dvd
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hdiv x) (c ^ 2)
  calc
    (x / P + (2 * (x * c) + P * x * c ^ 2)) % 3 =
        ((x / P + 2 * (x * c)) + P * x * c ^ 2) % 3 := by rw [add_assoc]
    _ = (x / P + 2 * (x * c)) % 3 := by
      rw [Nat.add_mod, hzero, add_zero, Nat.mod_mod]

/-- Three residues in a nonconstant progression modulo three include `2`. -/
theorem three_residues (q u : ℕ) (hu : u % 3 ≠ 0) :
    q % 3 = 2 ∨ (q + u) % 3 = 2 ∨ (q + 2 * u) % 3 = 2 := by
  have hq : q % 3 = 0 ∨ q % 3 = 1 ∨ q % 3 = 2 := by omega
  have hu' : u % 3 = 1 ∨ u % 3 = 2 := by omega
  rcases hq with hq | hq | hq <;> rcases hu' with hu' | hu' <;>
    norm_num [Nat.add_mod, Nat.mul_mod, hq, hu']

/-- Good exponents cannot form a nonconstant three-term arithmetic progression.

The units digit forces both `a` and `a+d` to be even, hence `d` to be even.
Write `2^d = 1 + 3^r*c`, where `r > 0` and `3 ∤ c`.  At digit position `r`,
the powers with exponents `a`, `a+d`, and `a+2d` have residues
`q`, `q+u`, and `q+2u` modulo three, with `u = 2^a*c` nonzero modulo three.
One of those digits must be `2`.
-/
theorem not_three_term_AP (a d : ℕ) (hd : 0 < d) :
    ¬(goodExponent a ∧ goodExponent (a + d) ∧ goodExponent (a + 2 * d)) := by
  rintro ⟨ha, hb, hcgood⟩
  have haeven := goodExponent_even a ha
  have hbeven := goodExponent_even (a + d) hb
  have hdeven : d % 2 = 0 := by
    simpa only [Nat.add_mod, haeven, zero_add, Nat.mod_mod] using hbeven
  have hamod : 2 ^ a % 3 = 1 := by
    rw [two_pow_mod_three, haeven]
    decide
  obtain ⟨r, c, hr, hc, hfactor⟩ := two_pow_even_step_factor d hd hdeven
  have hP : 0 < (3 : ℕ) ^ r := by positivity
  have hPdiv : 3 ∣ (3 : ℕ) ^ r := dvd_pow_self 3 (by omega)
  have hstepmod : 2 ^ a * c % 3 ≠ 0 := by
    rw [Nat.mul_mod, hamod, one_mul, Nat.mod_mod]
    intro hmod
    exact hc (Nat.dvd_of_mod_eq_zero hmod)
  have hfirst : 2 ^ (a + d) / 3 ^ r % 3 =
      (2 ^ a / 3 ^ r + 2 ^ a * c) % 3 := by
    rw [pow_add, hfactor]
    exact first_digit_shift _ _ _ hP
  have hsecond : 2 ^ (a + 2 * d) / 3 ^ r % 3 =
      (2 ^ a / 3 ^ r + 2 * (2 ^ a * c)) % 3 := by
    rw [pow_add, mul_comm 2 d, pow_mul, hfactor]
    exact second_digit_shift _ _ _ hP hPdiv
  rcases three_residues (2 ^ a / 3 ^ r) (2 ^ a * c) hstepmod with h | h | h
  · exact digits_good_digit_ne_two (2 ^ a) r ha h
  · exact digits_good_digit_ne_two (2 ^ (a + d)) r hb (hfirst.trans h)
  · exact digits_good_digit_ne_two (2 ^ (a + 2 * d)) r hcgood (hsecond.trans h)

/-- At least one exponent in every nonconstant three-term progression is bad. -/
theorem no_three_term_AP (a d : ℕ) (hd : 0 < d) :
    ¬goodExponent a ∨ ¬goodExponent (a + d) ∨ ¬goodExponent (a + 2 * d) := by
  by_contra h
  have hall : goodExponent a ∧ goodExponent (a + d) ∧ goodExponent (a + 2 * d) := by
    simpa only [not_or, not_not] using h
  exact not_three_term_AP a d hd hall

/-- The bad term can be witnessed by an actual base-three digit `2`. -/
theorem three_term_AP_has_digit_two (a d : ℕ) (hd : 0 < d) :
    2 ∈ Nat.digits 3 (2 ^ a) ∨
      2 ∈ Nat.digits 3 (2 ^ (a + d)) ∨
      2 ∈ Nat.digits 3 (2 ^ (a + 2 * d)) := by
  simpa only [goodExponent_iff_two_absent, not_not] using no_three_term_AP a d hd

end Erdos406.Arithmetic
