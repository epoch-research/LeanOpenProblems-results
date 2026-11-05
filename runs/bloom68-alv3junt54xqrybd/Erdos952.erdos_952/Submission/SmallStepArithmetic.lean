import FormalConjecturesUtil

/-! Arithmetic and finite-exception lemmas for the small-step Gaussian-prime obstruction. -/

namespace GaussianSmallStep.Arithmetic

theorem norm_eq_sum_sq (z : GaussianInt) : z.norm = z.re ^ 2 + z.im ^ 2 := by
  simp [Zsqrtd.norm, pow_two]

theorem norm_cast (z : GaussianInt) (p : ℕ) :
    (z.norm : ZMod p) = (z.re : ZMod p) ^ 2 + (z.im : ZMod p) ^ 2 := by
  rw [norm_eq_sum_sq]
  push_cast
  rfl

/-- Exact division by a Gaussian factor, witnessed by the conjugate coordinates. -/
theorem dvd_of_conjugate_coordinates (z f : GaussianInt) (hf : f ≠ 0)
    (hr : f.norm ∣ (z * star f).re) (hi : f.norm ∣ (z * star f).im) : f ∣ z := by
  let q : GaussianInt := ⟨(z * star f).re / f.norm, (z * star f).im / f.norm⟩
  have hq : q * (f.norm : GaussianInt) = z * star f := by
    apply Zsqrtd.ext
    · simpa [q] using Int.ediv_mul_cancel hr
    · simpa [q] using Int.ediv_mul_cancel hi
  refine ⟨q, ?_⟩
  have he : (f * q) * star f = z * star f := by
    calc
      (f * q) * star f = q * (f.norm : GaussianInt) := by
        rw [Zsqrtd.norm_eq_mul_conj]
        ring
      _ = z * star f := hq
  have hf' : star f ≠ 0 := by simpa using hf
  exact (mul_right_cancel₀ hf' he).symm

/-- The modular form of the same exact division criterion. -/
theorem dvd_factor_of_modular_coordinates (z : GaussianInt) (k l : ℤ) (p : ℕ)
    (hp : (⟨k, l⟩ : GaussianInt).norm = p) (hpos : 0 < p)
    (hr : (k : ZMod p) * (z.re : ZMod p) + (l : ZMod p) * (z.im : ZMod p) = 0)
    (hi : (k : ZMod p) * (z.im : ZMod p) - (l : ZMod p) * (z.re : ZMod p) = 0) :
    (⟨k, l⟩ : GaussianInt) ∣ z := by
  apply dvd_of_conjugate_coordinates
  · apply GaussianInt.norm_pos.mp
    rw [hp]
    exact_mod_cast hpos
  · rw [hp]
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
    simpa [Zsqrtd.re_mul, Zsqrtd.re_star, Zsqrtd.im_star, mul_comm] using hr
  · rw [hp]
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
    simpa [Zsqrtd.im_mul, Zsqrtd.re_star, Zsqrtd.im_star, mul_comm, sub_eq_add_neg, add_comm] using hi

/-- A nonunit divisor of a prime has the same Gaussian squared norm. -/
theorem prime_norm_eq_of_dvd {z f : GaussianInt} (hz : Prime z)
    (hf : f.norm ≠ 1) (h : f ∣ z) : z.norm = f.norm := by
  have hfu : ¬ IsUnit f := by
    intro hu
    exact hf ((Zsqrtd.norm_eq_one_iff' (by decide) f).mpr hu)
  exact Zsqrtd.norm_eq_of_associated (by decide)
    ((hz.irreducible.dvd_iff.mp h).resolve_left hfu)

/-- Consequently, primes of norm above 13 have none of the small nonunit factors. -/
theorem large_prime_not_dvd {z : GaussianInt} (hz : Prime z) (hn : 13 < z.norm)
    (f : GaussianInt) (hlo : 1 < f.norm) (hhi : f.norm ≤ 13) : ¬ f ∣ z := by
  intro h
  have he := prime_norm_eq_of_dvd hz (ne_of_gt hlo) h
  omega

private theorem check_two : ∀ a b : ZMod 2,
    a ^ 2 + b ^ 2 = 0 → a + b = 0 ∧ b - a = 0 := by decide

private theorem check_five : ∀ a b : ZMod 5,
    a ^ 2 + b ^ 2 = 0 →
      (2 * a + b = 0 ∧ 2 * b - a = 0) ∨ (2 * a - b = 0 ∧ 2 * b + a = 0) := by decide

private theorem check_thirteen : ∀ a b : ZMod 13,
    a ^ 2 + b ^ 2 = 0 →
      (3 * a + 2 * b = 0 ∧ 3 * b - 2 * a = 0) ∨
      (3 * a - 2 * b = 0 ∧ 3 * b + 2 * a = 0) := by decide

private theorem check_parity : ∀ a b : ZMod 2,
    a ^ 2 + b ^ 2 ≠ 0 → a + b - 1 = 0 ∧ b - a + 1 = 0 := by decide

theorem prime_norm_ne_zero_two {z : GaussianInt} (hz : Prime z) (hn : 13 < z.norm) :
    (z.norm : ZMod 2) ≠ 0 := by
  intro h
  rw [norm_cast] at h
  obtain ⟨hr, hi⟩ := check_two _ _ h
  apply large_prime_not_dvd hz hn (⟨1, 1⟩ : GaussianInt)
    (by norm_num [Zsqrtd.norm]) (by norm_num [Zsqrtd.norm])
  apply dvd_factor_of_modular_coordinates z 1 1 2
    (by norm_num [Zsqrtd.norm]) (by decide)
  · simpa using hr
  · simpa using hi

theorem prime_norm_ne_zero_five {z : GaussianInt} (hz : Prime z) (hn : 13 < z.norm) :
    (z.norm : ZMod 5) ≠ 0 := by
  intro h
  rw [norm_cast] at h
  rcases check_five _ _ h with h | h
  · apply large_prime_not_dvd hz hn (⟨2, 1⟩ : GaussianInt)
      (by norm_num [Zsqrtd.norm]) (by norm_num [Zsqrtd.norm])
    apply dvd_factor_of_modular_coordinates z 2 1 5
      (by norm_num [Zsqrtd.norm]) (by decide)
    · simpa using h.1
    · simpa using h.2
  · apply large_prime_not_dvd hz hn (⟨2, -1⟩ : GaussianInt)
      (by norm_num [Zsqrtd.norm]) (by norm_num [Zsqrtd.norm])
    apply dvd_factor_of_modular_coordinates z 2 (-1) 5
      (by norm_num [Zsqrtd.norm]) (by decide)
    · simpa [sub_eq_add_neg] using h.1
    · simpa [sub_eq_add_neg] using h.2

theorem prime_norm_ne_zero_thirteen {z : GaussianInt} (hz : Prime z) (hn : 13 < z.norm) :
    (z.norm : ZMod 13) ≠ 0 := by
  intro h
  rw [norm_cast] at h
  rcases check_thirteen _ _ h with h | h
  · apply large_prime_not_dvd hz hn (⟨3, 2⟩ : GaussianInt)
      (by norm_num [Zsqrtd.norm]) (by norm_num [Zsqrtd.norm])
    apply dvd_factor_of_modular_coordinates z 3 2 13
      (by norm_num [Zsqrtd.norm]) (by decide)
    · simpa using h.1
    · simpa using h.2
  · apply large_prime_not_dvd hz hn (⟨3, -2⟩ : GaussianInt)
      (by norm_num [Zsqrtd.norm]) (by norm_num [Zsqrtd.norm])
    apply dvd_factor_of_modular_coordinates z 3 (-2) 13
      (by norm_num [Zsqrtd.norm]) (by decide)
    · simpa [sub_eq_add_neg] using h.1
    · simpa [sub_eq_add_neg] using h.2

/-- Every Gaussian integer of odd squared norm is `1 + (1+i)w`. -/
theorem exists_normal_form (z : GaussianInt) (hn : (z.norm : ZMod 2) ≠ 0) :
    ∃ w : GaussianInt, z = 1 + (⟨1, 1⟩ : GaussianInt) * w := by
  rw [norm_cast] at hn
  obtain ⟨hr, hi⟩ := check_parity _ _ hn
  have hdiv : (⟨1, 1⟩ : GaussianInt) ∣ z - 1 := by
    apply dvd_factor_of_modular_coordinates (z - 1) 1 1 2
      (by norm_num [Zsqrtd.norm]) (by decide)
    · simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hr
    · simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hi
  obtain ⟨w, hw⟩ := hdiv
  refine ⟨w, ?_⟩
  calc
    z = 1 + (z - 1) := by abel
    _ = 1 + (⟨1, 1⟩ : GaussianInt) * w := by rw [hw]

/-- Norm-bounded sets of Gaussian integers are finite. -/
theorem finite_norm_le (B : ℤ) : {z : GaussianInt | z.norm ≤ B}.Finite := by
  let coords : GaussianInt → ℤ × ℤ := fun z => (z.re, z.im)
  have hc : Function.Injective coords := by
    intro z w h
    apply Zsqrtd.ext
    · exact congrArg Prod.fst h
    · exact congrArg Prod.snd h
  have hbox : (Set.Icc (-B - 1, -B - 1) (B + 1, B + 1)).Finite := Set.finite_Icc _ _
  apply (hbox.preimage hc.injOn).subset
  intro z hz
  change z.norm ≤ B at hz
  have hB : 0 ≤ B := (GaussianInt.norm_nonneg z).trans hz
  rw [norm_eq_sum_sq] at hz
  have hreSq : z.re ^ 2 ≤ (B + 1) ^ 2 := by nlinarith [sq_nonneg z.im, sq_nonneg B]
  have himSq : z.im ^ 2 ≤ (B + 1) ^ 2 := by nlinarith [sq_nonneg z.re, sq_nonneg B]
  have hpos : 0 ≤ B + 1 := by omega
  have hre := abs_le_of_sq_le_sq' hreSq hpos
  have him := abs_le_of_sq_le_sq' himSq hpos
  change (-B - 1 ≤ z.re ∧ -B - 1 ≤ z.im) ∧ (z.re ≤ B + 1 ∧ z.im ≤ B + 1)
  omega

/-- An injective sequence eventually avoids every fixed norm-bounded set. -/
theorem eventually_norm_gt (x : ℕ → GaussianInt) (hx : Function.Injective x) (B : ℤ) :
    ∃ N : ℕ, ∀ n : ℕ, B < (x (n + N)).norm := by
  have hs : (x ⁻¹' {z : GaussianInt | z.norm ≤ B}).Finite :=
    (finite_norm_le B).preimage hx.injOn
  obtain ⟨M, hM⟩ := hs.bddAbove
  refine ⟨M + 1, fun n => ?_⟩
  by_contra h
  have hle : n + (M + 1) ≤ M := hM (not_lt.mp h)
  omega

/-- Integer lattice steps of squared norm below two are zero or a nearest neighbor. -/
theorem norm_lt_two_cases (w : GaussianInt) (h : w.norm < 2) :
    w = 0 ∨ w = ⟨1, 0⟩ ∨ w = ⟨-1, 0⟩ ∨ w = ⟨0, 1⟩ ∨ w = ⟨0, -1⟩ := by
  rcases w with ⟨a, b⟩
  rw [norm_eq_sum_sq] at h
  have ha : a ^ 2 ≤ (1 : ℤ) ^ 2 := by
    change a ^ 2 + b ^ 2 < 2 at h
    nlinarith [sq_nonneg b]
  have hb : b ^ 2 ≤ (1 : ℤ) ^ 2 := by
    change a ^ 2 + b ^ 2 < 2 at h
    nlinarith [sq_nonneg a]
  have har := abs_le_of_sq_le_sq' ha (by norm_num)
  have hbr := abs_le_of_sq_le_sq' hb (by norm_num)
  rcases har with ⟨hal, hau⟩
  rcases hbr with ⟨hbl, hbu⟩
  interval_cases a <;> interval_cases b <;> norm_num at *
  rfl

/-- There is no Gaussian squared norm equal to three. -/
theorem norm_lt_four_iff_le_two (w : GaussianInt) : w.norm < 4 ↔ w.norm ≤ 2 := by
  constructor
  · intro h
    rcases w with ⟨a, b⟩
    rw [norm_eq_sum_sq] at h
    have ha : a ^ 2 < (2 : ℤ) ^ 2 := by
      change a ^ 2 + b ^ 2 < 4 at h
      nlinarith [sq_nonneg b]
    have hb : b ^ 2 < (2 : ℤ) ^ 2 := by
      change a ^ 2 + b ^ 2 < 4 at h
      nlinarith [sq_nonneg a]
    have har := abs_lt_of_sq_lt_sq' ha (by norm_num)
    have hbr := abs_lt_of_sq_lt_sq' hb (by norm_num)
    have hal : -1 ≤ a := by omega
    have hau : a ≤ 1 := by omega
    have hbl : -1 ≤ b := by omega
    have hbu : b ≤ 1 := by omega
    interval_cases a <;> interval_cases b <;> norm_num [Zsqrtd.norm]
  · intro h
    exact lt_of_le_of_lt h (by norm_num)

#print axioms prime_norm_ne_zero_two
#print axioms prime_norm_ne_zero_five
#print axioms prime_norm_ne_zero_thirteen
#print axioms exists_normal_form
#print axioms eventually_norm_gt
#print axioms norm_lt_two_cases
#print axioms norm_lt_four_iff_le_two

end GaussianSmallStep.Arithmetic
