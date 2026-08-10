import FormalConjectures.Util.ProblemImports

open Nat

namespace Zd2

/-- The ring `ℤ[√-2]`. -/
abbrev Z2 := Zsqrtd (-2)

-- sanity: norm is a^2 + 2 b^2
example (z : Z2) : z.norm = z.re * z.re - (-2) * z.im * z.im := Zsqrtd.norm_def z

example (z : Z2) : 0 ≤ z.norm := Zsqrtd.norm_nonneg (by norm_num) z

-- division by rounding rational coordinates
instance : Div Z2 :=
  ⟨fun x y => ⟨round ((x * star y).re / y.norm : ℚ), round ((x * star y).im / y.norm : ℚ)⟩⟩

theorem div_def (x y : Z2) :
    x / y = ⟨round ((x * star y).re / y.norm : ℚ), round ((x * star y).im / y.norm : ℚ)⟩ :=
  rfl

instance : Mod Z2 := ⟨fun x y => x - y * (x / y)⟩

theorem mod_def (x y : Z2) : x % y = x - y * (x / y) := rfl

/-- Rounding bound: `|a - n·round(a/n)| ≤ n/2`, squared form. -/
theorem round_bound (a n : ℤ) (hn : 0 < n) :
    4 * (a - n * round ((a : ℚ) / n)) ^ 2 ≤ n ^ 2 := by
  set r : ℤ := a - n * round ((a : ℚ) / n) with hr
  have hnQ : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have hrQ : (r : ℚ) = n * ((a : ℚ) / n - round ((a : ℚ) / n)) := by
    rw [hr]; push_cast; field_simp
  have h2 : |((a : ℚ) / n - round ((a : ℚ) / n))| ≤ 1 / 2 := abs_sub_round _
  have hrabs : |(r : ℚ)| ≤ (n : ℚ) / 2 := by
    rw [hrQ, abs_mul]
    have : |(n : ℚ)| = n := by rw [abs_of_pos]; exact_mod_cast hn
    rw [this]
    calc (n : ℚ) * |((a : ℚ) / n - round ((a : ℚ) / n))| ≤ (n : ℚ) * (1/2) := by
          apply mul_le_mul_of_nonneg_left h2; exact_mod_cast hn.le
      _ = (n : ℚ)/2 := by ring
  -- now 2|r| ≤ n in ℚ, hence (2r)^2 ≤ n^2
  have h2r : (2 * |(r:ℚ)|) ≤ n := by linarith
  have hsq : (2 * (r:ℚ))^2 ≤ (n:ℚ)^2 := by
    have h0 : (0:ℚ) ≤ 2 * |(r:ℚ)| := by positivity
    have := mul_le_mul h2r h2r (by positivity) (by exact_mod_cast hn.le)
    calc (2 * (r:ℚ))^2 = (2 * |(r:ℚ)|)^2 := by rw [mul_pow, mul_pow, sq_abs]
      _ ≤ (n:ℚ) * n := by nlinarith [abs_nonneg (r:ℚ)]
      _ = (n:ℚ)^2 := by ring
  have : (4 * (r:ℚ)^2) ≤ (n:ℚ)^2 := by nlinarith [hsq]
  have hcast : ((4 * r^2 : ℤ) : ℚ) ≤ ((n^2 : ℤ) : ℚ) := by push_cast; linarith
  exact_mod_cast hcast

theorem norm_pos {y : Z2} (hy : y ≠ 0) : 0 < y.norm := by
  rcases lt_or_eq_of_le (Zsqrtd.norm_nonneg (by norm_num) y) with h | h
  · exact h
  · exact absurd ((Zsqrtd.norm_eq_zero_iff (by norm_num) y).1 h.symm) hy

theorem key_eq (x y : Z2) :
    (x % y) * star y = (x * star y) - (↑(y.norm)) * (x / y) := by
  rw [mod_def, sub_mul, mul_assoc, mul_comm (x/y) (star y), ← mul_assoc,
     Zsqrtd.norm_eq_mul_conj]

theorem norm_mod_lt (x : Z2) {y : Z2} (hy : y ≠ 0) : (x % y).norm < y.norm := by
  set n : ℤ := y.norm with hn_def
  have hn : 0 < n := norm_pos hy
  set t : Z2 := x * star y with ht
  -- coordinates of the remainder times conjugate
  have hqre : (x / y).re = round ((t.re : ℚ) / n) := rfl
  have hqim : (x / y).im = round ((t.im : ℚ) / n) := rfl
  have hcoeff_re : ((↑n : Z2) * (x / y)).re = n * round ((t.re : ℚ) / n) := by
    rw [Zsqrtd.re_mul, Zsqrtd.re_intCast, Zsqrtd.im_intCast, hqre]; ring
  have hcoeff_im : ((↑n : Z2) * (x / y)).im = n * round ((t.im : ℚ) / n) := by
    rw [Zsqrtd.im_mul, Zsqrtd.re_intCast, Zsqrtd.im_intCast, hqim]; ring
  have hre : ((x % y) * star y).re = t.re - n * round ((t.re : ℚ) / n) := by
    rw [key_eq, ← ht, ← hn_def, Zsqrtd.re_sub, hcoeff_re]
  have him : ((x % y) * star y).im = t.im - n * round ((t.im : ℚ) / n) := by
    rw [key_eq, ← ht, ← hn_def, Zsqrtd.im_sub, hcoeff_im]
  -- norm relation
  have hnorm : (x % y).norm * n = ((x % y) * star y).norm := by
    rw [Zsqrtd.norm_mul, Zsqrtd.norm_conj]
  have hexp : ((x % y) * star y).norm
      = (t.re - n * round ((t.re : ℚ) / n))^2 + 2 * (t.im - n * round ((t.im : ℚ) / n))^2 := by
    rw [Zsqrtd.norm_def, hre, him]; ring
  have hb1 := round_bound t.re n hn
  have hb2 := round_bound t.im n hn
  have hnn : 0 ≤ (x % y).norm := Zsqrtd.norm_nonneg (by norm_num) _
  nlinarith [hnorm, hexp, hb1, hb2, hn, hnn]

theorem norm_le_norm_mul_left (a : Z2) {b : Z2} (hb : b ≠ 0) :
    (a.norm).natAbs ≤ (a * b).norm.natAbs := by
  rw [Zsqrtd.norm_mul, Int.natAbs_mul]
  apply Nat.le_mul_of_pos_right
  have : 0 < b.norm := norm_pos hb
  omega

instance : EuclideanDomain Z2 where
  quotient := (· / ·)
  remainder := (· % ·)
  quotient_mul_add_remainder_eq := fun x y => by rw [mod_def]; ring
  quotient_zero := by intro x; apply Zsqrtd.ext <;> simp [div_def]
  r := fun a b => a.norm.natAbs < b.norm.natAbs
  r_wellFounded := (measure (Int.natAbs ∘ Zsqrtd.norm)).wf
  remainder_lt := fun x {y} hy => by
    have := norm_mod_lt x hy
    have h1 : 0 ≤ (x % y).norm := Zsqrtd.norm_nonneg (by norm_num) _
    have h2 : 0 ≤ y.norm := Zsqrtd.norm_nonneg (by norm_num) _
    omega
  mul_left_not_lt := fun a {b} hb => by
    have := norm_le_norm_mul_left a hb
    omega

end Zd2
