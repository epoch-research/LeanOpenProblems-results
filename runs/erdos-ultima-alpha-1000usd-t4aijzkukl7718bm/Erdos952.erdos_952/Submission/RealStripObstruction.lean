import Submission.PeriodicCompositePatches
import Submission.IrrationalLatticeApproximation
import Submission.RationalStripObstruction

/-! Gaussian prime walks cannot remain in any straight strip, including
irrational slopes. This does not exclude walks that leave every straight strip. -/
namespace Erdos952Investigation
namespace RealStrip

set_option maxHeartbeats 0

lemma exists_irrational_crosscut {α : ℝ} (hα : Irrational α)
    (B : ℝ) (W : ℕ) (M : ℤ) :
    ∃ A : ℤ, M < A ∧ ∀ z : GaussianInt,
      |z.re - A| ≤ W → |(z.im : ℝ) - α*(z.re : ℝ)| ≤ B → ¬ Prime z := by
  obtain ⟨H, hH⟩ := exists_nat_gt (B + |α| *(W : ℝ) + 1)
  obtain ⟨a, P, hP, hpatch⟩ := PeriodicCompositePatches.periodic_rectangle W H
  obtain ⟨k, l, hfar, hnear⟩ := IrrationalLatticeApproximation.arbitrarily_far_grid_center
    hα (a : ℤ) (P : ℤ) (|M| + P + W + 1) (by exact_mod_cast hP)
  let A : ℤ := (a : ℤ) + (P : ℤ)*k
  let T : ℤ := (P : ℤ)*l
  have hbarrier (z : GaussianInt) (hr : |z.re - A| ≤ W)
      (hs : |(z.im : ℝ) - α*(z.re : ℝ)| ≤ B) : ¬ Prime z := by
    have hrreal : |(z.re : ℝ) - (A : ℝ)| ≤ W := by exact_mod_cast hr
    have hcalc : |(z.im : ℝ) - (T : ℝ)| < H := by
      have hdecomp : (z.im : ℝ) - (T : ℝ) =
          ((z.im : ℝ) - α*(z.re : ℝ)) + α*((z.re : ℝ) - (A : ℝ)) +
            (α*(A : ℝ) - (T : ℝ)) := by ring
      rw [hdecomp]
      have ht := abs_add_le ((z.im : ℝ) - α*(z.re : ℝ))
        (α*((z.re : ℝ) - (A : ℝ)))
      have ht' := abs_add_le (((z.im : ℝ) - α*(z.re : ℝ)) +
        α*((z.re : ℝ) - (A : ℝ))) (α*(A : ℝ) - (T : ℝ))
      have hm : |α*((z.re : ℝ) - (A : ℝ))| ≤ |α| *(W : ℝ) := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left hrreal (abs_nonneg α)
      change |α*(A : ℝ) - (T : ℝ)| < 1 at hnear
      linarith
    have hi : |z.im - T| ≤ H := by
      have ht : |z.im - T| < H := by exact_mod_cast hcalc
      exact ht.le
    have hn : (P : ℤ) < z.norm := by
      have ht : |A| ≤ |z.re - A| + |z.re| := by
        have ht := abs_add_le (A - z.re) z.re
        rw [abs_sub_comm A z.re] at ht
        simpa only [sub_add_cancel] using ht
      have hnorm := abs_re_le_gaussian_norm z
      change |M| + (P : ℤ) + W + 1 < |A| at hfar
      have := abs_nonneg M
      omega
    exact hpatch k l z hr hi hn
  by_cases hA : 0 ≤ A
  · refine ⟨A, ?_, hbarrier⟩
    change |M| + (P : ℤ) + W + 1 < |A| at hfar
    rw [abs_of_nonneg hA] at hfar
    have := le_abs_self M
    omega
  · refine ⟨-A, ?_, ?_⟩
    · change |M| + (P : ℤ) + W + 1 < |A| at hfar
      rw [abs_of_neg (lt_of_not_ge hA)] at hfar
      have := le_abs_self M
      omega
    · intro z hr hs hpz
      apply hbarrier (-z) ?_ ?_ hpz.neg
      · have he : (-z).re - A = -(z.re - -A) := by simp; ring
        rw [he, abs_neg]
        exact hr
      · have he : ((-z).im : ℝ) - α*((-z).re : ℝ) =
            -((z.im : ℝ) - α*(z.re : ℝ)) := by simp; ring
        rw [he, abs_neg]
        exact hs

lemma prime_walk_bounded_in_irrational_strip {α : ℝ} (hα : Irrational α)
    (x : ℕ → GaussianInt) (C : ℤ) (B : ℝ)
    (h : ∀ n, Prime (x n) ∧ (x (n + 1) - x n).norm < C)
    (hstrip : ∀ n, |((x n).im : ℝ) - α*((x n).re : ℝ)| ≤ B) :
    ∃ L : ℤ, ∀ n, (x n).norm ≤ L := by
  have hC : 0 < C := (GaussianInt.norm_nonneg _).trans_lt (h 0).2
  have hW : (C.toNat : ℤ) = C := Int.toNat_of_nonneg hC.le
  obtain ⟨A, hA, hfree⟩ := exists_irrational_crosscut hα B C.toNat |(x 0).re|
  have hApos : 0 < A := (abs_nonneg _).trans_lt hA
  have hnegstrip (n : ℕ) : |((-x n).im : ℝ) - α*((-x n).re : ℝ)| ≤ B := by
    have he : ((-x n).im : ℝ) - α*((-x n).re : ℝ) =
        -(((x n).im : ℝ) - α*((x n).re : ℝ)) := by simp; ring
    rw [he, abs_neg]
    exact hstrip n
  have hr (n : ℕ) : -A < (x n).re ∧ (x n).re < A := by
    induction n with
    | zero => exact abs_lt.mp hA
    | succ n ih =>
      have hs : |(x (n + 1)).re - (x n).re| < C :=
        (abs_re_le_gaussian_norm _).trans_lt (h n).2
      have hs' := abs_lt.mp hs
      constructor
      · by_contra hn
        apply hfree (-x (n + 1)) ?_ (hnegstrip (n + 1)) (h (n + 1)).1.neg
        rw [hW]
        simp only [Zsqrtd.re_neg]
        apply abs_le.mpr
        omega
      · by_contra hn
        apply hfree (x (n + 1)) ?_ (hstrip (n + 1)) (h (n + 1)).1
        rw [hW]
        apply abs_le.mpr
        omega
  obtain ⟨T, hT⟩ := exists_nat_gt (B + |α| *(A : ℝ))
  have hi (n : ℕ) : |(x n).im| ≤ (T : ℤ) := by
    have hrreal : |((x n).re : ℝ)| ≤ (A : ℝ) := by
      have ht := (abs_lt.mpr (hr n)).le
      exact_mod_cast ht
    have ht := abs_add_le (((x n).im : ℝ) - α*((x n).re : ℝ))
      (α*((x n).re : ℝ))
    rw [sub_add_cancel] at ht
    have hm : |α*((x n).re : ℝ)| ≤ |α| *(A : ℝ) := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hrreal (abs_nonneg α)
    have hib : |((x n).im : ℝ)| < (T : ℝ) := by have := hstrip n; linarith
    have hiZ : |(x n).im| < (T : ℤ) := by exact_mod_cast hib
    exact hiZ.le
  refine ⟨A^2 + (T : ℤ)^2, ?_⟩
  intro n
  have hr2 : (x n).re^2 ≤ A^2 := sq_le_sq.mpr (by
    rw [abs_of_pos hApos]
    exact (abs_lt.mpr (hr n)).le)
  have hi2 : (x n).im^2 ≤ (T : ℤ)^2 := sq_le_sq.mpr (by
    rw [abs_of_nonneg (Int.natCast_nonneg T)]
    exact hi n)
  rw [gaussian_norm_sq]
  omega

/-- Boundedness in a strip of arbitrary real slope. -/
theorem prime_walk_bounded_in_real_strip (α : ℝ)
    (x : ℕ → GaussianInt) (C : ℤ) (B : ℝ)
    (h : ∀ n, Prime (x n) ∧ (x (n + 1) - x n).norm < C)
    (hstrip : ∀ n, |((x n).im : ℝ) - α*((x n).re : ℝ)| ≤ B) :
    ∃ L : ℤ, ∀ n, (x n).norm ≤ L := by
  by_cases hα : Irrational α
  · exact prime_walk_bounded_in_irrational_strip hα x C B h hstrip
  obtain ⟨q, rfl⟩ := exists_rat_of_not_irrational hα
  let d : GaussianInt := ⟨q.den, -q.num⟩
  have hd : d ≠ 0 := by
    intro he
    have ht := congrArg Zsqrtd.re he
    change (q.den : ℤ) = 0 at ht
    exact q.den_nz (Int.natCast_eq_zero.mp ht)
  have hden : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
  obtain ⟨T, hT⟩ := exists_nat_gt ((q.den : ℝ)*B)
  apply RationalStrip.prime_walk_bounded_in_rational_strip d hd x C T h
  intro n
  have he : (((d * x n).im : ℤ) : ℝ) = (q.den : ℝ)*
      (((x n).im : ℝ) - (q : ℝ)*((x n).re : ℝ)) := by
    simp only [Zsqrtd.im_mul, d, Int.cast_add, Int.cast_mul, Int.cast_natCast,
      Int.cast_neg, Rat.cast_def]
    field_simp
    ring
  have hnorm : |(((d * x n).im : ℤ) : ℝ)| ≤ (T : ℝ) := by
    rw [he, abs_mul, abs_of_pos hden]
    exact (mul_le_mul_of_nonneg_left (hstrip n) hden.le).trans hT.le
  exact_mod_cast hnorm

/-- Any bounded nonzero real linear projection forces the entire walk to be bounded. -/
theorem prime_walk_bounded_in_real_projection (a b : ℝ) (hab : a ≠ 0 ∨ b ≠ 0)
    (x : ℕ → GaussianInt) (C : ℤ) (B : ℝ)
    (h : ∀ n, Prime (x n) ∧ (x (n + 1) - x n).norm < C)
    (hstrip : ∀ n, |a*((x n).re : ℝ) + b*((x n).im : ℝ)| ≤ B) :
    ∃ L : ℤ, ∀ n, (x n).norm ≤ L := by
  by_cases hb : b = 0
  · have ha : a ≠ 0 := hab.resolve_right (not_not.mpr hb)
    have haabs : 0 < |a| := abs_pos.mpr ha
    obtain ⟨T, hT⟩ := exists_nat_gt (B / |a|)
    let d : GaussianInt := ⟨0, 1⟩
    have hd : d ≠ 0 := by simp [d, Zsqrtd.ext_iff]
    apply RationalStrip.prime_walk_bounded_in_rational_strip d hd x C T h
    intro n
    have hcoord : |((x n).re : ℝ)| ≤ B / |a| := by
      apply (le_div_iff₀ haabs).mpr
      simpa [hb, abs_mul, mul_comm] using hstrip n
    have hcoord' : |(x n).re| ≤ (T : ℤ) := by exact_mod_cast (hcoord.trans hT.le)
    simpa [d, Zsqrtd.im_mul] using hcoord'
  · have hbabs : 0 < |b| := abs_pos.mpr hb
    apply prime_walk_bounded_in_real_strip (-a/b) x C (B / |b|) h
    intro n
    apply (le_div_iff₀ hbabs).mpr
    have he : a*((x n).re : ℝ) + b*((x n).im : ℝ) =
        b*(((x n).im : ℝ) - (-a/b)*((x n).re : ℝ)) := by
      field_simp
      ring
    have hs := hstrip n
    rw [he, abs_mul] at hs
    simpa only [mul_comm] using hs

/-- Every nonzero real linear projection of a hypothetical injective prime ray
is unbounded on every tail. The coefficients need not be rational. -/
theorem real_projection_unbounded (x : ℕ → GaussianInt) (C : ℤ)
    (hx : Function.Injective x)
    (h : ∀ n, Prime (x n) ∧ (x (n + 1) - x n).norm < C)
    (a b : ℝ) (hab : a ≠ 0 ∨ b ≠ 0) :
    ∀ N : ℕ, ∀ B : ℝ, ∃ n ≥ N, B < |a*((x n).re : ℝ) + b*((x n).im : ℝ)| := by
  intro N B
  by_contra! hbound
  let y : ℕ → GaussianInt := fun n => x (N + n)
  have hyinj : Function.Injective y := by
    intro i j he
    exact Nat.add_left_cancel (hx he)
  have hyp (n : ℕ) : Prime (y n) ∧ (y (n + 1) - y n).norm < C := by
    simpa only [y, Nat.add_assoc] using h (N + n)
  have hystrip (n : ℕ) : |a*((y n).re : ℝ) + b*((y n).im : ℝ)| ≤ B :=
    hbound (N + n) (Nat.le_add_right _ _)
  obtain ⟨L, hL⟩ := prime_walk_bounded_in_real_projection a b hab y C B hyp hystrip
  obtain ⟨n, hn⟩ := injective_escapes_norm y hyinj L
  have := hn n le_rfl
  have := hL n
  omega

/-- The corresponding affine-strip obstruction. -/
theorem not_in_real_affine_strip (x : ℕ → GaussianInt) (C : ℤ)
    (hx : Function.Injective x)
    (h : ∀ n, Prime (x n) ∧ (x (n + 1) - x n).norm < C)
    (a b c : ℝ) (hab : a ≠ 0 ∨ b ≠ 0) :
    ¬ ∃ B : ℝ, ∀ n, |a*((x n).re : ℝ) + b*((x n).im : ℝ) - c| ≤ B := by
  rintro ⟨B, hB⟩
  obtain ⟨n, _, hn⟩ := real_projection_unbounded x C hx h a b hab 0 (B + |c|)
  have ht := abs_add_le (a*((x n).re : ℝ) + b*((x n).im : ℝ) - c) c
  rw [sub_add_cancel] at ht
  have := hB n
  linarith

#print axioms prime_walk_bounded_in_real_strip
#print axioms prime_walk_bounded_in_real_projection
#print axioms real_projection_unbounded
#print axioms not_in_real_affine_strip

#print axioms exists_irrational_crosscut
#print axioms prime_walk_bounded_in_irrational_strip

end RealStrip
end Erdos952Investigation
