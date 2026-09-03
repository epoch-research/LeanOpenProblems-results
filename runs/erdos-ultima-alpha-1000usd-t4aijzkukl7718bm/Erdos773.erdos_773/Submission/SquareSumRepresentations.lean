import Submission.GaussianDivisorBound

/-!
Uniform subpower estimates for representations as a sum of two positive
squares. These supply the same-side case of square-collision codegrees.
-/
namespace Erdos773.SquareSumRepresentations
open Finset Filter UniqueFactorizationMonoid GaussianDivisorBound
set_option maxHeartbeats 1000000

noncomputable local instance : NormalizationMonoid GaussianInt :=
  UniqueFactorizationMonoid.normalizationMonoid

/-- Positive first-quadrant Gaussian integers have no distinct associates. -/
lemma eq_of_associated_positive {z w : GaussianInt}
    (hzr : 0 < z.re) (hzi : 0 < z.im) (hwr : 0 < w.re) (hwi : 0 < w.im)
    (h : Associated z w) : z = w := by
  obtain ⟨u, hu⟩ := h
  have hn : (u : GaussianInt).norm = 1 :=
    (Zsqrtd.norm_eq_one_iff' (by norm_num) _).mpr u.isUnit
  have hs : (u : GaussianInt).re ^ 2 + (u : GaussianInt).im ^ 2 = 1 := by
    simpa [Zsqrtd.norm, pow_two] using hn
  have hr : -1 ≤ (u : GaussianInt).re ∧ (u : GaussianInt).re ≤ 1 := by
    constructor <;> nlinarith [sq_nonneg (u : GaussianInt).im]
  have hi : -1 ≤ (u : GaussianInt).im ∧ (u : GaussianInt).im ≤ 1 := by
    constructor <;> nlinarith [sq_nonneg (u : GaussianInt).re]
  have hre := congrArg Zsqrtd.re hu
  have him := congrArg Zsqrtd.im hu
  simp only [Zsqrtd.re_mul, Zsqrtd.im_mul] at hre him
  have he : (u : GaussianInt).re = 1 ∧ (u : GaussianInt).im = 0 := by
    rcases (by omega : (u : GaussianInt).re = -1 ∨ (u : GaussianInt).re = 0 ∨
      (u : GaussianInt).re = 1) with h | h | h <;> rw [h] at hs hre him
    · have : (u : GaussianInt).im = 0 := by nlinarith
      simp [this] at hre
      omega
    · rcases (by nlinarith [sq_nonneg ((u : GaussianInt).im - 1),
          sq_nonneg ((u : GaussianInt).im + 1)] :
          (u : GaussianInt).im = -1 ∨ (u : GaussianInt).im = 1) with hi' | hi'
      · simp [hi'] at him
        omega
      · simp [hi'] at hre
        omega
    · exact ⟨h, by nlinarith⟩
  apply Zsqrtd.ext <;> simp_all

/-- Ordered positive representations, with a root-height cutoff. -/
def reps (N T : ℕ) : Finset (ℕ × ℕ) :=
  ((Icc 1 N) ×ˢ (Icc 1 N)).filter (fun p => p.1 ^ 2 + p.2 ^ 2 = T)

def gaussianPair (p : ℕ × ℕ) : GaussianInt := ⟨p.1, p.2⟩

lemma gaussianPair_norm (p : ℕ × ℕ) :
    (gaussianPair p).norm = (p.1 ^ 2 + p.2 ^ 2 : ℕ) := by
  simp [gaussianPair, Zsqrtd.norm, pow_two]

lemma gaussianPair_ne_zero {N T : ℕ} {p : ℕ × ℕ} (hp : p ∈ reps N T) :
    gaussianPair p ≠ 0 := by
  have hpos := (mem_Icc.mp (mem_product.mp (mem_filter.mp hp).1).1).1
  intro h
  have hh := congrArg Zsqrtd.re h
  simp [gaussianPair] at hh
  omega

/-- Inject each representation into the prime-factor submultisets of T
in the Gaussian integers. Positivity makes the injection unit-free. -/
theorem reps_card_le_factor_submultisets (N T : ℕ) (hT : 0 < T) :
    (reps N T).card ≤ (Iic (normalizedFactors (T : GaussianInt))).card := by
  classical
  apply card_le_card_of_injOn (fun p => normalizedFactors (gaussianPair p))
  · intro p hp
    have hn : (gaussianPair p).norm = T := by rw [gaussianPair_norm, (mem_filter.mp hp).2]
    have hd : gaussianPair p ∣ (T : GaussianInt) := by
      refine ⟨star (gaussianPair p), ?_⟩
      have hh := Zsqrtd.norm_eq_mul_conj (gaussianPair p)
      simpa [hn] using hh
    exact mem_Iic.mpr ((dvd_iff_normalizedFactors_le_normalizedFactors
      (gaussianPair_ne_zero hp) (by exact_mod_cast hT.ne')).mp hd)
  · intro p hp q hq he
    have ha := (associated_iff_normalizedFactors_eq_normalizedFactors
      (gaussianPair_ne_zero hp) (gaussianPair_ne_zero hq)).mpr he
    have hpp := mem_product.mp (mem_filter.mp hp).1
    have hqp := mem_product.mp (mem_filter.mp hq).1
    have hh : gaussianPair p = gaussianPair q := eq_of_associated_positive
      (by change (0 : ℤ) < p.1; exact_mod_cast (Nat.lt_of_succ_le (mem_Icc.mp hpp.1).1)) (by change (0 : ℤ) < p.2; exact_mod_cast (Nat.lt_of_succ_le (mem_Icc.mp hpp.2).1))
      (by change (0 : ℤ) < q.1; exact_mod_cast (Nat.lt_of_succ_le (mem_Icc.mp hqp.1).1)) (by change (0 : ℤ) < q.2; exact_mod_cast (Nat.lt_of_succ_le (mem_Icc.mp hqp.2).1)) ha
    apply Prod.ext
    · have he := congrArg Zsqrtd.re hh
      simpa [gaussianPair] using he
    · have he := congrArg Zsqrtd.im hh
      simpa [gaussianPair] using he

/-- The representation count is subpower in the represented integer,
uniformly in the cutoff N. -/
theorem reps_subpower (δ : ℝ) (hδ : 0 < δ) :
    ∃ C > (0 : ℝ), ∀ N T : ℕ, 0 < T →
      ((reps N T).card : ℝ) ≤ C * (T : ℝ) ^ δ := by
  obtain ⟨C,hC,hb⟩ := factor_submultisets_subpower (δ/2) (by linarith)
  refine ⟨C,hC,fun N T hT => ?_⟩
  have hnorm : gNorm (T : GaussianInt) = T ^ 2 := by
    simp [gNorm_eq, Zsqrtd.norm_natCast, pow_two, Int.natAbs_mul]
  calc
    _ ≤ ((Iic (normalizedFactors (T : GaussianInt))).card : ℝ) := by
      exact_mod_cast reps_card_le_factor_submultisets N T hT
    _ ≤ C * (gNorm (T : GaussianInt) : ℝ) ^ (δ/2) :=
      hb _ (by exact_mod_cast hT.ne')
    _ = C * (T : ℝ) ^ δ := by
      rw [hnorm, Nat.cast_pow, ← Real.rpow_natCast_mul (Nat.cast_nonneg T)]
      congr 2
      push_cast
      ring

/-- Root-height version, covering every positive sum at most 2*N^2. -/
theorem reps_height_subpower (δ : ℝ) (hδ : 0 < δ) :
    ∃ C > (0 : ℝ), ∀ N T : ℕ, 0 < T → T ≤ 2*N^2 →
      ((reps N T).card : ℝ) ≤ C * (N : ℝ) ^ δ := by
  obtain ⟨C,hC,hb⟩ := reps_subpower (δ/2) (by linarith)
  refine ⟨C * 2^(δ/2), by positivity,fun N T hT hTN => ?_⟩
  have hh : (T : ℝ) ≤ 2 * (N : ℝ)^2 := by exact_mod_cast hTN
  calc
    _ ≤ C * (T : ℝ)^(δ/2) := hb N T hT
    _ ≤ C * (2 * (N : ℝ)^2)^(δ/2) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hh (by linarith)) hC.le
    _ = C * 2^(δ/2) * (N : ℝ)^δ := by
      rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (by positivity),
        ← Real.rpow_natCast_mul (Nat.cast_nonneg N)]
      norm_num only [Nat.cast_ofNat]
      rw [show (2 : ℝ)*(δ/2)=δ by ring]
      ring

#print axioms eq_of_associated_positive
#print axioms reps_card_le_factor_submultisets
#print axioms reps_subpower
#print axioms reps_height_subpower
end Erdos773.SquareSumRepresentations
