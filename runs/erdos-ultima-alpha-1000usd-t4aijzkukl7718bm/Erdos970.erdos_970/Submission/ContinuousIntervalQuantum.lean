import Submission.ContinuousIntervalCertificate

/-! Integer survivor thresholds give additional valid affine lower supports.
The normalized count is NOT rounded to an integer. Instead, a positive count
is at least one, and the normalization has a proved lower bound. This file
makes no assertion of uniform quadratic positivity. -/
namespace Erdos970.ContinuousInterval
open IntervalRescaling

/-- The reference density is a uniform lower bound on the normalization. -/
theorem density_le_normalization (p : ℕ → ℕ) (Q : ℕ → ℝ) (k : ℕ)
    (hp : ∀ i < k, 1 < p i)
    (hQ : ∀ i < k, 1 / (p i : ℝ) ≤ Q i ∧ Q i ≤ 1) :
    density Q k ≤ normalization p Q k := by
  apply Finset.prod_le_prod
  · intro i hi
    exact sub_nonneg.mpr (hQ i (Finset.mem_range.mp hi)).2
  · intro i hi
    have hi' := Finset.mem_range.mp hi
    have hpi : (1 : ℝ) < p i := by exact_mod_cast hp i hi'
    have hq : 1 / (p i : ℝ) < 1 := (div_lt_one (by linarith)).mpr hpi
    have hb := boost_bounds _ _ hq (hQ i hi').1 (hQ i hi').2
    have he := boost_identity (1 / (p i : ℝ)) (Q i) hq
    have hmul : 0 ≤ (1 - boost (1 / (p i : ℝ)) (Q i)) * (1 / (p i : ℝ)) :=
      mul_nonneg (sub_nonneg.mpr hb.2) (by positivity)
    linarith

lemma Regular.max_affine {d : ℝ} {L U : ℝ → ℝ} (h : Regular d L U)
    (s z : ℝ) (hs0 : 0 ≤ s) (hsd : s ≤ d) (hz : 0 ≤ z) :
    Regular d (fun x => max (L x) (s * (x - z))) U := by
  have hconv : ConvexOn ℝ Set.univ (fun x : ℝ => s * (x - z)) := by
    convert ((convexOn_id (𝕜 := ℝ) convex_univ).smul hs0).add_const (-s * z) using 1
    funext x
    simp only [smul_eq_mul, Pi.add_apply, id_eq]
    ring
  refine ⟨h.density_nonneg, fun x => (h.lower_nonneg x).trans (le_max_left _ _),
    ?_, h.lower_convex.sup hconv, ?_, ?_, h.upper_zero, h.upper_concave, h.upper_growth⟩
  · intro x hx
    rw [h.lower_zero x hx]
    exact max_eq_left (mul_nonpos_of_nonneg_of_nonpos hs0 (by linarith))
  · intro x y hxy
    exact max_le_max (h.lower_mono hxy)
      (mul_le_mul_of_nonneg_left (by linarith) hs0)
  · intro x y hxy
    apply (max_sub_max_le_max (L y) (s * (y - z)) (L x) (s * (x - z))).trans
    apply max_le (h.lower_lip x y hxy)
    nlinarith [mul_nonneg (sub_nonneg.mpr hsd) (sub_nonneg.mpr hxy)]

noncomputable def quantumFactor (d a : ℝ) : ℝ := d / (d - a)

lemma quantumFactor_bounds {d a : ℝ} (hd : 0 < d) (ha : a ≤ 0) :
    0 < quantumFactor d a ∧ quantumFactor d a ≤ 1 := by
  have hden : 0 < d - a := by linarith
  exact ⟨div_pos hd hden, (div_le_one hden).mpr (by linarith)⟩

lemma quantumFactor_identity {d a : ℝ} (hd : 0 < d) (ha : a ≤ 0) :
    quantumFactor d a * a + (1 - quantumFactor d a) * d = 0 := by
  have hden : d - a ≠ 0 := ne_of_gt (by linarith)
  dsimp [quantumFactor]
  field_simp
  ring

/-- The affine support being strengthened is `s*(x-(g-1))+a`, where `a<=0`.
The new support vanishes at `g-1` and has a slightly reduced slope. -/
noncomputable def quantumPatch (d : ℝ) (g : ℕ) (s a : ℝ)
    (L : ℝ → ℝ) (x : ℝ) : ℝ :=
  max (L x) (quantumFactor d a * s * (x - ((g : ℝ) - 1)))

lemma Regular.quantumPatch {d : ℝ} {L U : ℝ → ℝ} (h : Regular d L U)
    (g : ℕ) (s a : ℝ) (hd : 0 < d) (hg : 0 < g)
    (hs0 : 0 ≤ s) (hsd : s ≤ d) (ha : a ≤ 0) :
    Regular d (quantumPatch d g s a L) U := by
  have he := quantumFactor_bounds hd ha
  have hsd' : quantumFactor d a * s ≤ d :=
    (mul_le_mul_of_nonneg_right he.2 hs0).trans (by simpa using hsd)
  exact h.max_affine _ _ (mul_nonneg he.1.le hs0) hsd'
    (by
      have hgR : (1 : ℝ) ≤ g := by exact_mod_cast hg
      linarith)

/-- Positivity of a normalized certificate forces the actual integer count to
be at least one. Monotonicity in length then gives the threshold `d` at all
longer lengths. No integrality of the normalized count is assumed. -/
lemma IntervalBounds.normalized_ge_density_of_positive
    {d α : ℝ} {L U : ℝ → ℝ} {p : ℕ → ℕ} {k g : ℕ}
    (h : IntervalBounds L U α p k) (hda : d ≤ α) (hd : 0 ≤ d)
    (hpos : 0 < L g) (m : ℕ) (hgm : g ≤ m) (r : ℕ → ℕ) :
    d ≤ α * (count p r k m : ℝ) := by
  have hc : 0 < count p r k g := by
    by_contra hn
    have hz : count p r k g = 0 := by omega
    have hh := hpos.trans_le (h g r).1
    simp [hz] at hh
  have hm : (1 : ℝ) ≤ count p r k m := by
    exact_mod_cast (show 1 ≤ count p r k m from
      (show 1 ≤ count p r k g by omega).trans (count_mono_length p r k hgm))
  exact hda.trans (by nlinarith [mul_nonneg (hd.trans hda) (sub_nonneg.mpr hm)])

/-- A convex combination of the old affine bound and the integer threshold
produces a new affine support. At shorter natural lengths its value is nonpositive. -/
theorem IntervalBounds.quantumPatch {d α : ℝ} {L U : ℝ → ℝ}
    {p : ℕ → ℕ} {k : ℕ} (h : IntervalBounds L U α p k)
    (g : ℕ) (s a : ℝ) (hd : 0 < d) (hda : d ≤ α) (ha : a ≤ 0)
    (hs0 : 0 ≤ s) (hpos : 0 < L g)
    (hsupport : ∀ n : ℕ, s * ((n : ℝ) - ((g : ℝ) - 1)) + a ≤ L n) :
    IntervalBounds (quantumPatch d g s a L) U α p k := by
  have he := quantumFactor_bounds hd ha
  have hid := quantumFactor_identity hd ha
  intro m r
  refine ⟨max_le (h m r).1 ?_, (h m r).2⟩
  by_cases hmg : m < g
  · have hmR : (m : ℝ) ≤ (g : ℝ) - 1 := by
      have hh : (m : ℝ) + 1 ≤ g := by exact_mod_cast hmg
      linarith
    have hn : quantumFactor d a * s * ((m : ℝ) - ((g : ℝ) - 1)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (mul_nonneg he.1.le hs0) (sub_nonpos.mpr hmR)
    exact hn.trans (mul_nonneg (hd.le.trans hda) (Nat.cast_nonneg _))
  · have hg := h.normalized_ge_density_of_positive hda hd.le hpos m (by omega) r
    have hl := (hsupport m).trans (h m r).1
    have h1 := mul_le_mul_of_nonneg_left hl he.1.le
    have h2 := mul_le_mul_of_nonneg_left hg (sub_nonneg.mpr he.2)
    nlinarith

/-- The chord on the NEXT unit cell supplies an old affine support at all
natural lengths. Its slope and value at the preceding integer determine the patch. -/
def quantumSlope (L : ℝ → ℝ) (g : ℕ) : ℝ := L ((g : ℝ) + 1) - L g

def quantumIntercept (L : ℝ → ℝ) (g : ℕ) : ℝ := L g - quantumSlope L g

lemma Regular.quantumSlope_bounds {d : ℝ} {L U : ℝ → ℝ} (h : Regular d L U) (g : ℕ) :
    0 ≤ quantumSlope L g ∧ quantumSlope L g ≤ d := by
  exact ⟨sub_nonneg.mpr (h.lower_mono (by linarith)),
    by simpa [quantumSlope] using h.lower_lip (g : ℝ) ((g : ℝ) + 1) (by linarith)⟩

lemma quantum_support_nat {d : ℝ} {L U : ℝ → ℝ} (h : Regular d L U) (g n : ℕ) :
    quantumSlope L g * ((n : ℝ) - ((g : ℝ) - 1)) + quantumIntercept L g ≤ L n := by
  have hh := chord_le_outside h.lower_convex (g : ℝ) (n : ℝ)
    (Set.mem_univ _) (Set.mem_univ _) (Set.mem_univ _) (nat_outside_unit g n)
  dsimp [chord, quantumSlope, quantumIntercept] at hh ⊢
  linarith

lemma Regular.quantumIntercept_nonpos {d : ℝ} {L U : ℝ → ℝ} (h : Regular d L U)
    (g : ℕ) (hg : 0 < g) (hz : L ((g - 1 : ℕ) : ℝ) = 0) :
    quantumIntercept L g ≤ 0 := by
  have hh := quantum_support_nat h g (g - 1)
  have he : ((g - 1 : ℕ) : ℝ) = (g : ℝ) - 1 := by
    rw [Nat.cast_sub (show 1 ≤ g by omega), Nat.cast_one]
  rw [he] at hz hh
  simpa only [sub_self, mul_zero, zero_add, hz] using hh

/-- A complete soundness and regularity package for the concrete integer-threshold
patch at the first positive natural length. -/
theorem quantum_cell_certificate {d α : ℝ} {L U : ℝ → ℝ}
    {p : ℕ → ℕ} {k : ℕ} (hr : Regular d L U) (hs : IntervalBounds L U α p k)
    (g : ℕ) (hd : 0 < d) (hda : d ≤ α) (hg : 0 < g)
    (hz : L ((g - 1 : ℕ) : ℝ) = 0) (hpos : 0 < L g) :
    Regular d (quantumPatch d g (quantumSlope L g) (quantumIntercept L g) L) U ∧
      IntervalBounds (quantumPatch d g (quantumSlope L g) (quantumIntercept L g) L)
        U α p k := by
  have hsl := hr.quantumSlope_bounds g
  have ha := hr.quantumIntercept_nonpos g hg hz
  exact ⟨hr.quantumPatch g _ _ hd hg hsl.1 hsl.2 ha,
    hs.quantumPatch g _ _ hd hda ha hsl.1 hpos (quantum_support_nat hr g)⟩

#print axioms density_le_normalization
#print axioms quantum_cell_certificate
end Erdos970.ContinuousInterval
