import Submission.CompactGapRatioColoring

/-!
Fixed nontrivial pair-sum and cross-difference ratios confine a strict cubic
collision's adjacent-gap ratio to a compact subinterval of (1,infinity).
This is a uniform statement for each fixed relation, not for all ratios.
-/
namespace Erdos1206.CubeShapeCompactness

private lemma cofactors {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    y^2 ≤ y^2+y*x+x^2 ∧ y^2+y*x+x^2 ≤ 3*y^2 := by
  have hy := hx.trans hxy
  have h₁ := mul_nonneg hx (sub_nonneg.mpr hxy)
  have h₂ := mul_nonneg hy (sub_nonneg.mpr hxy)
  constructor <;> nlinarith [sq_nonneg x,mul_nonneg hx hy]

lemma gap_strict {a b c d : ℝ} (ha : 0 ≤ a) (hab : a < b) (hbc : b ≤ c) (hcd : c < d)
    (he : a^3+d^3=b^3+c^3) : d-c < b-a := by
  have hb := ha.trans_lt hab
  have hc := hb.trans_le hbc
  have hd := hc.trans hcd
  have hQ₁ : 0 ≤ b^2+b*a+a^2 := by positivity
  have hQ : b^2+b*a+a^2 < d^2+d*c+c^2 := by
    have hb2 : b^2 < d^2 := (sq_lt_sq₀ hb.le hd.le).mpr (hbc.trans_lt hcd)
    have ha2 : a^2 < c^2 := (sq_lt_sq₀ ha hc.le).mpr (hab.trans_le hbc)
    have hmul := mul_le_mul (hbc.trans_lt hcd).le (hab.trans_le hbc).le ha hd.le
    nlinarith
  have hp : (b-a)*(b^2+b*a+a^2)=(d-c)*(d^2+d*c+c^2) := by linear_combination -he
  by_contra! hgap
  have h₁ := mul_le_mul_of_nonneg_right hgap hQ₁
  have h₂ := mul_lt_mul_of_pos_left hQ (sub_pos.mpr hcd)
  linarith

lemma largest_le_twice_middle {a b c d : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hbc : b ≤ c) (he : a^3+d^3=b^3+c^3) : d ≤ 2*c := by
  have hc : 0 < c := (ha.trans_lt hab).trans_le hbc
  have hbc3 : b^3 ≤ c^3 := (by decide : Odd (3:ℕ)).strictMono_pow.monotone hbc
  apply (by decide : Odd (3:ℕ)).strictMono_pow.le_iff_le.mp
  nlinarith [pow_nonneg ha 3,pow_pos hc 3]

lemma gap_upper_of_middle_bound {a b c d L : ℝ} (ha : 0 ≤ a)
    (hab : a < b) (hbc : b ≤ c) (hcd : c < d) (he : a^3+d^3=b^3+c^3)
    (hL : 0 < L) (hbound : c ≤ L*b) : b-a ≤ 12*L^2*(d-c) := by
  have hb := ha.trans_lt hab
  have hc := hb.trans_le hbc
  have hd := hc.trans hcd
  have hh := sub_pos.mpr hab
  have hk := sub_pos.mpr hcd
  have hQ₁ := (cofactors ha hab.le).1
  have hQ₂ := (cofactors hc.le hcd.le).2
  have hd2 : d^2 ≤ 4*c^2 := by
    have hs := sq_le_sq₀ hd.le (by positivity : 0 ≤ 2*c) |>.mpr
      (largest_le_twice_middle ha hab hbc he)
    nlinarith
  have hc2 : c^2 ≤ L^2*b^2 := by
    have hs := sq_le_sq₀ hc.le (by positivity : 0 ≤ L*b) |>.mpr hbound
    nlinarith
  have hp : (b-a)*(b^2+b*a+a^2)=(d-c)*(d^2+d*c+c^2) := by linear_combination -he
  have hfinal : (b-a)*b^2 ≤ (12*L^2*(d-c))*b^2 := by
    calc
      _ ≤ (b-a)*(b^2+b*a+a^2) := mul_le_mul_of_nonneg_left hQ₁ hh.le
      _ = (d-c)*(d^2+d*c+c^2) := hp
      _ ≤ (d-c)*(12*c^2) := mul_le_mul_of_nonneg_left (by linarith) hk.le
      _ ≤ (d-c)*(12*(L^2*b^2)) := by gcongr
      _ = _ := by ring
  exact (mul_le_mul_iff_left₀ (sq_pos_of_pos hb)).mp hfinal

lemma cross_ratio_bounds {a b c d s : ℝ} (ha : 0 ≤ a) (hab : a < b) (hbc : b ≤ c)
    (hcd : c < d) (he : a^3+d^3=b^3+c^3) (hs : 1 < s)
    (hr : c-a=s*(d-b)) :
    s*(d-c) ≤ b-a ∧ b-a ≤ 12*(s/(s-1))^2*(d-c) := by
  have hb := ha.trans_lt hab
  have hden : 0 < s-1 := by linarith
  constructor
  · have ht := mul_nonneg hden.le (sub_nonneg.mpr hbc)
    nlinarith only [hr,ht]
  · apply gap_upper_of_middle_bound ha hab hbc hcd he (by positivity)
    have hk := mul_nonneg (show 0 ≤ s by linarith) (sub_nonneg.mpr hcd.le)
    have h : c ≤ s*b/(s-1) := (le_div_iff₀ hden).mpr (by nlinarith only [hr,ha,hk])
    simpa only [div_mul_eq_mul_div] using h

lemma sum_ratio_bounds {a b c d q : ℝ} (ha : 0 ≤ a) (hab : a < b) (hbc : b ≤ c)
    (hcd : c < d) (he : a^3+d^3=b^3+c^3) (hq : 0 < q) (hq1 : q < 1)
    (hr : a+d=q*(b+c)) :
    (1+(1-q)/2)*(d-c) ≤ b-a ∧ b-a ≤ 12*(q/(1-q))^2*(d-c) := by
  have hb := ha.trans_lt hab
  have hc := hb.trans_le hbc
  have hden : 0 < 1-q := by linarith
  constructor
  · have hd := largest_le_twice_middle ha hab hbc he
    have ht := mul_nonneg hden.le (show 0 ≤ 2*(b+c)-(d-c) by linarith)
    nlinarith only [hr,ht]
  · apply gap_upper_of_middle_bound ha hab hbc hcd he (by positivity)
    have h : c ≤ q*b/(1-q) := (le_div_iff₀ hden).mpr (by nlinarith only [hr,ha,hcd.le])
    simpa only [div_mul_eq_mul_div] using h

/-- Convert a real compact gap interval to the integer-indexed form used by
the existing positive-density geometric-band theorem. -/
lemma integer_compact_interval {l U : ℝ} (hl : 1 < l) :
    ∃ H : ℕ, 1 ≤ H ∧ ∀ h k : ℝ, 0 < k → l*k ≤ h → h ≤ U*k →
      ((H:ℝ)+1)*k ≤ H*h ∧ h ≤ H*k := by
  obtain ⟨H,hH⟩ := exists_nat_gt (max 1 (max U (1/(l-1))))
  have hH1 : (1:ℝ) < H := (le_max_left _ _).trans_lt hH
  have hHU : U < H := (le_trans (le_max_left _ _) (le_max_right _ _)).trans_lt hH
  have hHl : 1/(l-1) < H := (le_trans (le_max_right _ _) (le_max_right _ _)).trans_lt hH
  have hHnat : 1 ≤ H := by exact_mod_cast hH1.le
  have hl0 : 0 < l-1 := by linarith
  have hcoef : (H:ℝ)+1 ≤ H*l := by
    have hh := (div_lt_iff₀ hl0).mp hHl
    nlinarith
  refine ⟨H,hHnat,fun h k hk hlow hupp => ?_⟩
  constructor
  · have h₁ := mul_le_mul_of_nonneg_right hcoef hk.le
    have h₂ := mul_le_mul_of_nonneg_left hlow (by positivity : (0:ℝ) ≤ H)
    nlinarith
  · exact hupp.trans (mul_le_mul_of_nonneg_right hHU.le hk.le)

/-- A single fixed pair-sum ratio away from one can be excluded at positive
lower density, uniformly over all integer sizes and dilations. -/
theorem positive_density_avoids_sum_ratio {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    ∃ A : Set ℕ, A.Infinite ∧ 0 < A.lowerDensity ∧
      ∀ a b c d : ℕ, 0 < a → a < b → b ≤ c → c < d →
        a^3+d^3=b^3+c^3 → (a:ℝ)+d=q*((b:ℝ)+c) → ¬ (b ∈ A ∧ d ∈ A) := by
  obtain ⟨H,hH,hcompact⟩ := integer_compact_interval
    (U := 12*(q/(1-q))^2) (by linarith : (1:ℝ) < 1+(1-q)/2)
  obtain ⟨A,hA,hden,havoid⟩ := CompactGapRatioColoring.positive_density_avoids_compact_gap_ratios H hH
  refine ⟨A,hA,hden,fun a b c d ha hab hbc hcd he hr => ?_⟩
  have hrng := sum_ratio_bounds (by positivity : (0:ℝ) ≤ a)
    (by exact_mod_cast hab) (by exact_mod_cast hbc) (by exact_mod_cast hcd)
    (by exact_mod_cast he) hq hq1 hr
  obtain ⟨hlow,hupp⟩ := hcompact ((b:ℝ)-a) ((d:ℝ)-c)
    (by
      apply sub_pos.mpr
      exact_mod_cast hcd) hrng.1 hrng.2
  rw [← Nat.cast_sub hcd.le, ← Nat.cast_sub hab.le] at hlow hupp
  apply havoid a b c d hab hbc hcd he
  · exact_mod_cast hlow
  · exact_mod_cast hupp

/-- The same uniform conclusion for a fixed cross-difference ratio. -/
theorem positive_density_avoids_cross_ratio {s : ℝ} (hs : 1 < s) :
    ∃ A : Set ℕ, A.Infinite ∧ 0 < A.lowerDensity ∧
      ∀ a b c d : ℕ, 0 < a → a < b → b ≤ c → c < d →
        a^3+d^3=b^3+c^3 → (c:ℝ)-a=s*((d:ℝ)-b) → ¬ (b ∈ A ∧ d ∈ A) := by
  obtain ⟨H,hH,hcompact⟩ := integer_compact_interval (U := 12*(s/(s-1))^2) hs
  obtain ⟨A,hA,hden,havoid⟩ := CompactGapRatioColoring.positive_density_avoids_compact_gap_ratios H hH
  refine ⟨A,hA,hden,fun a b c d ha hab hbc hcd he hr => ?_⟩
  have hrng := cross_ratio_bounds (by positivity : (0:ℝ) ≤ a)
    (by exact_mod_cast hab) (by exact_mod_cast hbc) (by exact_mod_cast hcd)
    (by exact_mod_cast he) hs hr
  obtain ⟨hlow,hupp⟩ := hcompact ((b:ℝ)-a) ((d:ℝ)-c)
    (by
      apply sub_pos.mpr
      exact_mod_cast hcd) hrng.1 hrng.2
  rw [← Nat.cast_sub hcd.le, ← Nat.cast_sub hab.le] at hlow hupp
  apply havoid a b c d hab hbc hcd he
  · exact_mod_cast hlow
  · exact_mod_cast hupp

#print axioms cross_ratio_bounds
#print axioms sum_ratio_bounds
#print axioms positive_density_avoids_sum_ratio
#print axioms positive_density_avoids_cross_ratio
end Erdos1206.CubeShapeCompactness
