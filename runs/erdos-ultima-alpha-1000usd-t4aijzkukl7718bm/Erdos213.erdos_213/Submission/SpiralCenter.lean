import FormalConjecturesUtil

/-! A rational-distance extension rule via a spiral center. This does not
assert the existence of eight points or settle Erdős Problem 213. -/
namespace Erdos213.SpiralCenter
noncomputable section

def center (a b c d : ℂ) : ℂ := (a*c-b*d)/(a+c-b-d)

lemma center_sub_first (a b c d : ℂ) (h : a+c-b-d ≠ 0) :
    center a b c d-a = -(a-b)*(a-d)/(a+c-b-d) := by
  dsimp [center]
  field_simp
  ring

lemma center_sub_second (a b c d : ℂ) (h : a+c-b-d ≠ 0) :
    center a b c d-b = (a-b)*(c-b)/(a+c-b-d) := by
  dsimp [center]
  field_simp
  ring

lemma center_sub_third (a b c d : ℂ) (h : a+c-b-d ≠ 0) :
    center a b c d-c = -(c-b)*(c-d)/(a+c-b-d) := by
  dsimp [center]
  field_simp
  ring

lemma center_sub_fourth (a b c d : ℂ) (h : a+c-b-d ≠ 0) :
    center a b c d-d = (a-d)*(c-d)/(a+c-b-d) := by
  dsimp [center]
  field_simp
  ring

lemma dist_first (a b c d : ℂ) (h : a+c-b-d ≠ 0) :
    dist (center a b c d) a = dist a b*dist a d/‖a+c-b-d‖ := by
  rw [dist_eq_norm, center_sub_first a b c d h]
  simp only [norm_div,norm_mul,norm_neg,dist_eq_norm]

lemma dist_second (a b c d : ℂ) (h : a+c-b-d ≠ 0) :
    dist (center a b c d) b = dist a b*dist c b/‖a+c-b-d‖ := by
  rw [dist_eq_norm, center_sub_second a b c d h]
  simp only [norm_div,norm_mul,dist_eq_norm]

lemma dist_third (a b c d : ℂ) (h : a+c-b-d ≠ 0) :
    dist (center a b c d) c = dist c b*dist c d/‖a+c-b-d‖ := by
  rw [dist_eq_norm, center_sub_third a b c d h]
  simp only [norm_div,norm_mul,norm_neg,dist_eq_norm]

lemma dist_fourth (a b c d : ℂ) (h : a+c-b-d ≠ 0) :
    dist (center a b c d) d = dist a d*dist c d/‖a+c-b-d‖ := by
  rw [dist_eq_norm, center_sub_fourth a b c d h]
  simp only [norm_div,norm_mul,dist_eq_norm]

def Rational (r : ℝ) : Prop := r ∈ Set.range ((↑) : ℚ → ℝ)

lemma Rational.mul {r s : ℝ} (hr : Rational r) (hs : Rational s) : Rational (r*s) := by
  obtain ⟨a,rfl⟩ := hr
  obtain ⟨b,rfl⟩ := hs
  exact ⟨a*b, by simp⟩

lemma Rational.div {r s : ℝ} (hr : Rational r) (hs : Rational s) : Rational (r/s) := by
  obtain ⟨a,rfl⟩ := hr
  obtain ⟨b,rfl⟩ := hs
  exact ⟨a/b, by simp⟩

/-- A rational bimedian gives rational distances from the center to the four
vertices. General position is a separate condition. -/
lemma rational_four_distances (a b c d : ℂ) (h : a+c-b-d ≠ 0)
    (hab : Rational (dist a b)) (had : Rational (dist a d))
    (hcb : Rational (dist c b)) (hcd : Rational (dist c d))
    (hm : Rational ‖a+c-b-d‖) :
    Rational (dist (center a b c d) a) ∧
    Rational (dist (center a b c d) b) ∧
    Rational (dist (center a b c d) c) ∧
    Rational (dist (center a b c d) d) := by
  rw [dist_first _ _ _ _ h,dist_second _ _ _ _ h,
    dist_third _ _ _ _ h,dist_fourth _ _ _ _ h]
  exact ⟨(hab.mul had).div hm,(hab.mul hcb).div hm,
    (hcb.mul hcd).div hm,(had.mul hcd).div hm⟩

/-- Conversely, one nonzero edge product and one new rational distance
already force the bimedian norm to be rational. -/
lemma rational_denominator_iff (a b c d : ℂ) (h : a+c-b-d ≠ 0)
    (hab : Rational (dist a b)) (had : Rational (dist a d))
    (hab0 : a ≠ b) (had0 : a ≠ d) :
    Rational ‖a+c-b-d‖ ↔ Rational (dist (center a b c d) a) := by
  constructor
  · intro hm
    rw [dist_first _ _ _ _ h]
    exact (hab.mul had).div hm
  · intro hc
    have hnorm : ‖a+c-b-d‖ ≠ 0 := norm_ne_zero_iff.mpr h
    have hed : dist a b * dist a d ≠ 0 := mul_ne_zero (dist_ne_zero.mpr hab0) (dist_ne_zero.mpr had0)
    have hh : ‖a+c-b-d‖ = (dist a b*dist a d)/dist (center a b c d) a := by
      rw [dist_first _ _ _ _ h]
      field_simp
      simp [hed]
    rw [hh]
    exact (hab.mul had).div hc

lemma centers_difference12 (a b c d : ℂ)
    (h1 : a+c-b-d ≠ 0) (h2 : a+b-c-d ≠ 0) :
    center a b c d-center a c b d =
      -(a-d)*(b-c)*(a+d-b-c)/((a+c-b-d)*(a+b-c-d)) := by
  dsimp [center]
  field_simp
  ring

lemma centers_difference13 (a b c d : ℂ)
    (h1 : a+c-b-d ≠ 0) (h3 : a+d-b-c ≠ 0) :
    center a b c d-center a b d c =
      (a-b)*(c-d)*(a+b-c-d)/((a+c-b-d)*(a+d-b-c)) := by
  dsimp [center]
  field_simp
  ring

lemma centers_difference23 (a b c d : ℂ)
    (h2 : a+b-c-d ≠ 0) (h3 : a+d-b-c ≠ 0) :
    center a c b d-center a b d c =
      (a-c)*(b-d)*(a+c-b-d)/((a+b-c-d)*(a+d-b-c)) := by
  dsimp [center]
  field_simp
  ring

lemma rational_center_pairs (a b c d : ℂ)
    (h1 : a+c-b-d ≠ 0) (h2 : a+b-c-d ≠ 0) (h3 : a+d-b-c ≠ 0)
    (hab : Rational (dist a b)) (hac : Rational (dist a c))
    (had : Rational (dist a d)) (hbc : Rational (dist b c))
    (hbd : Rational (dist b d)) (hcd : Rational (dist c d))
    (hm1 : Rational ‖a+c-b-d‖) (hm2 : Rational ‖a+b-c-d‖)
    (hm3 : Rational ‖a+d-b-c‖) :
    Rational (dist (center a b c d) (center a c b d)) ∧
    Rational (dist (center a b c d) (center a b d c)) ∧
    Rational (dist (center a c b d) (center a b d c)) := by
  simp only [dist_eq_norm] at hab hac had hbc hbd hcd ⊢
  rw [centers_difference12 _ _ _ _ h1 h2,centers_difference13 _ _ _ _ h1 h3,
    centers_difference23 _ _ _ _ h2 h3]
  simp only [norm_div,norm_mul,norm_neg]
  exact ⟨((had.mul hbc).mul hm3).div (hm1.mul hm2),
    ((hab.mul hcd).mul hm2).div (hm1.mul hm3),
    ((hac.mul hbd).mul hm1).div (hm2.mul hm3)⟩

def seven (a b c d : ℂ) : Fin 7 → ℂ :=
  ![a,b,c,d,center a b c d,center a c b d,center a b d c]

/-- Three rational bimedians complete a rational quadrilateral to a
seven-term rational-distance configuration. Injectivity and general position
are not asserted by this theorem. -/
lemma rational_seven (a b c d : ℂ)
    (h1 : a+c-b-d ≠ 0) (h2 : a+b-c-d ≠ 0) (h3 : a+d-b-c ≠ 0)
    (hab : Rational (dist a b)) (hac : Rational (dist a c))
    (had : Rational (dist a d)) (hbc : Rational (dist b c))
    (hbd : Rational (dist b d)) (hcd : Rational (dist c d))
    (hm1 : Rational ‖a+c-b-d‖) (hm2 : Rational ‖a+b-c-d‖)
    (hm3 : Rational ‖a+d-b-c‖) :
    ∀ i j, Rational (dist (seven a b c d i) (seven a b c d j)) := by
  have hcb : Rational (dist c b) := by simpa only [dist_comm] using hbc
  have hdb : Rational (dist d b) := by simpa only [dist_comm] using hbd
  have hdc : Rational (dist d c) := by simpa only [dist_comm] using hcd
  obtain ⟨ha1,hb1,hc1,hd1⟩ := rational_four_distances a b c d h1 hab had hcb hcd hm1
  obtain ⟨ha2,hc2,hb2,hd2⟩ := rational_four_distances a c b d h2 hac had hbc hbd hm2
  obtain ⟨ha3,hb3,hd3,hc3⟩ := rational_four_distances a b d c h3 hab hac hdb hdc hm3
  obtain ⟨h12,h13,h23⟩ := rational_center_pairs a b c d h1 h2 h3
    hab hac had hbc hbd hcd hm1 hm2 hm3
  have hzero : Rational 0 := ⟨0,by simp⟩
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [seven,dist_comm]

#print axioms rational_four_distances
#print axioms rational_denominator_iff
#print axioms rational_seven
end
end Erdos213.SpiralCenter
