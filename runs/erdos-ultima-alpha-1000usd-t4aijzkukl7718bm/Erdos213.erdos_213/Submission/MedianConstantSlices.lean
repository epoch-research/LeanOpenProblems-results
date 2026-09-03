import Submission.MedianDiscriminant

/-! Exact arithmetic for constant-parameter slices of the median template.
This is not an existence theorem or an unrestricted obstruction for Erdős 213.
The remaining conductor-96 quartic is only a reduction here; no external
elliptic rank computation is used in any Lean theorem. -/
namespace Erdos213.MedianConstantSlices
set_option maxHeartbeats 3000000

private lemma quartic_mod16_two : ∀ m n w : ZMod 16,
    w^2=2*m^4+4*m^2*n^2-14*n^4 → m.val%2=0 ∧ n.val%2=0 := by decide

private lemma quartic_mod16_half : ∀ m n w : ZMod 16,
    w^2=8*m^4-8*m^2*n^2+10*n^4 → m.val%2=0 ∧ n.val%2=0 := by decide

lemma rational_quartic_obstruction (a b c : ℤ)
    (hmod : ∀ m n w : ZMod 16,
      w^2=(a : ZMod 16)*m^4+(b : ZMod 16)*m^2*n^2+(c : ZMod 16)*n^4 →
      m.val%2=0 ∧ n.val%2=0) (u : ℚ) :
    ¬ IsSquare ((a : ℚ)*u^4+(b : ℚ)*u^2+c) := by
  rintro ⟨v,hv⟩
  have hd : (u.den : ℚ)≠0 := by exact_mod_cast u.den_ne_zero
  have hn : (u.num : ℚ)=u*(u.den : ℚ) := by
    calc
      _ = ((u.num : ℚ)/(u.den : ℚ))*(u.den : ℚ) := by field_simp
      _ = _ := by rw [Rat.num_div_den]
  have hs : IsSquare ((a*u.num^4+b*u.num^2*(u.den : ℤ)^2+c*(u.den : ℤ)^4 : ℤ) : ℚ) := by
    refine ⟨v*(u.den : ℚ)^2,?_⟩
    push_cast
    rw [hn]
    linear_combination (u.den : ℚ)^4*hv
  obtain ⟨w,hw⟩ := Rat.isSquare_intCast_iff.mp hs
  have he : (w : ZMod 16)^2=(a : ZMod 16)*(u.num : ZMod 16)^4+
      (b : ZMod 16)*(u.num : ZMod 16)^2*(u.den : ZMod 16)^2+
      (c : ZMod 16)*(u.den : ZMod 16)^4 := by
    have hh := congrArg (fun z : ℤ => (z : ZMod 16)) hw
    push_cast at hh
    simpa only [pow_two] using hh.symm
  have hh := hmod _ _ _ he
  have hm : (2 : ℤ) ∣ u.num := by
    have h : (((u.num : ZMod 16).val : ℤ)%2)=0 := by exact_mod_cast hh.1
    rw [ZMod.val_intCast] at h
    norm_num only [Nat.cast_ofNat] at h
    rw [Int.emod_emod_of_dvd _ (by norm_num : (2 : ℤ) ∣ 16)] at h
    exact Int.dvd_of_emod_eq_zero h
  have hden : (2 : ℤ) ∣ (u.den : ℤ) := by
    have h : (((u.den : ZMod 16).val : ℤ)%2)=0 := by exact_mod_cast hh.2
    simp only [ZMod.val_natCast] at h
    have hn2 : u.den%16%2=0 := by exact_mod_cast h
    exact_mod_cast Nat.dvd_of_mod_eq_zero (by omega : u.den%2=0)
  obtain ⟨r,s,hrs⟩ := u.isCoprime_num_den
  have htwo : (2 : ℤ) ∣ 1 := by
    rw [←hrs]
    exact dvd_add (dvd_mul_of_dvd_right hm r) (dvd_mul_of_dvd_right hden s)
  norm_num at htwo

lemma no_two_quartic (u : ℚ) : ¬ IsSquare (2*u^4+4*u^2-14) := by
  have h := rational_quartic_obstruction 2 4 (-14) (by
    simpa only [Int.cast_ofNat,Int.cast_neg,sub_eq_add_neg,neg_mul] using quartic_mod16_two) u
  simpa only [Int.cast_ofNat,Int.cast_neg,sub_eq_add_neg] using h

lemma no_half_quartic (u : ℚ) : ¬ IsSquare (8*u^4-8*u^2+10) := by
  have h := rational_quartic_obstruction 8 (-8) 10 (by
    simpa only [Int.cast_ofNat,Int.cast_neg,sub_eq_add_neg,neg_mul] using quartic_mod16_half) u
  simpa only [Int.cast_ofNat,Int.cast_neg,sub_eq_add_neg,neg_mul] using h

/-- The automatic first-median slice has no rational side roots at all. -/
theorem no_sides_two (s : ℚ) :
    ¬ (IsSquare (2*s^2-1) ∧ IsSquare (4*s-1)) := by
  rintro ⟨⟨a,ha⟩,⟨c,hc⟩⟩
  apply no_two_quartic c
  refine ⟨4*a,?_⟩
  have hc' : c^2=4*s-1 := by nlinarith only [hc]
  rw [show c^4=(c^2)^2 by ring,hc']
  nlinarith only [ha]

/-- The automatic second-median slice also has no rational side roots. -/
theorem no_sides_half (s : ℚ) :
    ¬ (IsSquare ((s^2+1)/2) ∧ IsSquare (s+1/2)) := by
  rintro ⟨⟨a,ha⟩,⟨c,hc⟩⟩
  apply no_half_quartic c
  refine ⟨4*a,?_⟩
  have hc' : c^2=s+1/2 := by nlinarith only [hc]
  rw [show c^4=(c^2)^2 by ring,hc']
  nlinarith only [ha]

lemma no_param_two (s : ℚ) : ¬ MedianDiscriminant.ParamAdmissible s 2 := by
  intro h
  apply no_sides_two s
  constructor
  · convert h.1 using 1; ring
  · convert h.2.1 using 1; ring

lemma no_param_half (s : ℚ) : ¬ MedianDiscriminant.ParamAdmissible s (1/2) := by
  intro h
  apply no_sides_half s
  constructor
  · convert h.1 using 1; ring
  · convert h.2.1 using 1; ring

/-- The third automatic-median slice reduces to a specific quartic.
No rational-point classification of this quartic is assumed here. -/
lemma minus_one_quartic (s : ℚ) (h : MedianDiscriminant.ParamAdmissible s (-1)) :
    ∃ c d : ℚ, c^2=2-2*s ∧ d^2= -2*c^4+4*c^2+16 ∧ 0<c^2 ∧ c^2<4 := by
  rcases h with ⟨_,⟨c,hc⟩,⟨m,hm⟩,_,_,hH⟩
  have hc' : c^2=2-2*s := by nlinarith only [hc]
  have hm' : m^2=4-2*s^2+2*s := by nlinarith only [hm]
  have hH' : 0<(1-s^2)*(3+(s-2)^2) := by nlinarith only [hH]
  have hpos : 0<3+(s-2)^2 := by positivity
  have hs : s^2<1 := by
    have hh := (mul_pos_iff_of_pos_right hpos).mp hH'
    linarith
  refine ⟨c,2*m,hc',?_,?_,?_⟩
  · rw [show c^4=(c^2)^2 by ring,hc']
    nlinarith only [hm']
  · nlinarith [sq_nonneg (s-1)]
  · nlinarith [sq_nonneg (s+1)]

/-- A rational norm equation excluded by the sum-of-two-squares obstruction
at 3. The proof is an explicit quadratic-form transformation. -/
lemma norm_two_three {x y z : ℚ} (h : x^2-2*y^2=3*z^2) : z=0 := by
  have hz := rat_sum_two_squares_three_mul
    (x := x+3*z) (y := 2*y) (z := x+z)
    (by linear_combination -2*h)
  nlinarith [sq_nonneg y,sq_nonneg z]

/-- No rational square parameter can make even the first median a square. -/
lemma first_median_not_square_parameter (s z : ℚ) :
    ¬ IsSquare (3+z^2*(2*s^2-2*s-1)) := by
  rintro ⟨m,hm⟩
  let W := z*(2*s-1)
  have he : W^2-2*m^2=3*(z^2-2) := by
    dsimp [W]
    linear_combination 2*hm
  have hh : (W*z-2*m)^2-2*(m*z-W)^2=3*(z^2-2)^2 := by
    linear_combination (z^2-2)*he
  have hz := norm_two_three hh
  have hs : IsSquare (2 : ℚ) := ⟨z,by nlinarith only [hz]⟩
  norm_num at hs

/-- The square class six is excluded too, by a different norm composition. -/
lemma first_median_not_six_square_parameter (s z : ℚ) :
    ¬ IsSquare (3+6*z^2*(2*s^2-2*s-1)) := by
  rintro ⟨m,hm⟩
  let W := z*(2*s-1)
  have he : m^2+9*z^2=3*(W^2+1) := by
    dsimp [W]
    linear_combination -hm
  have hh : (m*W+3*z)^2+(3*z*W-m)^2=3*(W^2+1)^2 := by
    linear_combination (W^2+1)*he
  have hz := rat_sum_two_squares_three_mul hh
  nlinarith [sq_nonneg W]

/-- These square-class restrictions hold for every parameter of the full
median criterion, not only for the three constant automatic-median slices. -/
theorem admissible_parameter_square_classes {s q : ℚ}
    (h : MedianDiscriminant.ParamAdmissible s q) :
    ¬ IsSquare q ∧ ¬ IsSquare (q/6) := by
  have hm := h.2.2.1
  constructor
  · rintro ⟨z,hz⟩
    have hq : q=z^2 := by nlinarith only [hz]
    exact first_median_not_square_parameter s z (by simpa [hq] using hm)
  · rintro ⟨z,hz⟩
    have hq : q=6*z^2 := by nlinarith only [hz]
    exact first_median_not_six_square_parameter s z (by simpa [hq,mul_assoc] using hm)

/-- A positive-area side-and-one-median control for `q=-1`.
The other two medians fail, so it is not an admissible eight-point input. -/
lemma minus_one_control :
    IsSquare (MedianDiscriminant.sideA (17/25) (-1)) ∧
    IsSquare (MedianDiscriminant.sideC (17/25) (-1)) ∧
    IsSquare (3+(-1 : ℚ)*(-(17/25)^2+4*(17/25)-1)) ∧
    0<(1+(-1 : ℚ)*(17/25)^2)*(3-(-1 : ℚ)*((17/25)-2)^2) ∧
    ¬ IsSquare (3+(-1 : ℚ)*(2*(17/25)^2-2*(17/25)-1)) ∧
    ¬ IsSquare (3+2*(-1 : ℚ)*((17/25)^2+2*(17/25)-2)) := by
  norm_num [MedianDiscriminant.sideA,MedianDiscriminant.sideC]

#print axioms no_sides_two
#print axioms no_sides_half
#print axioms no_param_two
#print axioms no_param_half
#print axioms minus_one_quartic
#print axioms admissible_parameter_square_classes
#print axioms minus_one_control
end Erdos213.MedianConstantSlices
