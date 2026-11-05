import FormalConjecturesUtil

/-! Derivative-free geometric part of the four-witness sign argument. -/
namespace SquarefreeFourthSign

set_option autoImplicit false

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

lemma minor_size_polynomial_left (A B : ℝ) (hA : 2 ≤ A) (hB : 1 ≤ B) :
    3*(A+B+1)^2 ≤ 4*A*(A+1)*B*(B+1) := by
  let s := A-2
  let h := B-1
  have hs : 0 ≤ s := by dsimp [s]; linarith
  have hh : 0 ≤ h := by dsimp [h]; linarith
  have hpos : 0 ≤ 4*s^2*h^2 + 12*s^2*h + 5*s^2 + 20*s*h^2 +
      54*s*h + 16*s + 21*h^2 + 48*h := by positivity
  have hid : 4*A*(A+1)*B*(B+1)-3*(A+B+1)^2 =
      4*s^2*h^2 + 12*s^2*h + 5*s^2 + 20*s*h^2 +
      54*s*h + 16*s + 21*h^2 + 48*h := by dsimp [s, h]; ring
  linarith

lemma minor_size_polynomial (A B : ℝ) (hA : 1 ≤ A) (hB : 1 ≤ B)
    (hlarge : 2 ≤ A ∨ 2 ≤ B) :
    3*(A+B+1)^2 ≤ 4*A*(A+1)*B*(B+1) := by
  rcases hlarge with h | h
  · exact minor_size_polynomial_left A B h hB
  · have := minor_size_polynomial_left B A h hA
    nlinarith only [this]

/-- The two normalized weights are balanced at
`B(B+1)r₀² = A(A+1)`. No derivatives are used. -/
lemma balanced_ratios (A B r r₀ : ℝ)
    (hA : 0 < A) (hB : 0 < B) (hr : 0 < r) (hr₀ : 0 < r₀)
    (hbal : B*(B+1)*r₀^2 = A*(A+1)) :
    B*(B+1)*r₀/(A+B+1) ≤
      max (A/(r+1)*(1+1/((B+1)*r+A)))
        (B*r/(r+1)*(1+r/(B*r+A+1))) := by
  have hp : 0 < A+B+1 := by positivity
  have hp₀ : 0 < r₀+1 := by positivity
  have hq₀ : 0 < (B+1)*r₀+A := by positivity
  have hs₀ : 0 < B*r₀+A+1 := by positivity
  have heq₁ : A/(r₀+1)*(1+1/((B+1)*r₀+A)) =
      B*(B+1)*r₀/(A+B+1) := by
    apply (eq_div_iff hp.ne').mpr
    field_simp
    have hid : A*((B+1)*r₀+A+1)*(A+B+1) -
        B*(B+1)*r₀*(r₀+1)*((B+1)*r₀+A) =
        (A*(A+1)-B*(B+1)*r₀^2)*(A+B*r₀+B+r₀+1) := by ring
    rw [hbal] at hid
    nlinarith only [hid]
  have heq₂ : B*r₀/(r₀+1)*(1+r₀/(B*r₀+A+1)) =
      B*(B+1)*r₀/(A+B+1) := by
    apply (eq_div_iff hp.ne').mpr
    field_simp
    have hid : (B*r₀+A+1+r₀)*(A+B+1) -
        (B+1)*(r₀+1)*(B*r₀+A+1) =
        A*(A+1)-B*(B+1)*r₀^2 := by ring
    rw [hbal] at hid
    nlinarith only [hid]
  by_cases hrr : r ≤ r₀
  · have hmono : A/(r₀+1)*(1+1/((B+1)*r₀+A)) ≤
        A/(r+1)*(1+1/((B+1)*r+A)) := by
      gcongr
    rw [heq₁] at hmono
    exact hmono.trans (le_max_left _ _)
  · have hrr' : r₀ ≤ r := le_of_lt (lt_of_not_ge hrr)
    have hratio₁ : r₀/(r₀+1) ≤ r/(r+1) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith
    have hratio₂ : r₀/(B*r₀+A+1) ≤ r/(B*r+A+1) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      have := mul_nonneg (show 0 ≤ r-r₀ by linarith) (show 0 ≤ A+1 by positivity)
      nlinarith
    have hmono : B*r₀/(r₀+1)*(1+r₀/(B*r₀+A+1)) ≤
        B*r/(r+1)*(1+r/(B*r+A+1)) := by
      simp only [mul_div_assoc]
      exact mul_le_mul (mul_le_mul_of_nonneg_left hratio₁ hB.le)
        (by linarith) (by positivity) (by positivity)
    rw [heq₂] at hmono
    exact hmono.trans (le_max_right _ _)

/-- Integer previous minors of which at least one is two give a weight
strictly greater than `3/4` of the geometric cofactor sum. This is the
needed consequence of the supplied optimized geometric inequality. -/
theorem large_minors_give_large_weight (a b c A B : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hA : 1 ≤ A) (hB : 1 ≤ B) (hlarge : 2 ≤ A ∨ 2 ≤ B)
    (hgap : b ≤ c*A+a*B) :
    3*(a+b)*(a+c)*(b+c) <
      4*max (A*c*(b+c)*(a+b+c)) (B*a*(a+b)*(a+b+c)) := by
  have hA0 : 0 < A := by linarith
  have hB0 : 0 < B := by linarith
  let r := a/c
  let r₀ := Real.sqrt (A*(A+1)/(B*(B+1)))
  let K := B*(B+1)*r₀/(A+B+1)
  have hr : 0 < r := div_pos ha hc
  have hden : 0 < B*(B+1) := by positivity
  have harg : 0 < A*(A+1)/(B*(B+1)) := by positivity
  have hr₀ : 0 < r₀ := Real.sqrt_pos.2 harg
  have hbal : B*(B+1)*r₀^2 = A*(A+1) := by
    have hs : r₀^2 = A*(A+1)/(B*(B+1)) := Real.sq_sqrt harg.le
    have := (eq_div_iff hden.ne').mp hs
    nlinarith only [this]
  have hK0 : 0 < K := by dsimp [K]; positivity
  have hKsq : 3 ≤ 4*K^2 := by
    have hsize := minor_size_polynomial A B hA hB hlarge
    have hid : K^2*(A+B+1)^2 = A*(A+1)*B*(B+1) := by
      dsimp [K]
      rw [div_pow, div_mul_cancel₀ _ (by positivity : (A+B+1)^2 ≠ 0)]
      have hi := congrArg (fun t : ℝ => t * (B*(B+1))) hbal
      nlinarith only [hi]
    have hpos : 0 < (A+B+1)^2 := by positivity
    have hmul : 3*(A+B+1)^2 ≤ (4*K^2)*(A+B+1)^2 := by nlinarith only [hid, hsize]
    exact (mul_le_mul_iff_left₀ hpos).mp (by simpa only [mul_comm] using hmul)
  have hK : (3/4 : ℝ) < K := by
    by_contra h
    have hh : K ≤ 3/4 := le_of_not_gt h
    have hm := mul_nonneg hK0.le (show 0 ≤ 3/4-K by linarith)
    nlinarith
  have hnorm := balanced_ratios A B r r₀ hA0 hB0 hr hr₀ hbal
  change K ≤ _ at hnorm
  let C₀ := (a+b)*(a+c)*(b+c)
  have hC₀ : 0 < C₀ := by dsimp [C₀]; positivity
  have hrep₁ : A/(r+1)*(1+1/((B+1)*r+A)) =
      A*c/(a+c)*(1+c/(a+c*A+a*B)) := by
    dsimp [r]
    field_simp
    ring
  have hsmall₁ : A/(r+1)*(1+1/((B+1)*r+A)) ≤
      (A*c*(b+c)*(a+b+c))/C₀ := by
    rw [hrep₁]
    calc
      A*c/(a+c)*(1+c/(a+c*A+a*B)) ≤ A*c/(a+c)*(1+c/(a+b)) := by
        have hd : c/(a+c*A+a*B) ≤ c/(a+b) :=
          div_le_div_of_nonneg_left hc.le (by positivity) (by linarith)
        exact mul_le_mul_of_nonneg_left (by linarith [hd]) (by positivity)
      _ = (A*c*(b+c)*(a+b+c))/C₀ := by dsimp [C₀]; field_simp
  have hsmall₂ : B*r/(r+1)*(1+r/(B*r+A+1)) ≤
      (B*a*(a+b)*(a+b+c))/C₀ := by
    have heq : B*r/(r+1)*(1+r/(B*r+A+1)) =
        B*a/(a+c)*(1+a/(c*A+a*B+c)) := by
      dsimp [r]
      field_simp
      ring
    rw [heq]
    calc
      B*a/(a+c)*(1+a/(c*A+a*B+c)) ≤ B*a/(a+c)*(1+a/(b+c)) := by
        have hd : a/(c*A+a*B+c) ≤ a/(b+c) :=
          div_le_div_of_nonneg_left ha.le (by positivity) (by linarith)
        exact mul_le_mul_of_nonneg_left (by linarith [hd]) (by positivity)
      _ = (B*a*(a+b)*(a+b+c))/C₀ := by dsimp [C₀]; field_simp; ring
  have hmax : K ≤ (max (A*c*(b+c)*(a+b+c)) (B*a*(a+b)*(a+b+c)))/C₀ := by
    apply hnorm.trans
    apply max_le
    · exact hsmall₁.trans (div_le_div_of_nonneg_right (le_max_left _ _) hC₀.le)
    · exact hsmall₂.trans (div_le_div_of_nonneg_right (le_max_right _ _) hC₀.le)
  have hlt : (3/4 : ℝ) < (max (A*c*(b+c)*(a+b+c)) (B*a*(a+b)*(a+b+c)))/C₀ :=
    hK.trans_le hmax
  have := (lt_div_iff₀ hC₀).mp hlt
  dsimp [C₀] at this
  linarith

end SquarefreeFourthSign
