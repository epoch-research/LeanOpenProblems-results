import Submission.LocalStructure

/-!
# Exact local shapes of ordered cube collisions

These are integer-algebra building blocks, **not a proof of the density claim**
in `Submission.Spec`. That file is not imported, and no point-counting or
number-theoretic counting estimate is assumed here.

For natural roots `0 < a < b ≤ c < d` with `a ^ 3 + d ^ 3 = b ^ 3 + c ^ 3`,
all differences below are taken in `ℤ`, not by truncated natural subtraction.
The shape coordinates are `s = a + d`, `h = d - a`, `l = c - b`,
`q = b + c - a - d`, and `e = h ^ 2 - l ^ 2 - q * (s + q)`.
Repeated middle roots `b = c` are allowed. The shifted-gap coordinates are
`t = d - c`, `p = b - a`, `U = p * (2 * a + p)`, and `V = 2 * c + t`.
-/

namespace Erdos1206.CollisionShape

/-- The outer root sum `s`, in the integers. -/
def outerSum (a d : ℕ) : ℤ := (a : ℤ) + d

/-- The outer gap `h`, in the integers. -/
def outerGap (a d : ℕ) : ℤ := (d : ℤ) - a

/-- The inner gap `l`, which may be zero. -/
def innerGap (b c : ℕ) : ℤ := (c : ℤ) - b

/-- The root-sum defect `q`, with the inner sum minus the outer sum. -/
def sumDefect (a b c d : ℕ) : ℤ := (b : ℤ) + c - a - d

/-- The integral shape defect `e = h² - l² - q(s + q)`. -/
def shapeDefect (a b c d : ℕ) : ℤ :=
  outerGap a d ^ 2 - innerGap b c ^ 2 -
    sumDefect a b c d * (outerSum a d + sumDefect a b c d)

/-- The lower end gap `p = b - a`. -/
def lowerGap (a b : ℕ) : ℤ := (b : ℤ) - a

/-- The upper end gap `t = d - c`. -/
def upperGap (c d : ℕ) : ℤ := (d : ℤ) - c

/-- The first shifted-gap Pell coordinate `U = p(2a + p)`. -/
def pellU (a b : ℕ) : ℤ := lowerGap a b * (2 * (a : ℤ) + lowerGap a b)

/-- The second shifted-gap Pell coordinate `V = 2c + t`. -/
def pellV (c d : ℕ) : ℤ := 2 * (c : ℤ) + upperGap c d

/-- The exact relation `p = t + q` does not require a cube equality. -/
theorem lowerGap_eq_upperGap_add_sumDefect (a b c d : ℕ) :
    lowerGap a b = upperGap c d + sumDefect a b c d := by
  dsimp [lowerGap, upperGap, sumDefect]
  ring

/-- The exact relation `h = l + q + 2t`. -/
theorem outerGap_eq_innerGap_add_sumDefect_add_two_mul_upperGap (a b c d : ℕ) :
    outerGap a d = innerGap b c + sumDefect a b c d + 2 * upperGap c d := by
  dsimp [outerGap, innerGap, sumDefect, upperGap]
  ring

set_option maxHeartbeats 800000 in
/-- The short shifted gap satisfies `t² < bq`, even when `b = c`. -/
theorem upperGap_sq_lt_mul_sumDefect {a b c d : ℕ}
    (ha : 0 < a) (hab : a < b) (hbc : b ≤ c) (hcd : c < d)
    (hcube : a ^ 3 + d ^ 3 = b ^ 3 + c ^ 3) :
    upperGap c d ^ 2 < (b : ℤ) * sumDefect a b c d := by
  have haZ : (0 : ℤ) < a := by exact_mod_cast ha
  have hbZ : (0 : ℤ) < b := by omega
  have hbcZ : (b : ℤ) ≤ c := by exact_mod_cast hbc
  have hp : (0 : ℤ) < (b : ℤ) - a := by omega
  have ht : (0 : ℤ) < (d : ℤ) - c := by omega
  have hcubeZ : (a : ℤ) ^ 3 + d ^ 3 = b ^ 3 + c ^ 3 := by
    exact_mod_cast hcube
  have hupper : (b : ℤ) ^ 3 - a ^ 3 < 3 * (b : ℤ) ^ 2 * ((b : ℤ) - a) := by
    have hpositive := mul_pos (sq_pos_of_pos hp)
      (show (0 : ℤ) < (a : ℤ) + 2 * b by omega)
    nlinarith only [hpositive]
  have hsq : (b : ℤ) ^ 2 ≤ (c : ℤ) ^ 2 := by nlinarith only [hbZ, hbcZ]
  have hlower : 3 * (b : ℤ) ^ 2 * ((d : ℤ) - c) +
      3 * (b : ℤ) * ((d : ℤ) - c) ^ 2 ≤ (d : ℤ) ^ 3 - c ^ 3 := by
    have hfirst := mul_nonneg (sub_nonneg.mpr hsq) ht.le
    have hsecond := mul_nonneg (sub_nonneg.mpr hbcZ) (sq_nonneg ((d : ℤ) - c))
    have hthird := mul_nonneg ht.le (sq_nonneg ((d : ℤ) - c))
    nlinarith only [hfirst, hsecond, hthird]
  have hscaled : (3 * (b : ℤ)) * upperGap c d ^ 2 <
      (3 * (b : ℤ)) * ((b : ℤ) * sumDefect a b c d) := by
    dsimp [upperGap, sumDefect]
    nlinarith only [hupper, hlower, hcubeZ]
  exact (mul_lt_mul_iff_right₀ (by positivity : (0 : ℤ) < 3 * (b : ℤ))).mp hscaled

/-- The inner root sum is strictly larger than the outer root sum. -/
theorem sumDefect_pos {a b c d : ℕ}
    (ha : 0 < a) (hab : a < b) (hbc : b ≤ c) (hcd : c < d)
    (hcube : a ^ 3 + d ^ 3 = b ^ 3 + c ^ 3) :
    0 < sumDefect a b c d := by
  have hbZ : (0 : ℤ) < b := by omega
  have hproduct : 0 < (b : ℤ) * sumDefect a b c d :=
    lt_of_le_of_lt (sq_nonneg _) (upperGap_sq_lt_mul_sumDefect ha hab hbc hcd hcube)
  exact (mul_pos_iff_of_pos_left hbZ).mp hproduct

/-- Cubing modulo six forces the integer defect to be divisible by six.
No order hypotheses are needed for this congruence. -/
theorem six_dvd_sumDefect {a b c d : ℕ}
    (hcube : a ^ 3 + d ^ 3 = b ^ 3 + c ^ 3) :
    (6 : ℤ) ∣ sumDefect a b c d := by
  have hmod := cube_sum_eq_implies_sum_mod_six hcube
  have hmodZ : ((a : ℤ) + d) % 6 = ((b : ℤ) + c) % 6 := by
    exact_mod_cast hmod
  apply Int.dvd_iff_emod_eq_zero.mpr
  dsimp [sumDefect]
  omega

/-- The original cube equality expanded in `s,h,l,q`, with denominators cleared. -/
theorem cube_expansion {a b c d : ℕ}
    (hcube : a ^ 3 + d ^ 3 = b ^ 3 + c ^ 3) :
    outerSum a d ^ 3 + 3 * outerSum a d * outerGap a d ^ 2 =
      (outerSum a d + sumDefect a b c d) ^ 3 +
        3 * (outerSum a d + sumDefect a b c d) * innerGap b c ^ 2 := by
  have hcubeZ : (a : ℤ) ^ 3 + d ^ 3 = b ^ 3 + c ^ 3 := by
    exact_mod_cast hcube
  dsimp [outerSum, outerGap, innerGap, sumDefect]
  nlinarith only [hcubeZ]

/-- The exact denominator-cleared shape equation `3se = q(3l² + q²)`. -/
theorem three_mul_outerSum_mul_shapeDefect {a b c d : ℕ}
    (hcube : a ^ 3 + d ^ 3 = b ^ 3 + c ^ 3) :
    3 * outerSum a d * shapeDefect a b c d =
      sumDefect a b c d * (3 * innerGap b c ^ 2 + sumDefect a b c d ^ 2) := by
  have hexpansion := cube_expansion hcube
  dsimp only [shapeDefect]
  nlinarith only [hexpansion]

/-- The version `se = q(l² + q²/3)` uses exact integer division: `3 ∣ q²`. -/
theorem outerSum_mul_shapeDefect {a b c d : ℕ}
    (hcube : a ^ 3 + d ^ 3 = b ^ 3 + c ^ 3) :
    outerSum a d * shapeDefect a b c d =
      sumDefect a b c d * (innerGap b c ^ 2 + sumDefect a b c d ^ 2 / 3) := by
  have hthree : (3 : ℤ) ∣ sumDefect a b c d :=
    dvd_trans (by norm_num) (six_dvd_sumDefect hcube)
  have hsq : (3 : ℤ) ∣ sumDefect a b c d ^ 2 := by
    simpa only [pow_two] using dvd_mul_of_dvd_left hthree (sumDefect a b c d)
  have hdivision := Int.ediv_mul_cancel hsq
  have hscaled := three_mul_outerSum_mul_shapeDefect hcube
  nlinarith only [hscaled, congrArg (fun value : ℤ => sumDefect a b c d * value) hdivision]

/-- The shape defect is strictly positive for ordered positive roots. -/
theorem shapeDefect_pos {a b c d : ℕ}
    (ha : 0 < a) (hab : a < b) (hbc : b ≤ c) (hcd : c < d)
    (hcube : a ^ 3 + d ^ 3 = b ^ 3 + c ^ 3) :
    0 < shapeDefect a b c d := by
  have hq := sumDefect_pos ha hab hbc hcd hcube
  have hs : 0 < outerSum a d := by dsimp [outerSum]; omega
  have hright : 0 < sumDefect a b c d *
      (3 * innerGap b c ^ 2 + sumDefect a b c d ^ 2) := by
    apply mul_pos hq
    nlinarith only [sq_nonneg (innerGap b c), sq_pos_of_pos hq]
  rw [← three_mul_outerSum_mul_shapeDefect hcube] at hright
  exact (mul_pos_iff_of_pos_left (by positivity : 0 < 3 * outerSum a d)).mp hright

/-- In particular, reconstruction may cancel the nonzero shape defect. -/
theorem shapeDefect_ne_zero {a b c d : ℕ}
    (ha : 0 < a) (hab : a < b) (hbc : b ≤ c) (hcd : c < d)
    (hcube : a ^ 3 + d ^ 3 = b ^ 3 + c ^ 3) :
    shapeDefect a b c d ≠ 0 :=
  ne_of_gt (shapeDefect_pos ha hab hbc hcd hcube)

/-- The shape defect is even. This uses only the cube equality, not order. -/
theorem shapeDefect_even {a b c d : ℕ}
    (hcube : a ^ 3 + d ^ 3 = b ^ 3 + c ^ 3) :
    Even (shapeDefect a b c d) := by
  have hq : Even (sumDefect a b c d) :=
    even_iff_two_dvd.mpr (dvd_trans (by norm_num) (six_dvd_sumDefect hcube))
  have hgap : Even (outerGap a d - innerGap b c) := by
    have hlinear : outerGap a d - innerGap b c =
        sumDefect a b c d + 2 * upperGap c d := by
      have hrelation := outerGap_eq_innerGap_add_sumDefect_add_two_mul_upperGap a b c d
      omega
    rw [hlinear]
    exact hq.add (even_two_mul _)
  have hsquares : Even (outerGap a d ^ 2 - innerGap b c ^ 2) := by
    rw [sq_sub_sq, mul_comm]
    exact hgap.mul_right _
  exact hsquares.sub (hq.mul_right _)

/-- Eliminating `s` gives the exact denominator-cleared conic in `h,l`.
The sign of the inner-gap term is negative. -/
theorem shape_conic {a b c d : ℕ}
    (hcube : a ^ 3 + d ^ 3 = b ^ 3 + c ^ 3) :
    3 * shapeDefect a b c d * outerGap a d ^ 2 -
        3 * (shapeDefect a b c d + sumDefect a b c d ^ 2) * innerGap b c ^ 2 =
      3 * shapeDefect a b c d ^ 2 +
        3 * shapeDefect a b c d * sumDefect a b c d ^ 2 + sumDefect a b c d ^ 4 := by
  have hscaled := three_mul_outerSum_mul_shapeDefect hcube
  have hdefinition : shapeDefect a b c d = outerGap a d ^ 2 - innerGap b c ^ 2 -
      sumDefect a b c d * (outerSum a d + sumDefect a b c d) := rfl
  linear_combination -3 * shapeDefect a b c d * hdefinition + sumDefect a b c d * hscaled

/-- With `q,e,l` fixed and `e ≠ 0`, the cleared shape equation determines `s`.
This cancellation lemma is purely over the integers. -/
theorem sum_eq_of_shape_identity
    {sumOne sumTwo defectCoord shapeCoord innerCoord : ℤ}
    (hshape : shapeCoord ≠ 0)
    (hfirst : 3 * sumOne * shapeCoord = defectCoord * (3 * innerCoord ^ 2 + defectCoord ^ 2))
    (hsecond : 3 * sumTwo * shapeCoord = defectCoord * (3 * innerCoord ^ 2 + defectCoord ^ 2)) :
    sumOne = sumTwo := by
  have hscaled := mul_right_cancel₀ hshape (hfirst.trans hsecond.symm)
  omega

/-- Exact reconstruction of `s` by integer division by the positive defect `e`. -/
theorem outerSum_eq_div {a b c d : ℕ}
    (ha : 0 < a) (hab : a < b) (hbc : b ≤ c) (hcd : c < d)
    (hcube : a ^ 3 + d ^ 3 = b ^ 3 + c ^ 3) :
    outerSum a d =
      (sumDefect a b c d * (innerGap b c ^ 2 + sumDefect a b c d ^ 2 / 3)) /
        shapeDefect a b c d := by
  exact (Int.ediv_eq_of_eq_mul_left (shapeDefect_ne_zero ha hab hbc hcd hcube)
    (outerSum_mul_shapeDefect hcube).symm).symm

/-- The four roots reconstructed without denominators from `s,h,l,q`.
These are algebraic identities for all natural roots, without order assumptions. -/
theorem twice_roots (a b c d : ℕ) :
    2 * (a : ℤ) = outerSum a d - outerGap a d ∧
    2 * (b : ℤ) = outerSum a d + sumDefect a b c d - innerGap b c ∧
    2 * (c : ℤ) = outerSum a d + sumDefect a b c d + innerGap b c ∧
    2 * (d : ℤ) = outerSum a d + outerGap a d := by
  dsimp [outerSum, outerGap, innerGap, sumDefect]
  omega

/-- The corresponding exact integer-division reconstruction formulas. -/
theorem root_reconstruction (a b c d : ℕ) :
    (a : ℤ) = (outerSum a d - outerGap a d) / 2 ∧
    (b : ℤ) = (outerSum a d + sumDefect a b c d - innerGap b c) / 2 ∧
    (c : ℤ) = (outerSum a d + sumDefect a b c d + innerGap b c) / 2 ∧
    (d : ℤ) = (outerSum a d + outerGap a d) / 2 := by
  obtain ⟨ha, hb, hc, hd⟩ := twice_roots a b c d
  omega

/-- Equality of `s,q,h,l` gives equality of all four natural roots, in order. -/
theorem roots_eq_of_coordinates_eq {a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : ℕ}
    (hsum : outerSum a₁ d₁ = outerSum a₂ d₂)
    (hdefect : sumDefect a₁ b₁ c₁ d₁ = sumDefect a₂ b₂ c₂ d₂)
    (houter : outerGap a₁ d₁ = outerGap a₂ d₂)
    (hinner : innerGap b₁ c₁ = innerGap b₂ c₂) :
    a₁ = a₂ ∧ b₁ = b₂ ∧ c₁ = c₂ ∧ d₁ = d₂ := by
  dsimp [outerSum, outerGap, innerGap, sumDefect] at hsum hdefect houter hinner
  omega

/-- Fixed `q,e,h,l` determine all roots of a cube collision when `e ≠ 0`.
No order is needed once nonvanishing of `e` is supplied. -/
theorem roots_eq_of_shape_eq {a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : ℕ}
    (hcubeOne : a₁ ^ 3 + d₁ ^ 3 = b₁ ^ 3 + c₁ ^ 3)
    (hcubeTwo : a₂ ^ 3 + d₂ ^ 3 = b₂ ^ 3 + c₂ ^ 3)
    (hshapeNonzero : shapeDefect a₁ b₁ c₁ d₁ ≠ 0)
    (hdefect : sumDefect a₁ b₁ c₁ d₁ = sumDefect a₂ b₂ c₂ d₂)
    (hshape : shapeDefect a₁ b₁ c₁ d₁ = shapeDefect a₂ b₂ c₂ d₂)
    (houter : outerGap a₁ d₁ = outerGap a₂ d₂)
    (hinner : innerGap b₁ c₁ = innerGap b₂ c₂) :
    a₁ = a₂ ∧ b₁ = b₂ ∧ c₁ = c₂ ∧ d₁ = d₂ := by
  have hfirst := three_mul_outerSum_mul_shapeDefect hcubeOne
  have hsecond := three_mul_outerSum_mul_shapeDefect hcubeTwo
  rw [← hdefect, ← hshape, ← hinner] at hsecond
  have hsum := sum_eq_of_shape_identity hshapeNonzero hfirst hsecond
  exact roots_eq_of_coordinates_eq hsum hdefect houter hinner

/-- For an ordered positive collision, nonvanishing in shape reconstruction
is automatic. The second collision need not even satisfy an order hypothesis. -/
theorem ordered_roots_eq_of_shape_eq {a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : ℕ}
    (ha : 0 < a₁) (hab : a₁ < b₁) (hbc : b₁ ≤ c₁) (hcd : c₁ < d₁)
    (hcubeOne : a₁ ^ 3 + d₁ ^ 3 = b₁ ^ 3 + c₁ ^ 3)
    (hcubeTwo : a₂ ^ 3 + d₂ ^ 3 = b₂ ^ 3 + c₂ ^ 3)
    (hdefect : sumDefect a₁ b₁ c₁ d₁ = sumDefect a₂ b₂ c₂ d₂)
    (hshape : shapeDefect a₁ b₁ c₁ d₁ = shapeDefect a₂ b₂ c₂ d₂)
    (houter : outerGap a₁ d₁ = outerGap a₂ d₂)
    (hinner : innerGap b₁ c₁ = innerGap b₂ c₂) :
    a₁ = a₂ ∧ b₁ = b₂ ∧ c₁ = c₂ ∧ d₁ = d₂ :=
  roots_eq_of_shape_eq hcubeOne hcubeTwo (shapeDefect_ne_zero ha hab hbc hcd hcubeOne)
    hdefect hshape houter hinner

/-- The shifted cube-difference expansion, multiplied by four. -/
theorem shifted_cube_expansion {a b c d : ℕ}
    (hcube : a ^ 3 + d ^ 3 = b ^ 3 + c ^ 3) :
    lowerGap a b * (3 * (2 * (a : ℤ) + lowerGap a b) ^ 2 + lowerGap a b ^ 2) =
      upperGap c d * (3 * (2 * (c : ℤ) + upperGap c d) ^ 2 + upperGap c d ^ 2) := by
  have hcubeZ : (a : ℤ) ^ 3 + d ^ 3 = b ^ 3 + c ^ 3 := by
    exact_mod_cast hcube
  dsimp [lowerGap, upperGap]
  nlinarith only [hcubeZ]

/-- The denominator-cleared shifted-gap Pell identity.
The right-hand side has the sign `-q * p`, not `q * p`. -/
theorem pell_identity {a b c d : ℕ}
    (hcube : a ^ 3 + d ^ 3 = b ^ 3 + c ^ 3) :
    3 * pellU a b ^ 2 - 3 * upperGap c d * lowerGap a b * pellV c d ^ 2 =
      -sumDefect a b c d * lowerGap a b *
        (3 * upperGap c d ^ 2 + 3 * upperGap c d * sumDefect a b c d +
          sumDefect a b c d ^ 2) := by
  have hshifted := shifted_cube_expansion hcube
  dsimp only [pellU, pellV]
  rw [lowerGap_eq_upperGap_add_sumDefect a b c d] at hshifted ⊢
  linear_combination (upperGap c d + sumDefect a b c d) * hshifted

/-- The ordered shape conclusions together, in the requested integer coordinates.
This is a local identity theorem, not a counting or density result. -/
theorem ordered_shape {a b c d : ℕ}
    (ha : 0 < a) (hab : a < b) (hbc : b ≤ c) (hcd : c < d)
    (hcube : a ^ 3 + d ^ 3 = b ^ 3 + c ^ 3) :
    let sumCoord : ℤ := (a : ℤ) + d
    let outerCoord : ℤ := (d : ℤ) - a
    let innerCoord : ℤ := (c : ℤ) - b
    let defectCoord : ℤ := (b : ℤ) + c - a - d
    let shapeCoord : ℤ := outerCoord ^ 2 - innerCoord ^ 2 -
      defectCoord * (sumCoord + defectCoord)
    0 < defectCoord ∧ (6 : ℤ) ∣ defectCoord ∧ 0 < shapeCoord ∧ Even shapeCoord ∧
      3 * sumCoord * shapeCoord = defectCoord * (3 * innerCoord ^ 2 + defectCoord ^ 2) ∧
      3 * shapeCoord * outerCoord ^ 2 - 3 * (shapeCoord + defectCoord ^ 2) * innerCoord ^ 2 =
        3 * shapeCoord ^ 2 + 3 * shapeCoord * defectCoord ^ 2 + defectCoord ^ 4 := by
  exact ⟨sumDefect_pos ha hab hbc hcd hcube, six_dvd_sumDefect hcube,
    shapeDefect_pos ha hab hbc hcd hcube, shapeDefect_even hcube,
    three_mul_outerSum_mul_shapeDefect hcube, shape_conic hcube⟩

/-- The shifted-gap conclusions together, including positivity of `t,q`.
All gaps and Pell coordinates in this statement are integers. -/
theorem ordered_shifted_gap {a b c d : ℕ}
    (ha : 0 < a) (hab : a < b) (hbc : b ≤ c) (hcd : c < d)
    (hcube : a ^ 3 + d ^ 3 = b ^ 3 + c ^ 3) :
    let shortGap : ℤ := (d : ℤ) - c
    let longGap : ℤ := (b : ℤ) - a
    let defectCoord : ℤ := (b : ℤ) + c - a - d
    let firstPell : ℤ := longGap * (2 * (a : ℤ) + longGap)
    let secondPell : ℤ := 2 * (c : ℤ) + shortGap
    0 < shortGap ∧ 0 < defectCoord ∧ longGap = shortGap + defectCoord ∧
      shortGap ^ 2 < (b : ℤ) * defectCoord ∧
      3 * firstPell ^ 2 - 3 * shortGap * longGap * secondPell ^ 2 =
        -defectCoord * longGap * (3 * shortGap ^ 2 + 3 * shortGap * defectCoord +
          defectCoord ^ 2) := by
  refine ⟨by omega, sumDefect_pos ha hab hbc hcd hcube,
    lowerGap_eq_upperGap_add_sumDefect a b c d,
    upperGap_sq_lt_mul_sumDefect ha hab hbc hcd hcube, pell_identity hcube⟩

end Erdos1206.CollisionShape
