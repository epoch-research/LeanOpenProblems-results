import FormalConjectures.Util.ProblemImports

open Nat Finset
open scoped BigOperators

namespace Work

local notation "r3" => Real.sqrt 3
local notation "r5" => Real.sqrt 5
local notation "r15" => Real.sqrt 15

/-- The purely algebraic last step of the proof. `F` is the unweighted
period, `D` its logarithmic derivative, and `H,E` are the two elliptic
period products occurring in Bailey's reduction. -/
lemma final_algebra (F D H E p : ℝ)
    (h3 : r3 ^ 2 = 3) (h5 : r5 ^ 2 = 5)
    (h15 : r15 = r3 * r5)
    (hF : F = 7 * r15 / 24 * H)
    (hD : 34320 * D +
      (53900 + 21560*r3 + 10780*r5 + 8043*r15) * H -
      (107800 + 21560*r5) * E = 0)
    (hp : -12*p -
      (15 + 6*r3 + 3*r5 + 2*r15) * H +
      (30 + 6*r5) * E = 0) :
    4290 * D + 367 * F = 5390 * p := by
  rw [hF]
  rw [h15] at *
  linear_combination (1 / 8 : ℝ) * hD + (2695 / 6 : ℝ) * hp <;>
    rw [h5] <;> ring

/-- Algebraic elimination of the cubic and quintic isogeny relations and
Legendre's relation. All periods here use the normalization `2/π`. -/
lemma period_algebra (h1 e1 h2 e2 hc2 ec2 p : ℝ)
    (h3 : r3 ^ 2 = 3) (h5 : r5 ^ 2 = 5) (h15 : r15 = r3 * r5)
    (hcub0 : h2 = (r15 - r3) / 2 * h1)
    (hcub1 : h2 - e2 = (r15-r3)/2 *
      (((r3/6-1/4)*r5+r3/6-1/4) * h1 +
       ((r5+3)/2) * (h1-e1)))
    (hquin0 : hc2 = (5-r5)/2 * h1)
    (hquin1 : hc2 - ec2 = (5-r5)/2 *
      (((r3/10-1/4)*r5+r3/2-1/4) * h1 +
       ((r5+3)/2) * (h1-e1)))
    (hleg : e2*hc2 + ec2*h2 - h2*hc2 = 2*p) :
    -12*p - (15+6*r3+3*r5+2*r15)*(h1*h2) +
      (30+6*r5)*(e1*h2) = 0 := by
  rw [h15] at *
  simp only [hcub0, hquin0] at hcub1 hquin1 hleg ⊢
  have he2 : e2 = (r3*r5-r3)/2 * h1 - (r3*r5-r3)/2 *
      (((r3/6-1/4)*r5+r3/6-1/4)*h1 + ((r5+3)/2)*(h1-e1)) := by
    linarith [hcub1]
  have hec2 : ec2 = (5-r5)/2*h1 - (5-r5)/2 *
      (((r3/10-1/4)*r5+r3/2-1/4)*h1 + ((r5+3)/2)*(h1-e1)) := by
    linarith [hquin1]
  rw [he2, hec2] at hleg
  linear_combination (6 : ℝ) * hleg +
    (-h1*r3*(r5-1)*(-30*e1+8*h1*r3+15*h1)/20) * h5


lemma sqrt_relations :
    Real.sqrt 3 ^ 2 = 3 ∧ Real.sqrt 5 ^ 2 = 5 ∧
      Real.sqrt 15 = Real.sqrt 3 * Real.sqrt 5 := by
  constructor
  · norm_num
  constructor
  · norm_num
  · rw [← Real.sqrt_mul (by norm_num : 0 ≤ (3:ℝ))]
    norm_num

end Work
