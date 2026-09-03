import FormalConjecturesUtil

/-!
Three exact plane obstructions for a possible classification of quadratic
triple-representation families. This file does not classify all such families
and does not settle the density conjecture.
-/

namespace Erdos1206.QuadraticTriplePlaneObstructions

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private lemma norm_pos (r : K) : 0 < r^2-r+1 := by
  nlinarith [sq_nonneg (r-1/2)]

/-- The first residual quadric for the inconsistent difference orientations. -/
def diffQ₁ (r s t B D F : K) : K :=
  let b := (t+1)*B
  let d := (t+1)*D
  let f := (t+1)*F
  let e := (r-s)*B+(s+1)*F+(t-r)*D
  let a := e+s*b-s*f
  let c := f+t*d-t*e
  r*(a^2+a*c+c^2)+(b^2+b*d+d^2)

/-- The second residual quadric for the inconsistent difference orientations. -/
def diffQ₂ (r s t B D F : K) : K :=
  let b := (t+1)*B
  let f := (t+1)*F
  let e := (r-s)*B+(s+1)*F+(t-r)*D
  let a := e+s*b-s*f
  s*(a^2+a*e+e^2)+(b^2+b*f+f^2)

private def dx (r t : K) : K :=
  (r+1)*(r^2*t^2-r^2*t+r^2+2*r*t^2-2*r*t-r+t^2+2*t+1)
private def dy (r s t : K) : K := 3*s*(r-t)^2
private def mx (r t : K) : K :=
  -(r+1)^2*(2*r*t^2-2*r*t+2*r-t^2-2*t-1)
private def my (r s t : K) : K := -6*s*(r+1)*(r-t)

private lemma diff_coefficients (r s t : K) :
    diffQ₁ r s t 0 1 0 = dx r t ∧
    diffQ₂ r s t 0 1 0 = dy r s t ∧
    diffQ₁ r s t 1 1 1 - diffQ₁ r s t 1 0 1 - diffQ₁ r s t 0 1 0 = mx r t ∧
    diffQ₂ r s t 1 1 1 - diffQ₂ r s t 1 0 1 - diffQ₂ r s t 0 1 0 = my r s t := by
  dsimp [diffQ₁, diffQ₂, dx, dy, mx, my]
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

/-- With negative, nondegenerate direction ratios, these two residual
quadrics cannot be proportional. This is only one orientation case. -/
theorem inconsistent_difference_not_proportional
    {r s t : K} (hr : r < 0) (hs : s ≠ 0) (ht : t < 0)
    (hr₁ : r ≠ -1) (ht₁ : t ≠ -1) :
    ¬ ∃ l : K, ∀ B D F : K, diffQ₁ r s t B D F = l * diffQ₂ r s t B D F := by
  rintro ⟨l, hl⟩
  obtain ⟨hxd, hyd, hxm, hym⟩ := diff_coefficients r s t
  have hd : dx r t = l * dy r s t := by
    rw [← hxd, ← hyd]
    exact hl 0 1 0
  have hm : mx r t = l * my r s t := by
    rw [← hxm, ← hym, hl 1 1 1, hl 1 0 1, hl 0 1 0]
    ring
  have hz : dy r s t * mx r t - dx r t * my r s t = 0 := by
    rw [hd, hm]
    ring
  have hi : dy r s t * mx r t - dx r t * my r s t =
      3*s*(r-t)*(t+1)^2*(r+1)^2*((2*r-1)*t-r+2) := by
    dsimp [dx, dy, mx, my]
    ring
  rw [hi] at hz
  have hp : 0 < (2*r-1)*t-r+2 := by
    have hh : 0 < (2*r-1)*t := mul_pos_of_neg_of_neg (by linarith) ht
    linarith
  have hrp : r+1 ≠ 0 := by intro h; apply hr₁; linarith
  have htp : t+1 ≠ 0 := by intro h; apply ht₁; linarith
  have hrt : r=t := by
    by_contra hrt
    have hrt' : r-t ≠ 0 := sub_ne_zero.mpr hrt
    have hn : 3*s*(r-t)*(t+1)^2*(r+1)^2*((2*r-1)*t-r+2) ≠ 0 := by
      positivity
    exact hn hz
  subst t
  have hdy : dy r s r = 0 := by simp [dy]
  have hdx : dx r r = (r+1)^3*(r^2-r+1) := by dsimp [dx]; ring
  rw [hdy, mul_zero, hdx] at hd
  have hq := norm_pos r
  have hn : (r+1)^3*(r^2-r+1) ≠ 0 := by positivity
  exact hn hd

/-- The first residual quadric when the third relation is proportionality
of the second and third pair sums. -/
def sumQ₁ (r s k B D F : K) : K :=
  let b := (1-k)*B
  let d := (1-k)*D
  let a := (r-k*s)*B-(r+1)*D+k*(s+1)*F
  let c := a-r*(b-d)
  r*(a^2+a*c+c^2)+(b^2+b*d+d^2)

/-- The second residual quadric in the same proportional-sum case. -/
def sumQ₂ (r s k B D F : K) : K :=
  let b := (1-k)*B
  let f := (1-k)*F
  let a := (r-k*s)*B-(r+1)*D+k*(s+1)*F
  let e := a-s*(b-f)
  s*(a^2+a*e+e^2)+(b^2+b*f+f^2)

private def sdx (r k : K) : K :=
  (r+1)*(k^2*r^2-k^2*r+k^2+k*r^2+2*k*r-2*k+r^2+2*r+1)
private def sdy (r s : K) : K := 3*s*(r+1)^2
private def smx (r k : K) : K :=
  -(r+1)^2*(2*k^2*r-k^2+2*k*r+2*k+2*r-1)
private def smy (r s k : K) : K := -6*s*(k+r)*(r+1)

private lemma sum_coefficients (r s k : K) :
    sumQ₁ r s k 0 1 0 = sdx r k ∧
    sumQ₂ r s k 0 1 0 = sdy r s ∧
    sumQ₁ r s k 1 1 1 - sumQ₁ r s k 1 0 1 - sumQ₁ r s k 0 1 0 = smx r k ∧
    sumQ₂ r s k 1 1 1 - sumQ₂ r s k 1 0 1 - sumQ₂ r s k 0 1 0 = smy r s k := by
  dsimp [sumQ₁, sumQ₂, sdx, sdy, smx, smy]
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

/-- A positive, nontrivial ratio of pair sums is incompatible with
proportional residual quadrics in this mixed orientation pattern. -/
theorem one_sum_not_proportional {r s k : K}
    (hs : s ≠ 0) (hr₁ : r ≠ -1) (hk : 0 < k) (hk₁ : k ≠ 1) :
    ¬ ∃ l : K, ∀ B D F : K, sumQ₁ r s k B D F = l * sumQ₂ r s k B D F := by
  rintro ⟨l, hl⟩
  obtain ⟨hxd, hyd, hxm, hym⟩ := sum_coefficients r s k
  have hd : sdx r k = l * sdy r s := by
    rw [← hxd, ← hyd]
    exact hl 0 1 0
  have hm : smx r k = l * smy r s k := by
    rw [← hxm, ← hym, hl 1 1 1, hl 1 0 1, hl 0 1 0]
    ring
  have hz : sdy r s * smx r k - sdx r k * smy r s k = 0 := by
    rw [hd, hm]
    ring
  have hi : sdy r s * smx r k - sdx r k * smy r s k =
      3*s*(k-1)^2*(r+1)^2*(2*k*(r^2-r+1)+(r+1)^2) := by
    dsimp [sdx, sdy, smx, smy]
    ring
  rw [hi] at hz
  have hrp : r+1 ≠ 0 := by intro h; apply hr₁; linarith
  have hkp : k-1 ≠ 0 := sub_ne_zero.mpr hk₁
  have hq := norm_pos r
  have hp : 0 < 2*k*(r^2-r+1)+(r+1)^2 := by positivity
  have hn : 3*s*(k-1)^2*(r+1)^2*(2*k*(r^2-r+1)+(r+1)^2) ≠ 0 := by
    positivity
  exact hn hz

/-- Residual quadrics for the consistent difference orientations after
eliminating the nontrivial relation among the three second coordinates. -/
def consistentQ₁ (r s t U D F : K) : K :=
  let a := (s-r)*U
  let b := (t-r)*D+(s-t)*F
  let d := (s-r)*D
  let c := a-r*(b-d)
  r*(a^2+a*c+c^2)+(b^2+b*d+d^2)

def consistentQ₂ (r s t U D F : K) : K :=
  let a := (s-r)*U
  let b := (t-r)*D+(s-t)*F
  let f := (s-r)*F
  let e := a-s*(b-f)
  s*(a^2+a*e+e^2)+(b^2+b*f+f^2)

/-- In the consistent orientation pattern, unequal direction ratios prevent
proportionality. Equal direction ratios are the collinear case. -/
theorem consistent_unequal_not_proportional {r s t : K}
    (hr : r ≠ 0) (hs : s ≠ 0) (ht : t ≠ 0) (hrs : s ≠ r) :
    ¬ ∃ l : K, ∀ U D F : K,
      consistentQ₁ r s t U D F = l * consistentQ₂ r s t U D F := by
  rintro ⟨l,hl⟩
  let x := consistentQ₁ r s t
  let y := consistentQ₂ r s t
  have hz : y 1 0 0*(x 1 1 0-x 1 0 0-x 0 1 0)-
      x 1 0 0*(y 1 1 0-y 1 0 0-y 0 1 0)=0 := by
    dsimp only [x,y]
    rw [hl 1 1 0,hl 1 0 0,hl 0 1 0]
    ring
  have he : y 1 0 0*(x 1 1 0-x 1 0 0-x 0 1 0)-
      x 1 0 0*(y 1 1 0-y 1 0 0-y 0 1 0)=9*r*s*t*(s-r)^4 := by
    dsimp [x,y,consistentQ₁,consistentQ₂]
    ring
  rw [he] at hz
  have hsr : s-r ≠ 0 := sub_ne_zero.mpr hrs
  have hn : 9*r*s*t*(s-r)^4 ≠ 0 := by positivity
  exact hn hz

#print axioms consistent_unequal_not_proportional

#print axioms inconsistent_difference_not_proportional
#print axioms one_sum_not_proportional

end Erdos1206.QuadraticTriplePlaneObstructions
