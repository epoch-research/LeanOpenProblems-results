import Submission.DescartesReflection

/-! A rational two-parameter family of five rational-distance circle centers.
This is an auxiliary construction, not a proof of Erdős 213. -/
namespace Erdos213.DescartesPoleFamily
open DescartesReflection

def ratio (t : ℚ) : ℚ := (15*t^2+8*t+1)/(1-t^2)
def lengthRatio (t : ℚ) : ℚ := 4*(t^2+4*t+1)/(1-t^2)
def poleX (t s : ℚ) : ℚ := (t^2+4*t+1)*s/((t+2)*(1+s^2))
def poleY (t s : ℚ) : ℚ := (1+2*t-t*(t+2)*s^2)/((t+2)*(1+s^2))

def seed : Fin 5 → Fin 4 → ℚ :=
  ![![-1,0,0,1], ![2,-1,0,0], ![2,1,0,0], ![3,0,2,1], ![15,0,4,1]]

def circles (t s : ℚ) (i : Fin 5) : Fin 4 → ℚ :=
  invert (seed i) (poleX t s) (poleY t s)

def center (t s : ℚ) (i : Fin 5) : Fin 2 → ℚ :=
  ![circles t s i 1 / circles t s i 0, circles t s i 2 / circles t s i 0]

lemma seed_norm : ∀ i, circleNorm (seed i) = 1 := by
  decide +kernel

lemma seed_special : twicePair (seed 0) (seed 4) = -14 := by
  decide +kernel

lemma seed_tangent : ∀ i j, i ≠ j → ¬ (i = 0 ∧ j = 4) →
    ¬ (i = 4 ∧ j = 0) → twicePair (seed i) (seed j) = -2 := by
  decide +kernel

lemma ratio_square (t : ℚ) (ht : 1-t^2 ≠ 0) :
    lengthRatio t ^ 2 = ratio t ^ 2 + 14*ratio t + 1 := by
  unfold lengthRatio ratio
  field_simp
  ring

lemma pole_locus (t s : ℚ) (ht : 1-t^2 ≠ 0) (ht2 : t+2 ≠ 0) :
    (15+ratio t)*(poleX t s ^ 2+poleY t s ^ 2) -
      8*poleY t s + 1-ratio t = 0 := by
  have hs : 1+s^2 ≠ 0 := by positivity
  unfold poleX poleY ratio
  field_simp
  ring

lemma curvature_ratio (t s : ℚ) (ht : 1-t^2 ≠ 0) (ht2 : t+2 ≠ 0) :
    circles t s 4 0 = ratio t * circles t s 0 0 := by
  have h := pole_locus t s ht ht2
  change 15*(poleX t s ^ 2+poleY t s ^ 2)-2*0*poleX t s-
    2*4*poleY t s+1 = ratio t *
      (-1*(poleX t s ^ 2+poleY t s ^ 2)-2*0*poleX t s-2*0*poleY t s+1)
  linear_combination h

lemma special_distance_square (a b : Fin 4 → ℚ)
    (ha : circleNorm a = 1) (hb : circleNorm b = 1)
    (ha0 : a 0 ≠ 0) (hb0 : b 0 ≠ 0) (hab : twicePair a b = -14)
    (k l : ℚ) (hk : b 0 = k*a 0) (hl : l^2 = k^2+14*k+1) :
    (a 1/a 0-b 1/b 0)^2+(a 2/a 0-b 2/b 0)^2 = (l/b 0)^2 := by
  rw [center_distance_sq a b ha hb ha0 hb0, hab]
  field_simp
  rw [hk]
  linear_combination -(a 0)^2 * hl

lemma all_distance_squares (t s : ℚ) (ht : 1-t^2 ≠ 0) (ht2 : t+2 ≠ 0)
    (hcurv : ∀ i, circles t s i 0 ≠ 0) (i j : Fin 5) :
    ∃ d : ℚ, (center t s i 0-center t s j 0)^2+
      (center t s i 1-center t s j 1)^2 = d^2 := by
  have hn (k : Fin 5) : circleNorm (circles t s k) = 1 := by
    rw [circles, invert_norm, seed_norm]
  have hp (a b : Fin 5) : twicePair (circles t s a) (circles t s b) =
      twicePair (seed a) (seed b) := invert_pair _ _ _ _
  have hs : (center t s 0 0-center t s 4 0)^2+
      (center t s 0 1-center t s 4 1)^2 =
      (lengthRatio t/circles t s 4 0)^2 := by
    exact special_distance_square _ _ (hn 0) (hn 4) (hcurv 0) (hcurv 4)
      ((hp 0 4).trans seed_special) (ratio t) (lengthRatio t)
      (curvature_ratio t s ht ht2) (ratio_square t ht)
  by_cases hij : i=j
  · subst j
    exact ⟨0, by simp⟩
  by_cases h04 : i=0 ∧ j=4
  · rcases h04 with ⟨rfl,rfl⟩
    exact ⟨_,hs⟩
  by_cases h40 : i=4 ∧ j=0
  · rcases h40 with ⟨rfl,rfl⟩
    refine ⟨lengthRatio t/circles t s 4 0,?_⟩
    convert hs using 1
    ring
  refine ⟨1/circles t s i 0+1/circles t s j 0, ?_⟩
  exact tangent_center_distance_sq _ _ (hn i) (hn j) (hcurv i) (hcurv j)
    ((hp i j).trans (seed_tangent i j hij h04 h40))

/-- Recover the conic parameter from any non-line point of the ratio conic. -/
lemma conic_parameter (k l : ℚ) (h : l^2=k^2+14*k+1) (hk : k+15 ≠ 0) :
    let t := (l-4)/(k+15)
    1-t^2 ≠ 0 ∧ t+2 ≠ 0 ∧ ratio t=k ∧ lengthRatio t=l := by
  dsimp
  have hid : (k+15)^2-(l-4)^2 = 8*(2*k+l+26) := by
    linear_combination -h
  have haux : 2*k+l+26 ≠ 0 := by
    intro hh
    have hsq : (k+15)^2=0 := by nlinarith [sq_nonneg (k+15)]
    exact hk (sq_eq_zero_iff.mp hsq)
  have ht : 1-((l-4)/(k+15))^2 ≠ 0 := by
    intro hh
    have he : (k+15)^2-(l-4)^2=0 := by
      field_simp at hh
      linear_combination hh
    exact haux (by linarith)
  have ht2 : (l-4)/(k+15)+2 ≠ 0 := by
    intro hh
    have he : l+2*k+26=0 := by
      field_simp at hh
      linear_combination hh
    exact haux (by linarith)
  refine ⟨ht, ht2, ?_, ?_⟩
  · unfold ratio
    apply (div_eq_iff ht).2
    field_simp [hk]
    linear_combination (k+15)*h
  · unfold lengthRatio
    apply (div_eq_iff ht).2
    field_simp [hk]
    linear_combination (l-4)*h

/-- The ratio locus is a rational circle, except at the already known line case. -/
lemma ratio_locus_circle (k l u v : ℚ) (hk : 15+k ≠ 0)
    (hl : l^2=k^2+14*k+1)
    (hp : (15+k)*(u^2+v^2)-8*v+1-k=0) :
    u^2+(v-4/(15+k))^2=(l/(15+k))^2 := by
  field_simp
  linear_combination (15+k)*hp-hl

/-- The usual rational parametrization covers every circle point off its
vertical diameter. Those excluded points are not general-position poles here. -/
lemma circle_parameter (c r u v : ℚ) (hu : u ≠ 0)
    (h : u^2+(v-c)^2=r^2) :
    let s := u/(v-c+r)
    v-c+r ≠ 0 ∧ 1+s^2 ≠ 0 ∧
      u=2*r*s/(1+s^2) ∧ v=c+r*(1-s^2)/(1+s^2) := by
  have hd : v-c+r ≠ 0 := by
    intro hh
    have he : v-c = -r := by linarith
    rw [he] at h
    have hu2 : u^2=0 := by nlinarith
    exact hu (sq_eq_zero_iff.mp hu2)
  dsimp
  have hs : 1+(u/(v-c+r))^2 ≠ 0 := by positivity
  refine ⟨hd,hs,?_,?_⟩
  · apply (eq_div_iff hs).2
    field_simp
    linear_combination h
  · apply (sub_eq_iff_eq_add').mp
    apply (eq_div_iff hs).2
    field_simp
    linear_combination (v-c+r)*h

/-- Pairwise distances within the common-tangent circle pencil. -/
lemma pencil_distance_numerator (u v k l : ℚ) :
    let q := u^2+v^2
    let f := fun a => q*(a^2-1)-2*v*a+1
    let x := fun a => -(a^2-1)*u
    let y := fun a => a-(a^2-1)*v
    (x k*f l-x l*f k)^2+(y k*f l-y l*f k)^2 =
      (k-l)^2*((q*k*l-v*(k+l)+q+1)^2+u^2*((k-l)^2-4)) := by
  dsimp
  ring

#print axioms all_distance_squares
#print axioms conic_parameter
#print axioms ratio_locus_circle
#print axioms circle_parameter
#print axioms pencil_distance_numerator
end Erdos213.DescartesPoleFamily
