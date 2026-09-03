import FormalConjecturesUtil

/-! Exact arithmetic for two threefold-rotational orbits in characteristic 3.
No nondegenerate orbit pair or arbitrary-cardinality set is asserted to exist. -/

namespace Erdos213.ThreefoldOrbits

def coreNorm (x y : ℚ) : ℚ := x^2+3*y^2

def cross0 (x y : ℚ) : ℚ := x^2+3*(y-1)^2

def cross1 (x y : ℚ) : ℚ := (x+3/2)^2+3*(y+1/2)^2

def cross2 (x y : ℚ) : ℚ := (x-3/2)^2+3*(y+1/2)^2

/-- The quartic in three cross-distances. -/
def delta (a b c : ℚ) : ℚ :=
  (a^2)^2+(b^2)^2+(c^2)^2-a^2*b^2-a^2*c^2-b^2*c^2

/-- These are the four squared-length requirements for the orbit of
`x+y*sqrt(-3)` together with the orbit of `sqrt(-3)` under cube-root rotation. -/
def OrbitData (x y : ℚ) : Prop :=
  IsSquare (3*coreNorm x y) ∧ IsSquare (cross0 x y) ∧
    IsSquare (cross1 x y) ∧ IsSquare (cross2 x y)

lemma cross_sum (x y : ℚ) :
    cross0 x y+cross1 x y+cross2 x y = 3*coreNorm x y+9 := by
  dsimp [cross0,cross1,cross2,coreNorm]
  ring

lemma cross_discriminant (x y : ℚ) :
    cross0 x y^2+cross1 x y^2+cross2 x y^2-
      cross0 x y*cross1 x y-cross0 x y*cross2 x y-cross1 x y*cross2 x y =
        27*coreNorm x y := by
  dsimp [cross0,cross1,cross2,coreNorm]
  ring

lemma parameters_of_orbit_data {x y : ℚ} (h : OrbitData x y) :
    ∃ s a b c : ℚ, a^2+b^2+c^2 = s^2+9 ∧ delta a b c = 9*s^2 ∧
      x = (b^2-c^2)/6 ∧ y = (b^2+c^2-2*a^2)/18 := by
  obtain ⟨⟨s,hs⟩,⟨a,ha⟩,⟨b,hb⟩,⟨c,hc⟩⟩ := h
  have hs' : 3*coreNorm x y = s^2 := by nlinarith [hs]
  have ha' : cross0 x y = a^2 := by nlinarith [ha]
  have hb' : cross1 x y = b^2 := by nlinarith [hb]
  have hc' : cross2 x y = c^2 := by nlinarith [hc]
  refine ⟨s,a,b,c,?_,?_,?_,?_⟩
  · simpa only [hs',ha',hb',hc'] using cross_sum x y
  · have hd := cross_discriminant x y
    rw [ha',hb',hc'] at hd
    dsimp [delta]
    nlinarith [hd,hs']
  · dsimp [cross1,cross2] at hb' hc'
    nlinarith [hb',hc']
  · dsimp [cross0,cross1,cross2] at ha' hb' hc'
    nlinarith [ha',hb',hc']

lemma orbit_data_of_parameters {s a b c : ℚ}
    (hs : a^2+b^2+c^2 = s^2+9) (hd : delta a b c = 9*s^2) :
    OrbitData ((b^2-c^2)/6) ((b^2+c^2-2*a^2)/18) := by
  dsimp [OrbitData]
  refine ⟨⟨s,?_⟩,⟨a,?_⟩,⟨b,?_⟩,⟨c,?_⟩⟩
  · dsimp [coreNorm,delta] at *
    linear_combination hd/9
  all_goals
    dsimp [cross0,cross1,cross2,delta] at *
    linear_combination hd/27-hs/3

lemma rational_three_square {x y : ℚ} (h : x^2 = 3*y^2) : x = 0 ∧ y = 0 := by
  by_cases hy : y = 0
  · subst y
    norm_num at h
    exact ⟨h,rfl⟩
  · have hh : IsSquare (3 : ℚ) := by
      refine ⟨x/y, ?_⟩
      field_simp
      nlinarith [h]
    norm_num at hh

/-- Equal cross-distances force a zero third cross-distance and coincident
threefold orbits; they do not give a general-position six-point example. -/
lemma equal_cross_degenerate {s a b c : ℚ}
    (hs : a^2+b^2+c^2 = s^2+9) (hd : delta a b c = 9*s^2)
    (hab : a^2 = b^2) : c = 0 ∧ s^2 = 9 ∧ a^2 = 9 := by
  dsimp [delta] at hd
  rw [← hab] at hs hd
  have hf : (a^2-c^2-3*s)*(a^2-c^2+3*s) = 0 := by
    linear_combination hd
  have hc : c = 0 := by
    rcases mul_eq_zero.mp hf with h | h
    · have he : (s-3)^2 = 3*c^2 := by nlinarith [hs,h]
      exact (rational_three_square he).2
    · have he : (s+3)^2 = 3*c^2 := by nlinarith [hs,h]
      exact (rational_three_square he).2
  refine ⟨hc,?_,?_⟩
  · rw [hc] at hs hf
    nlinarith [sq_nonneg (s^2-9)]
  · rw [hc] at hs hf
    nlinarith [sq_nonneg (a^2-9)]

/-- An exact degenerate control: rational points on the common circumcircle. -/
lemma common_circle_control {u v : ℚ} (h : u^2+3*v^2 = 1) :
    let a := 6*v
    let b := 3*(v-u)
    let c := 3*(u+v)
    a^2+b^2+c^2 = (3 : ℚ)^2+9 ∧ delta a b c = 9*(3 : ℚ)^2 := by
  dsimp [delta]
  constructor
  · nlinarith [h]
  · linear_combination 81*(u^2+3*v^2+1)*h

#print axioms parameters_of_orbit_data
#print axioms orbit_data_of_parameters
#print axioms equal_cross_degenerate
#print axioms common_circle_control

end Erdos213.ThreefoldOrbits
