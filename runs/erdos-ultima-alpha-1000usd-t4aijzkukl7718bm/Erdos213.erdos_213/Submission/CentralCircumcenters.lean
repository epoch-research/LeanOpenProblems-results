import Submission.MixedCircumcenters

/-! A parallelogram and its four opposite circumcenters.
Central symmetry reduces the four missing distances to two square conditions.
No simultaneous nondegenerate solution, eight-point witness, or solution of
Erdős 213 is asserted. -/
namespace Erdos213.CentralCircumcenters
open MixedCircumcenters
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

def radiusSq (x y : ℚ) : ℚ := x^2+y^2
def tilt (x y : ℚ) : ℚ := (1-radiusSq x y)/(2*y)
def firstMissing (x y : ℚ) : ℚ := 2+(tilt x y^2-1)*radiusSq x y
def secondMissing (x y : ℚ) : ℚ := tilt x y^2-1+2*radiusSq x y

def source (x y : ℚ) : Fin 4 → V := ![(1,0),(-1,0),(x,y),(-x,-y)]
def dual (x y : ℚ) : Fin 4 → V :=
  ![(-tilt x y*y,tilt x y*x),(tilt x y*y,-tilt x y*x),
    (0,tilt x y),(0,-tilt x y)]

lemma source_noncollinear {x y : ℚ} (hy : y≠0) : Noncollinear (source x y) := by
  intro i
  fin_cases i
  · change area (-1,0) (x,y) (-x,-y)≠0
    dsimp [area,det]
    intro h
    apply hy
    nlinarith
  · change area (1,0) (x,y) (-x,-y)≠0
    dsimp [area,det]
    intro h
    apply hy
    nlinarith
  · change area (1,0) (-1,0) (-x,-y)≠0
    dsimp [area,det]
    intro h
    apply hy
    nlinarith
  · change area (1,0) (-1,0) (x,y)≠0
    dsimp [area,det]
    intro h
    apply hy
    nlinarith

lemma source_injective {x y : ℚ} (hy : y≠0) : Function.Injective (source x y) := by
  intro i j h
  have hx := congrArg Prod.fst h
  have hyy := congrArg Prod.snd h
  fin_cases i <;> fin_cases j <;> try rfl
  all_goals dsimp [source] at hx hyy
  all_goals exfalso; apply hy; linarith

lemma centers_eq_dual {x y : ℚ} (hy : y≠0) (i : Fin 4) :
    centers (source x y) i=dual x y i := by
  fin_cases i
  · change center (-1,0) (x,y) (-x,-y)=(-tilt x y*y,tilt x y*x)
    ext <;> dsimp [center,area,det,MixedCircumcenters.norm,tilt,radiusSq]
    all_goals ring_nf
    all_goals field_simp [hy]
    all_goals ring
  · change center (1,0) (x,y) (-x,-y)=(tilt x y*y,-tilt x y*x)
    ext <;> dsimp [center,area,det,MixedCircumcenters.norm,tilt,radiusSq]
    all_goals ring_nf
    all_goals field_simp [hy]
    all_goals ring
  · change center (1,0) (-1,0) (-x,-y)=(0,tilt x y)
    ext <;> dsimp [center,area,det,MixedCircumcenters.norm,tilt,radiusSq]
    all_goals ring_nf
    all_goals field_simp [hy]
    all_goals ring
  · change center (1,0) (-1,0) (x,y)=(0,-tilt x y)
    ext <;> dsimp [center,area,det,MixedCircumcenters.norm,tilt,radiusSq]
    all_goals ring_nf
    all_goals field_simp [hy]
    all_goals ring

lemma source_norm (x y : ℚ) (i j : Fin 4) :
    sqDist (source x y i) (source x y j)=
      (!![0,4,(x-1)^2+y^2,(x+1)^2+y^2;
          4,0,(x+1)^2+y^2,(x-1)^2+y^2;
          (x-1)^2+y^2,(x+1)^2+y^2,0,4*radiusSq x y;
          (x+1)^2+y^2,(x-1)^2+y^2,4*radiusSq x y,0] i j) := by
  fin_cases i <;> fin_cases j
  · change ((1 : ℚ)-(1))^2+((0 : ℚ)-(0))^2=0
    ring
  · change ((1 : ℚ)-(-1))^2+((0 : ℚ)-(0))^2=4
    ring
  · change ((1 : ℚ)-(x))^2+((0 : ℚ)-(y))^2=(x-1)^2+y^2
    ring
  · change ((1 : ℚ)-(-x))^2+((0 : ℚ)-(-y))^2=(x+1)^2+y^2
    ring
  · change ((-1 : ℚ)-(1))^2+((0 : ℚ)-(0))^2=4
    ring
  · change ((-1 : ℚ)-(-1))^2+((0 : ℚ)-(0))^2=0
    ring
  · change ((-1 : ℚ)-(x))^2+((0 : ℚ)-(y))^2=(x+1)^2+y^2
    ring
  · change ((-1 : ℚ)-(-x))^2+((0 : ℚ)-(-y))^2=(x-1)^2+y^2
    ring
  · change ((x : ℚ)-(1))^2+((y : ℚ)-(0))^2=(x-1)^2+y^2
    ring
  · change ((x : ℚ)-(-1))^2+((y : ℚ)-(0))^2=(x+1)^2+y^2
    ring
  · change ((x : ℚ)-(x))^2+((y : ℚ)-(y))^2=0
    ring
  · change ((x : ℚ)-(-x))^2+((y : ℚ)-(-y))^2=4*(x^2+y^2)
    ring
  · change ((-x : ℚ)-(1))^2+((-y : ℚ)-(0))^2=(x+1)^2+y^2
    ring
  · change ((-x : ℚ)-(-1))^2+((-y : ℚ)-(0))^2=(x-1)^2+y^2
    ring
  · change ((-x : ℚ)-(x))^2+((-y : ℚ)-(y))^2=4*(x^2+y^2)
    ring
  · change ((-x : ℚ)-(-x))^2+((-y : ℚ)-(-y))^2=0
    ring

lemma source_squares {x y : ℚ}
    (hr : IsSquare (radiusSq x y))
    (hp : IsSquare ((x+1)^2+y^2)) (hm : IsSquare ((x-1)^2+y^2)) :
    ∀ i j, IsSquare (sqDist (source x y i) (source x y j)) := by
  have h4 : IsSquare (4 : ℚ) := by norm_num
  have h4r := h4.mul hr
  intro i j
  rw [source_norm]
  fin_cases i <;> fin_cases j
  all_goals first | exact IsSquare.zero | exact h4 | exact h4r | exact hp | exact hm

lemma opposite_norm {x y : ℚ} (hy : y≠0) (i : Fin 4) :
    sqDist (source x y i) (centers (source x y) i)=
      if i.val<2 then firstMissing x y else secondMissing x y := by
  rw [centers_eq_dual hy]
  fin_cases i <;> dsimp
  all_goals dsimp [sqDist,MixedCircumcenters.norm,source,dual,firstMissing,secondMissing,tilt,radiusSq]
  all_goals field_simp
  all_goals ring

/-- With the three source square conditions, precisely two additional square
conditions are needed for all twenty-eight distances. -/
theorem mixed_squares_iff_two {x y : ℚ} (hy : y≠0)
    (hr : IsSquare (radiusSq x y))
    (hp : IsSquare ((x+1)^2+y^2)) (hm : IsSquare ((x-1)^2+y^2)) :
    (∀ i j, IsSquare (sqDist (mixed (source x y) i) (mixed (source x y) j))) ↔
      IsSquare (firstMissing x y) ∧ IsSquare (secondMissing x y) := by
  rw [MixedCircumcenters.mixed_squares_iff (source_noncollinear hy) (source_injective hy)]
  constructor
  · rintro ⟨_,h⟩
    constructor
    · simpa only [opposite_norm hy,Fin.val_zero,Nat.reduceLT,ite_true] using h 0
    · simpa only [opposite_norm hy,Fin.val_two,Nat.reduceLT,ite_false] using h 2
  · rintro ⟨hA,hB⟩
    refine ⟨source_squares hr hp hm,?_⟩
    intro i
    rw [opposite_norm hy]
    split_ifs <;> assumption

/-- The two-square criterion also holds for actual Euclidean distances. -/
theorem mixed_rational_iff_two {x y : ℚ} (hy : y≠0)
    (hr : IsSquare (radiusSq x y))
    (hp : IsSquare ((x+1)^2+y^2)) (hm : IsSquare ((x-1)^2+y^2)) :
    (∀ i j, dist (plane (mixed (source x y) i)) (plane (mixed (source x y) j))∈
      Set.range ((↑) : ℚ → ℝ)) ↔
      IsSquare (firstMissing x y) ∧ IsSquare (secondMissing x y) := by
  simp_rw [plane_rational_iff]
  exact mixed_squares_iff_two hy hr hp hm

lemma pythagorean_tilt_identity {x y : ℚ} (hy : y≠0) :
    1+tilt x y^2=(((x+1)^2+y^2)*((x-1)^2+y^2))/(2*y)^2 := by
  dsimp [tilt,radiusSq]
  field_simp
  ring

lemma pythagorean_tilt {x y : ℚ} (hy : y≠0)
    (hp : IsSquare ((x+1)^2+y^2)) (hm : IsSquare ((x-1)^2+y^2)) :
    IsSquare (1+tilt x y^2) := by
  rw [pythagorean_tilt_identity hy]
  exact (hp.mul hm).div (IsSquare.sq _)

lemma missing_sum (x y : ℚ) : firstMissing x y+secondMissing x y=
    (1+tilt x y^2)*(1+radiusSq x y) := by
  dsimp [firstMissing,secondMissing]; ring

/-- A necessary elliptic equation for the two additional square conditions.
It is not a rational-point classification and does not imply the source
square conditions in the reverse direction. -/
lemma missing_elliptic_identity (k r a b : ℚ)
    (ha : a^2=2+(k^2-1)*r^2) (hb : b^2=k^2-1+2*r^2) :
    (2*(k^2-1)*r*a*b)^2=
      (2*(k^2-1)*r^2)*(2*(k^2-1)*r^2+4)*
        (2*(k^2-1)*r^2+(k^2-1)^2) := by
  calc
    (2*(k^2-1)*r*a*b)^2 = (2*(k^2-1)*r)^2*a^2*b^2 := by ring
    _ = _ := by rw [ha,hb]; ring

lemma control_source :
    radiusSq (1/13) (112/195)=(113/195)^2 ∧
    ((1/13 : ℚ)+1)^2+(112/195)^2=(238/195)^2 ∧
    ((1/13 : ℚ)-1)^2+(112/195)^2=(212/195)^2 ∧
    tilt (1/13) (112/195)=451/780 := by norm_num [radiusSq,tilt]

lemma control_missing :
    firstMissing (1/13) (112/195)=41097387769/23134410000 ∧
    secondMissing (1/13) (112/195)=401/67600 := by
  norm_num [firstMissing,secondMissing,tilt,radiusSq]

lemma control_missing_not_square :
    ¬IsSquare (firstMissing (1/13) (112/195)) ∧
    ¬IsSquare (secondMissing (1/13) (112/195)) := by
  rw [control_missing.1,control_missing.2]
  decide +kernel

#print axioms centers_eq_dual
#print axioms mixed_rational_iff_two
#print axioms pythagorean_tilt
#print axioms missing_elliptic_identity
#print axioms control_missing_not_square
end
end Erdos213.CentralCircumcenters
