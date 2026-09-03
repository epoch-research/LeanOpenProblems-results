import FormalConjecturesUtil

/-! An exact six-point Morley-catalog control. All six points are in general
position and twelve of their fifteen distances are integers. The other three
are irrational, and every rational-distance subset has at most three points.
This is not a proof or disproof of the unrestricted Erdős conjecture. -/
open EuclideanGeometry
namespace Erdos213.MorleyControl
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

private lemma collinear_det_zero {a b c : ℝ²} (h : Collinear ℝ {a, b, c}) :
    (b 0 - a 0) * (c 1 - a 1) - (b 1 - a 1) * (c 0 - a 0) = 0 := by
  obtain ⟨v, hv⟩ := (collinear_iff_of_mem (by simp : a ∈ ({a,b,c} : Set ℝ²))).mp h
  obtain ⟨r, hr⟩ := hv b (by simp)
  obtain ⟨s, hs⟩ := hv c (by simp)
  subst b c
  simp
  ring

private lemma p4_dist_sq (a b : ℝ²) :
    dist a b ^ 2 = (a 0 - b 0)^2 + (a 1 - b 1)^2 := by
  simp [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq]

private def det3 {R : Type*} [CommRing R] (a b c d e f g h i : R) : R :=
  a*(e*i-f*h) - b*(d*i-f*g) + c*(d*h-e*g)

private noncomputable def latticePoint (D : ℕ) (x y : ℤ) : ℝ² := !₂[(x : ℝ), (y : ℝ)*Real.sqrt D]

private def latticeNorm (D : ℕ) (x y x' y' : ℤ) : ℤ :=
  (x-x')^2 + (D : ℤ)*(y-y')^2

private def latticeTriangle (x y : Fin n → ℤ) (i j k : Fin n) : ℤ :=
  (x j-x i)*(y k-y i) - (y j-y i)*(x k-x i)

private def latticeCircle (D : ℕ) (x y : Fin n → ℤ) (i j k l : Fin n) : ℤ :=
  det3 (x j-x i) (y j-y i) (latticeNorm D (x i) (y i) (x j) (y j))
    (x k-x i) (y k-y i) (latticeNorm D (x i) (y i) (x k) (y k))
    (x l-x i) (y l-y i) (latticeNorm D (x i) (y i) (x l) (y l))

private lemma latticePoint_dist_sq (D : ℕ) (x y x' y' : ℤ) :
    dist (latticePoint D x y) (latticePoint D x' y')^2 = (latticeNorm D x y x' y' : ℝ) := by
  rw [p4_dist_sq]
  simp only [latticePoint, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    latticeNorm]
  push_cast
  linear_combination ((y : ℝ)-y')^2 * (Real.sq_sqrt (show 0 ≤ (D : ℝ) by positivity))

private lemma lattice_not_collinear {D : ℕ} (hD : 0 < D) {x y : Fin n → ℤ}
    {i j k : Fin n} (ht : latticeTriangle x y i j k ≠ 0) :
    ¬Collinear ℝ {latticePoint D (x i) (y i), latticePoint D (x j) (y j),
      latticePoint D (x k) (y k)} := by
  intro h
  have hz := collinear_det_zero h
  have hz' : (latticeTriangle x y i j k : ℝ) * Real.sqrt D = 0 := by
    convert hz using 1
    simp [latticePoint, latticeTriangle]
    ring
  have hn : (latticeTriangle x y i j k : ℝ) ≠ 0 := by exact_mod_cast ht
  exact (mul_ne_zero hn (Real.sqrt_ne_zero'.mpr (by exact_mod_cast hD))) hz'

private lemma cospherical_det_zero {a b c d : ℝ²} (h : Cospherical {a,b,c,d}) :
    det3 (b 0-a 0) (b 1-a 1) (dist a b^2)
      (c 0-a 0) (c 1-a 1) (dist a c^2)
      (d 0-a 0) (d 1-a 1) (dist a d^2) = 0 := by
  obtain ⟨o,r,h⟩ := h
  have ha := congrArg (fun z : ℝ => z^2) (h a (by simp))
  have hb := congrArg (fun z : ℝ => z^2) (h b (by simp))
  have hc := congrArg (fun z : ℝ => z^2) (h c (by simp))
  have hd := congrArg (fun z : ℝ => z^2) (h d (by simp))
  simp only [p4_dist_sq] at ha hb hc hd ⊢
  unfold det3
  linear_combination
    ((c 0-a 0)*(d 1-a 1)-(d 0-a 0)*(c 1-a 1)) * (hb-ha) +
    ((d 0-a 0)*(b 1-a 1)-(b 0-a 0)*(d 1-a 1)) * (hc-ha) +
    ((b 0-a 0)*(c 1-a 1)-(c 0-a 0)*(b 1-a 1)) * (hd-ha)

private lemma lattice_not_cospherical {D : ℕ} (hD : 0 < D) {x y : Fin n → ℤ}
    {i j k l : Fin n} (ht : latticeCircle D x y i j k l ≠ 0) :
    ¬Cospherical {latticePoint D (x i) (y i), latticePoint D (x j) (y j),
      latticePoint D (x k) (y k), latticePoint D (x l) (y l)} := by
  intro h
  have hz := cospherical_det_zero h
  simp only [latticePoint_dist_sq] at hz
  have hz' : (latticeCircle D x y i j k l : ℝ) * Real.sqrt D = 0 := by
    convert hz using 1
    simp [latticePoint, latticeCircle, det3]
    ring
  have hn : (latticeCircle D x y i j k l : ℝ) ≠ 0 := by exact_mod_cast ht
  exact (mul_ne_zero hn (Real.sqrt_ne_zero'.mpr (by exact_mod_cast hD))) hz'


def x : Fin 6 → ℤ := ![0,48419487732,31042269258,29465036692,32445868247,27306662682]
def y : Fin 6 → ℤ := ![0,0,10221709680,2968769440,5401295965,5675448480]
noncomputable def point (i : Fin 6) : ℝ² := latticePoint 3 (x i) (y i)

/-- Equal colors label exactly the three missing opposite-vertex edges. -/
def color : Fin 6 → Fin 3 := ![0,1,2,2,0,1]

def length : Fin 6 → Fin 6 → ℕ :=
  !![0,48419487732,35736151542,29910352108,0,29022163482;
     48419487732,0,24807615126,19639551680,18511577830,0;
     35736151542,24807615126,0,0,8466360214,8715516576;
     29910352108,19639551680,0,0,5161096070,5161096070;
     0,18511577830,8466360214,5161096070,0,5161096070;
     29022163482,0,8715516576,5161096070,5161096070,0]

abbrev QPoint := ℚ × ℚ
def qpoint (i : Fin 6) : QPoint := (x i,y i)
def qmul (u v : QPoint) : QPoint := (u.1*v.1-3*u.2*v.2,u.1*v.2+u.2*v.1)
def qconj (u : QPoint) : QPoint := (u.1,-u.2)
def qcube (u : QPoint) : QPoint := qmul (qmul u u) u
def qnorm (u : QPoint) : ℚ := u.1^2+3*u.2^2
def qcross (u v : QPoint) : ℚ := u.1*v.2-u.2*v.1
def unitA : QPoint := (397/403,40/403)
def unitB : QPoint := (83/86,13/86)
def unitC : QPoint := qmul (1/2,1/2) (qconj (qmul unitA unitB))

def directions : Fin 6 → QPoint :=
  ![unitA,qconj unitB,qconj (qmul unitB unitB),
    qmul (qcube unitA) (qmul unitC unitC),qmul (qcube unitA) unitC,qmul unitA unitA]

lemma unit_parameters : qnorm unitA=1 ∧ qnorm unitB=1 ∧ qnorm unitC=1 ∧
    qmul (qmul unitA unitB) unitC = (1/2,1/2) := by
  norm_num [qnorm,qmul,qconj,unitA,unitB,unitC,Prod.mk.injEq]

/-- The exact scaled source formula and six defining line incidences.
No statement about arbitrary real angle trisection is used in the metric proof. -/
lemma source_formula :
    qpoint 0 = (0,0) ∧
    qpoint 1 = (6*(5203798902289/360)*(qcube unitC).2,0) ∧
    qpoint 2 = (6*(5203798902289/360)*(qcube unitB).2*(qcube unitA).1,
      6*(5203798902289/360)*(qcube unitB).2*(qcube unitA).2) := by
  have h0 : qpoint 0 = (0,0) := rfl
  have h1 : qpoint 1 = (48419487732,0) := rfl
  have h2 : qpoint 2 = (31042269258,10221709680) := rfl
  rw [h0,h1,h2]
  norm_num [qcube,qmul,qconj,unitA,unitB,unitC,Prod.mk.injEq]

lemma direction_norms (i : Fin 6) : qnorm (directions i)=1 := by
  fin_cases i <;> norm_num [qnorm,directions,qcube,qmul,qconj,unitA,unitB,unitC,
    Matrix.cons_val_succ,Matrix.cons_val_succ']

lemma inner_line_incidence :
    qcross (qpoint 3-qpoint 0) (directions 0)=0 ∧
    qcross (qpoint 3-qpoint 1) (directions 1)=0 ∧
    qcross (qpoint 4-qpoint 1) (directions 2)=0 ∧
    qcross (qpoint 4-qpoint 2) (directions 3)=0 ∧
    qcross (qpoint 5-qpoint 2) (directions 4)=0 ∧
    qcross (qpoint 5-qpoint 0) (directions 5)=0 := by
  have h0 : qpoint 0 = (0,0) := rfl
  have h1 : qpoint 1 = (48419487732,0) := rfl
  have h2 : qpoint 2 = (31042269258,10221709680) := rfl
  have h3 : qpoint 3 = (29465036692,2968769440) := rfl
  have h4 : qpoint 4 = (32445868247,5401295965) := rfl
  have h5 : qpoint 5 = (27306662682,5675448480) := rfl
  have d0 : directions 0 = unitA := rfl
  have d1 : directions 1 = qconj unitB := rfl
  have d2 : directions 2 = qconj (qmul unitB unitB) := rfl
  have d3 : directions 3 = qmul (qcube unitA) (qmul unitC unitC) := rfl
  have d4 : directions 4 = qmul (qcube unitA) unitC := rfl
  have d5 : directions 5 = qmul unitA unitA := rfl
  rw [h0,h1,h2,h3,h4,h5,d0,d1,d2,d3,d4,d5]
  norm_num [qcross,qcube,qmul,qconj,unitA,unitB,unitC]

lemma point_injective : Function.Injective point := by
  have hx : Function.Injective x := by decide
  intro i j hij
  apply hx
  have he := congrArg (fun z : ℝ² => z 0) hij
  change (x i : ℝ) = (x j : ℝ) at he
  exact_mod_cast he

lemma point_dist_sq (i j : Fin 6) :
    dist (point i) (point j)^2 = (latticeNorm 3 (x i) (y i) (x j) (y j) : ℝ) :=
  latticePoint_dist_sq 3 _ _ _ _

lemma rational_distance_iff (i j : Fin 6) :
    dist (point i) (point j) ∈ Set.range ((↑) : ℚ → ℝ) ↔
      IsSquare (latticeNorm 3 (x i) (y i) (x j) (y j) : ℚ) := by
  constructor
  · rintro ⟨r,hr⟩
    refine ⟨r,?_⟩
    have h := point_dist_sq i j
    rw [← hr] at h
    have hh : (latticeNorm 3 (x i) (y i) (x j) (y j) : ℝ) = (r : ℝ)*(r : ℝ) := by
      nlinarith [h]
    exact_mod_cast hh
  · rintro ⟨r,hr⟩
    refine ⟨|r|,?_⟩
    rw [Rat.cast_abs]
    have h := point_dist_sq i j
    have hh : (latticeNorm 3 (x i) (y i) (x j) (y j) : ℝ) = (r : ℝ)*(r : ℝ) := by
      exact_mod_cast hr
    nlinarith [h,hh,abs_nonneg (r : ℝ),sq_abs (r : ℝ),dist_nonneg (x := point i) (y := point j)]

lemma rational_graph (i j : Fin 6) :
    dist (point i) (point j) ∈ Set.range ((↑) : ℚ → ℝ) ↔
      i=j ∨ color i ≠ color j := by
  rw [rational_distance_iff]
  fin_cases i <;> fin_cases j <;>
    norm_num [latticeNorm,x,y,color,Rat.isSquare_intCast_iff,
      Matrix.cons_val_succ,Matrix.cons_val_succ'] <;> decide

lemma integer_length (i j : Fin 6) (h : i=j ∨ color i ≠ color j) :
    dist (point i) (point j) = length i j := by
  have hn : ∀ i j : Fin 6, i=j ∨ color i ≠ color j →
      latticeNorm 3 (x i) (y i) (x j) (y j) = (length i j : ℤ)^2 := by decide
  have he := point_dist_sq i j
  rw [hn i j h] at he
  push_cast at he
  nlinarith [he,dist_nonneg (x := point i) (y := point j),
    Nat.cast_nonneg (α := ℝ) (length i j)]

lemma inner_equilateral :
    dist (point 3) (point 4) = 5161096070 ∧
    dist (point 4) (point 5) = 5161096070 ∧
    dist (point 5) (point 3) = 5161096070 := by
  constructor
  · exact integer_length 3 4 (by decide)
  constructor
  · exact integer_length 4 5 (by decide)
  · exact integer_length 5 3 (by decide)

lemma no_three_collinear : NonTrilinear (Set.range point) := by
  have ht : ∀ i j k : Fin 6, i ≠ j → j ≠ k → i ≠ k →
      latticeTriangle x y i j k ≠ 0 := by decide
  rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩ _ ⟨k,rfl⟩ hij hjk hik
  exact lattice_not_collinear (by decide : 0 < 3) (ht i j k
    (fun he => hij (he ▸ rfl)) (fun he => hjk (he ▸ rfl)) (fun he => hik (he ▸ rfl)))

lemma no_four_concyclic (Q : Set ℝ²) (hQ : Q ⊆ Set.range point) (hcard : Q.ncard=4) :
    ¬ Cospherical Q := by
  have hc : ∀ i j k l : Fin 6,
      i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l →
      latticeCircle 3 x y i j k l ≠ 0 := by decide
  obtain ⟨a,b,c,d,hab,hac,had,hbc,hbd,hcd,hset⟩ := Set.ncard_eq_four.mp hcard
  subst Q
  obtain ⟨i,rfl⟩ := hQ (by simp : a ∈ ({a,b,c,d} : Set ℝ²))
  obtain ⟨j,rfl⟩ := hQ (by simp : b ∈ ({point i,b,c,d} : Set ℝ²))
  obtain ⟨k,rfl⟩ := hQ (by simp : c ∈ ({point i,point j,c,d} : Set ℝ²))
  obtain ⟨l,rfl⟩ := hQ (by simp : d ∈ ({point i,point j,point k,d} : Set ℝ²))
  exact lattice_not_cospherical (by decide : 0 < 3) (hc i j k l
    (fun he => hab (he ▸ rfl)) (fun he => hac (he ▸ rfl)) (fun he => had (he ▸ rfl))
    (fun he => hbc (he ▸ rfl)) (fun he => hbd (he ▸ rfl)) (fun he => hcd (he ▸ rfl)))

/-- Pigeonhole obstruction, using the exact three missing edges. -/
lemma rational_subconfiguration_card (T : Finset (Fin 6))
    (h : ∀ i ∈ T, ∀ j ∈ T, i ≠ j →
      dist (point i) (point j) ∈ Set.range ((↑) : ℚ → ℝ)) : T.card ≤ 3 := by
  have hc : Set.InjOn color (↑T : Set (Fin 6)) := by
    intro i hi j hj he
    by_contra hn
    exact ((rational_graph i j).mp (h i hi j hj hn)).resolve_left hn he
  have he : (T.image color).card = T.card := Finset.card_image_iff.mpr hc
  rw [← he]
  exact le_trans (Finset.card_le_univ _) (by decide)

lemma rational_subset_ncard (S : Set ℝ²) (hS : S ⊆ Set.range point)
    (h : S.Pairwise fun a b => dist a b ∈ Set.range ((↑) : ℚ → ℝ)) : S.ncard ≤ 3 := by
  classical
  let f : ℝ² → Fin 3 := color ∘ Function.invFun point
  have hinv := Function.leftInverse_invFun point_injective
  have hf : Set.InjOn f S := by
    intro a ha b hb hab
    obtain ⟨i,rfl⟩ := hS ha
    obtain ⟨j,rfl⟩ := hS hb
    change color (Function.invFun point (point i)) = color (Function.invFun point (point j)) at hab
    rw [hinv i,hinv j] at hab
    by_cases hij : i=j
    · exact congrArg point hij
    exact False.elim (((rational_graph i j).mp
      (h ha hb (point_injective.ne hij))).resolve_left hij hab)
  have hc := Set.ncard_le_ncard_of_injOn f
    (fun a (_ : a ∈ S) => Set.mem_univ (f a)) hf Set.finite_univ
  simpa using hc

lemma sample_card : (Set.range point).ncard=6 := by
  rw [Set.ncard_range_of_injective point_injective]
  simp

lemma missing_edge :
    dist (point 0) (point 4) ∉ Set.range ((↑) : ℚ → ℝ) := by
  rw [rational_graph]
  decide

lemma no_common_scale (c : ℝ) (hc : c ≠ 0) :
    ¬ (∀ i j : Fin 6, c*dist (point i) (point j) ∈ Set.range ((↑) : ℚ → ℝ)) := by
  intro h
  have hd : dist (point 0) (point 1) = 48419487732 := integer_length 0 1 (by decide)
  obtain ⟨q,hq⟩ := h 0 1
  rw [hd] at hq
  have hq' : (q : ℝ)/48419487732 = c := by linarith
  obtain ⟨r,hr⟩ := h 0 4
  apply missing_edge
  refine ⟨r/(q/48419487732),?_⟩
  push_cast
  rw [hq']
  apply (div_eq_iff hc).mpr
  simpa [mul_comm] using hr

#print axioms unit_parameters
#print axioms source_formula
#print axioms direction_norms
#print axioms inner_line_incidence
#print axioms rational_subset_ncard
#print axioms sample_card
#print axioms rational_graph
#print axioms integer_length
#print axioms inner_equilateral
#print axioms no_three_collinear
#print axioms no_four_concyclic
#print axioms rational_subconfiguration_card
#print axioms no_common_scale
end Erdos213.MorleyControl
