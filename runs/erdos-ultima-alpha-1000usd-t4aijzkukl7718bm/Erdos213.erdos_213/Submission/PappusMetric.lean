import FormalConjecturesUtil

/-! Exact metric controls for a Pappus-completion proposal.
This file does not prove or disprove the unrestricted Erdős conjecture. -/

open EuclideanGeometry
namespace Erdos213.PappusMetric

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

abbrev QPoint := ℚ × ℚ

def qDistSq (p q : QPoint) : ℚ := (p.1-q.1)^2+(p.2-q.2)^2

noncomputable def embed (p : QPoint) : ℝ² := !₂[(p.1 : ℝ),(p.2 : ℝ)]

lemma embed_dist_sq (p q : QPoint) :
    dist (embed p) (embed q)^2 = (qDistSq p q : ℝ) := by
  simp [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq, embed, qDistSq]

lemma rational_distance_iff (p q : QPoint) :
    dist (embed p) (embed q) ∈ Set.range ((↑) : ℚ → ℝ) ↔ IsSquare (qDistSq p q) := by
  constructor
  · rintro ⟨r,hr⟩
    refine ⟨r,?_⟩
    have h := embed_dist_sq p q
    rw [← hr] at h
    exact_mod_cast (by nlinarith [h] : (qDistSq p q : ℝ) = (r : ℝ)*(r : ℝ))
  · rintro ⟨r,hr⟩
    refine ⟨|r|,?_⟩
    rw [Rat.cast_abs]
    have h := embed_dist_sq p q
    have hh : (qDistSq p q : ℝ) = (r : ℝ)*(r : ℝ) := by exact_mod_cast hr
    nlinarith [h,hh,abs_nonneg (r : ℝ),sq_abs (r : ℝ),dist_nonneg (x := embed p) (y := embed q)]

/-- The intersection of the lines from (a,0) to (0,d), and from (b,0) to (0,c).
The nonparallel assumption is supplied to the incidence lemmas below. -/
def intersection (a b c d : ℚ) : QPoint :=
  (a*b*(d-c)/(b*d-a*c), c*d*(b-a)/(b*d-a*c))

lemma intersection_first (a b c d : ℚ) (h : b*d-a*c ≠ 0) :
    intersection a b c d =
      ((1-c*(b-a)/(b*d-a*c))*a, (c*(b-a)/(b*d-a*c))*d) := by
  apply Prod.ext <;> dsimp [intersection] <;> field_simp <;> ring

lemma intersection_second (a b c d : ℚ) (h : b*d-a*c ≠ 0) :
    intersection a b c d =
      ((1-d*(b-a)/(b*d-a*c))*b, (d*(b-a)/(b*d-a*c))*c) := by
  apply Prod.ext <;> dsimp [intersection] <;> field_simp <;> ring

def triangle (p q r : QPoint) : ℚ :=
  (q.1-p.1)*(r.2-p.2)-(q.2-p.2)*(r.1-p.1)

/-- The Pappus incidence identity, before imposing any metric conditions. -/
lemma pappus (a b c d e f : ℚ)
    (h01 : b*e-a*d ≠ 0) (h02 : c*f-a*d ≠ 0) (h12 : c*f-b*e ≠ 0) :
    triangle (intersection a b d e) (intersection a c d f)
      (intersection b c e f) = 0 := by
  dsimp [triangle,intersection]
  field_simp
  ring

/-- The standard elliptic-duplication identity supplies a second common leg
of two rational right triangles. This is a polynomial identity only. -/
lemma second_common_leg (a b c u v : ℚ)
    (hu : u^2=c^2+a^2) (hv : v^2=c^2+b^2) :
    (c^4-a^2*b^2)^2+a^2*(2*c*u*v)^2 =
      (c^4+2*a^2*c^2+a^2*b^2)^2 ∧
    (c^4-a^2*b^2)^2+b^2*(2*c*u*v)^2 =
      (c^4+2*b^2*c^2+a^2*b^2)^2 := by
  constructor
  · linear_combination 4*a^2*c^2*v^2*hu + 4*a^2*c^2*(c^2+a^2)*hv
  · linear_combination 4*b^2*c^2*v^2*hu + 4*b^2*c^2*(c^2+a^2)*hv

def source : Fin 6 → QPoint :=
  ![(5,0),(-5,0),(9,0),(0,12),(0,2079/520),(0,-12)]

def sourceLength : Fin 6 → Fin 6 → ℚ := fun i j =>
  (!![0,5200,2080,6760,3329,6760;
      5200,0,7280,6760,3329,6760;
      2080,7280,0,7800,5121,7800;
      6760,6760,7800,0,4161,12480;
      3329,3329,5121,4161,0,8319;
      6760,6760,7800,12480,8319,0] i j)/520

lemma source_length_certificate : ∀ i j, qDistSq (source i) (source j) =
    (sourceLength i j)^2 := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [qDistSq,source,sourceLength,Matrix.cons_val_succ,Matrix.cons_val_succ']

lemma source_rational_distances (i j : Fin 6) :
    dist (embed (source i)) (embed (source j)) ∈ Set.range ((↑) : ℚ → ℝ) := by
  apply (rational_distance_iff _ _).mpr
  exact ⟨sourceLength i j, by rw [source_length_certificate]; ring⟩

def added : Fin 3 → QPoint :=
  ![(-6935/2773,16632/2773),(45/7,24/7),(-2773/339,4312/565)]

lemma added_intersections :
    added 0 = intersection 5 (-5) 12 (2079/520) ∧
    added 1 = intersection 5 9 12 (-12) ∧
    added 2 = intersection (-5) 9 (2079/520) (-12) := by
  norm_num [added,intersection,Matrix.cons_val_succ,Matrix.cons_val_succ']
  rfl

lemma added_collinear : triangle (added 0) (added 1) (added 2) = 0 := by
  change triangle (-6935/2773,16632/2773) (45/7,24/7) (-2773/339,4312/565) = 0
  norm_num [triangle]

lemma added_missing_distance_squared : qDistSq (added 1) (source 1) = 6976/49 := by
  norm_num [qDistSq,added,source]

/-- In particular, source rationality and Pappus incidence do not imply
rationality of all of the new distances. -/
lemma added_missing_distance_irrational :
    dist (embed (added 1)) (embed (source 1)) ∉ Set.range ((↑) : ℚ → ℝ) := by
  intro h
  obtain ⟨r,hr⟩ := (rational_distance_iff _ _).mp h
  rw [added_missing_distance_squared] at hr
  have hn : ¬ IsSquare (109 : ℚ) := by
    norm_num [Rat.isSquare_natCast_iff]
  apply hn
  refine ⟨r*7/8,?_⟩
  nlinarith [hr]

def complete : Fin 9 → QPoint :=
  ![(5,0),(-5,0),(9,0),(0,12),(0,2079/520),(0,-12),
    (-6935/2773,16632/2773),(45/7,24/7),(-2773/339,4312/565)]

private def det3 (a b c d e f g h i : ℚ) : ℚ :=
  a*(e*i-f*h)-b*(d*i-f*g)+c*(d*h-e*g)

/-- The four-point determinant vanishes on a line or circle. -/
def circleDet (p q r s : QPoint) : ℚ :=
  det3 (q.1-p.1) (q.2-p.2) (qDistSq p q)
    (r.1-p.1) (r.2-p.2) (qDistSq p r)
    (s.1-p.1) (s.2-p.2) (qDistSq p s)

private def intX : Fin 9 → ℤ :=
  ![17108855400,-17108855400,30795939720,0,0,0,-8557512600,21997099800,-27989885560]
private def intY : Fin 9 → ℤ :=
  ![0,0,0,41061252960,13680503991,-41061252960,20523222720,11731786560,26114472384]

private def iNorm (i j : Fin 9) : ℤ := (intX j-intX i)^2+(intY j-intY i)^2

private def iCircle (i j k l : Fin 9) : ℤ :=
  (intX j-intX i)*((intY k-intY i)*iNorm i l-iNorm i k*(intY l-intY i)) -
  (intY j-intY i)*((intX k-intX i)*iNorm i l-iNorm i k*(intX l-intX i)) +
  iNorm i j*((intX k-intX i)*(intY l-intY i)-(intY k-intY i)*(intX l-intX i))

private lemma complete_coordinates (i : Fin 9) :
    complete i = ((intX i : ℚ)/3421771080,(intY i : ℚ)/3421771080) := by
  fin_cases i <;> norm_num [complete,intX,intY,Matrix.cons_val_succ,Matrix.cons_val_succ']

private lemma complete_det_scale (i j k l : Fin 9) :
    circleDet (complete i) (complete j) (complete k) (complete l) =
      (iCircle i j k l : ℚ)/3421771080^4 := by
  rw [complete_coordinates i,complete_coordinates j,complete_coordinates k,complete_coordinates l]
  unfold circleDet det3 qDistSq iCircle iNorm
  push_cast
  ring

private lemma integer_determinants : ∀ i j k l : Fin 9, i < j → j < k → k < l →
    iCircle i j k l ≠ 0 := by decide

/-- The failed metric control nevertheless has no four-point line/circle
incidence obstruction. This is the arithmetic determinant certificate. -/
lemma complete_determinants : ∀ i j k l : Fin 9, i < j → j < k → k < l →
    circleDet (complete i) (complete j) (complete k) (complete l) ≠ 0 := by
  intro i j k l hij hjk hkl
  rw [complete_det_scale]
  exact div_ne_zero (by exact_mod_cast integer_determinants i j k l hij hjk hkl) (by norm_num)

/-- No nonzero common real dilation repairs the failed distances, either. -/
lemma no_common_scale (c : ℝ) (hc : c ≠ 0) :
    ¬ (∀ i j : Fin 9, c*dist (embed (complete i)) (embed (complete j)) ∈
      Set.range ((↑) : ℚ → ℝ)) := by
  intro h
  have hd : dist (embed (complete 0)) (embed (complete 1)) = 10 := by
    have hh := embed_dist_sq (complete 0) (complete 1)
    norm_num [complete,qDistSq,Matrix.cons_val_succ,Matrix.cons_val_succ'] at hh
    change dist (embed (5,0)) (embed (-5,0)) = 10
    nlinarith [dist_nonneg (x := embed (5,0)) (y := embed (-5,0))]
  obtain ⟨q,hq⟩ := h 0 1
  rw [hd] at hq
  have hq' : (q : ℝ)/10 = c := by linarith
  obtain ⟨r,hr⟩ := h 7 1
  apply added_missing_distance_irrational
  refine ⟨r/(q/10),?_⟩
  push_cast
  rw [hq']
  apply (div_eq_iff hc).mpr
  change (r : ℝ) = dist (embed (complete 7)) (embed (complete 1))*c
  simpa [mul_comm] using hr

#print axioms pappus
#print axioms second_common_leg
#print axioms source_rational_distances
#print axioms added_missing_distance_irrational
#print axioms complete_determinants
#print axioms no_common_scale

end Erdos213.PappusMetric
