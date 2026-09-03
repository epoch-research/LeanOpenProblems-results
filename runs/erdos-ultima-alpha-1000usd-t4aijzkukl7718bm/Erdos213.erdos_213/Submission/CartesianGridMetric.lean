import Submission.OrthogonalGlobal
import Submission.UnitCubeNormalForm

/-! Cartesian products require squares for pairs of coordinate differences,
not just for the coordinates themselves. These are restricted grid results;
no arbitrary-cardinality construction or bound on general configurations is
asserted. -/
namespace Erdos213.CartesianGridMetric
noncomputable section
set_option maxHeartbeats 3000000

/-- Exact square condition for a Cartesian product of rational coordinates. -/
def Grid (A B : Set ℚ) : Prop :=
  ∀ a ∈ A, ∀ a' ∈ A, ∀ b ∈ B, ∀ b' ∈ B,
    IsSquare ((a-a')^2+(b-b')^2)

def point (a b : ℚ) : ℂ := (a : ℂ)+(b : ℂ)*Complex.I

lemma distance_rational_iff (a b a' b' : ℚ) :
    dist (point a b) (point a' b') ∈ Set.range (Rat.cast : ℚ → ℝ) ↔
      IsSquare ((a-a')^2+(b-b')^2) := by
  rw [Complex.dist_eq]
  have he : point a b-point a' b'=
      ((a-a' : ℚ) : ℂ)+((b-b' : ℚ) : ℂ)*Complex.I := by
    simp only [point,Rat.cast_sub]
    ring
  rw [he,UnitCubeNormalForm.norm_rational_iff]

lemma grid_iff_rational_distances (A B : Set ℚ) :
    Grid A B ↔ ∀ a ∈ A, ∀ a' ∈ A, ∀ b ∈ B, ∀ b' ∈ B,
      dist (point a b) (point a' b') ∈ Set.range (Rat.cast : ℚ → ℝ) := by
  simp only [Grid,distance_rational_iff]

lemma Grid.swap {A B : Set ℚ} (h : Grid A B) : Grid B A := by
  intro b hb b' hb' a ha a' ha'
  simpa only [add_comm] using h a ha a' ha' b hb b' hb'

/-- Three equally spaced horizontal coordinates cannot occur if the other
coordinate set has two distinct elements. No finiteness or size cutoff is
used. -/
theorem no_three_term_progression {A B : Set ℚ} (h : Grid A B)
    {a u b c : ℚ} (hu : u≠0) (hbc : b≠c)
    (h0 : a∈A) (h1 : a+u∈A) (h2 : a+2*u∈A)
    (hb : b∈B) (hc : c∈B) : False := by
  have hs1 : IsSquare (u^2+(b-c)^2) := by
    convert h (a+u) h1 a h0 b hb c hc using 1; ring
  have hs2 : IsSquare (4*u^2+(b-c)^2) := by
    convert h (a+2*u) h2 a h0 b hb c hc using 1; ring
  apply OrthogonalGlobal.no_simultaneous_squares (div_ne_zero (sub_ne_zero.mpr hbc) hu)
  constructor
  · convert hs1.div (IsSquare.sq u) using 1
    field_simp
    ring
  · convert hs2.div (IsSquare.sq u) using 1
    field_simp
    ring

/-- The same restriction applies in the other coordinate direction. -/
theorem no_vertical_three_term_progression {A B : Set ℚ} (h : Grid A B)
    {b u a c : ℚ} (hu : u≠0) (hac : a≠c)
    (h0 : b∈B) (h1 : b+u∈B) (h2 : b+2*u∈B)
    (ha : a∈A) (hc : c∈A) : False :=
  no_three_term_progression h.swap hu hac h0 h1 h2 ha hc

/-- The previously examined Pythagorean biclique, with all nine cross-leg
hypotenuses. It is not a Cartesian rational-distance grid. -/
def bicliqueA : Fin 3 → ℚ := ![952,1800,3536]
def bicliqueB : Fin 3 → ℚ := ![960,1785,6630]
def bicliqueHyp : Fin 3 → Fin 3 → ℚ :=
  !![1352,2023,6698; 2040,2535,6870; 3664,3961,7514]

lemma biclique_edges (i j : Fin 3) :
    (bicliqueA i)^2+(bicliqueB j)^2=(bicliqueHyp i j)^2 := by
  fin_cases i <;> fin_cases j <;> norm_num [bicliqueA,bicliqueB,bicliqueHyp]

lemma biclique_all_cross_squares (i j : Fin 3) :
    IsSquare ((bicliqueA i)^2+(bicliqueB j)^2) := by
  rw [biclique_edges]
  exact IsSquare.sq _

lemma biclique_difference_not_square :
    ¬ IsSquare ((bicliqueA 0-bicliqueA 1)^2+(bicliqueB 0-bicliqueB 1)^2) := by
  norm_num [bicliqueA,bicliqueB,Rat.isSquare_iff]

lemma biclique_not_grid : ¬ Grid (Set.range bicliqueA) (Set.range bicliqueB) := by
  intro h
  exact biclique_difference_not_square
    (h _ ⟨0,rfl⟩ _ ⟨1,rfl⟩ _ ⟨0,rfl⟩ _ ⟨1,rfl⟩)

/-- A positive three-by-two grid control. Its first coordinates are NOT in
arithmetic progression. This does not meet the conjecture's circle condition. -/
def controlA : Fin 3 → ℚ := ![0,3/4,49200/24871]
def controlB : Fin 2 → ℚ := ![0,1]
def controlHyp : Fin 3 → Fin 3 → ℚ :=
  !![1,5/4,55129/24871; 5/4,1,157565/99484; 55129/24871,157565/99484,1]

lemma control_cross_identity (i j : Fin 3) :
    (controlA i-controlA j)^2+1=(controlHyp i j)^2 := by
  fin_cases i <;> fin_cases j <;> norm_num [controlA,controlHyp]

lemma control_grid : Grid (Set.range controlA) (Set.range controlB) := by
  rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩ _ ⟨k,rfl⟩ _ ⟨l,rfl⟩
  by_cases he : k=l
  · subst l
    simpa only [sub_self,zero_pow (by decide : (2 : ℕ)≠0),add_zero]
      using IsSquare.sq (controlA i-controlA j)
  · have hd : (controlB k-controlB l)^2=1 := by
      fin_cases k <;> fin_cases l <;> simp_all [controlB]
    rw [hd,control_cross_identity]
    exact IsSquare.sq _

lemma control_distinct : Function.Injective controlA ∧ Function.Injective controlB := by
  constructor
  · intro i j h
    fin_cases i <;> fin_cases j <;> norm_num [controlA] at h <;> rfl
  · intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [controlB]

lemma distance_sq (a b a' b' : ℚ) :
    dist (point a b) (point a' b')^2=(((a-a')^2+(b-b')^2 : ℚ) : ℝ) := by
  rw [Complex.dist_eq,Complex.sq_norm,Complex.normSq_apply]
  simp only [point,Complex.sub_re,Complex.sub_im,Complex.add_re,Complex.add_im,
    Complex.mul_re,Complex.mul_im,Complex.ratCast_re,Complex.ratCast_im,
    Complex.I_re,Complex.I_im]
  push_cast
  ring

/-- Every two-by-two subgrid is cospherical, independently of the arithmetic.
The full product itself is therefore not a GP witness. A growth argument
would need both unbounded grids and an extraction theorem. -/
lemma rectangle_cospherical (a a' b b' : ℚ) :
    EuclideanGeometry.Cospherical
      ({point a b,point a b',point a' b,point a' b'} : Set ℂ) := by
  let o := point ((a+a')/2) ((b+b')/2)
  refine ⟨o,dist (point a b) o,?_⟩
  intro p hp
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl | rfl
  all_goals apply (sq_eq_sq₀ dist_nonneg dist_nonneg).mp
  all_goals dsimp only [o]
  all_goals simp only [distance_sq]
  all_goals push_cast
  all_goals ring

#print axioms grid_iff_rational_distances
#print axioms no_three_term_progression
#print axioms no_vertical_three_term_progression
#print axioms biclique_not_grid
#print axioms control_grid
#print axioms control_distinct
#print axioms rectangle_cospherical
end
end Erdos213.CartesianGridMetric
