import Submission.HesseEisenstein

/-! A metric bridge for three opposite pairs of three-torsion y-coordinates.
After the cubic base change that supplies two-torsion, these six distinct
points cannot all have rational distances after a common real dilation.
This restricted theorem does not settle Erdos 213. -/
namespace Erdos213.HesseSixDistances
open RationalEisenstein HesseEisenstein
open scoped QuadraticAlgebra
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

def points (t : G) : Fin 6 → G :=
  ![4*t^3-4,-4*t^3+4,
    (-2*rr+6)*t^2+(-2*rr-6)*t+4*rr,
    (2*rr-6)*t^2+(2*rr+6)*t-4*rr,
    (2*rr+6)*t^2+(2*rr-6)*t-4*rr,
    (-2*rr-6)*t^2+(-2*rr+6)*t+4*rr]

def edge (t : G) (i j : Fin 6) : ℚ := norm (points t i-points t j)

def Common (t : G) : Prop := ∀ i j k l : Fin 6, i≠j → k≠l →
  IsSquare (edge t i j*edge t k l)

lemma edge_ne {t : G} (hp : Function.Injective (points t)) {i j : Fin 6} (hij : i≠j) :
    edge t i j≠0 := norm_ne_zero (sub_ne_zero.mpr (hp.ne hij))

lemma rr_cube : rr^3=-3*rr := by rw [pow_succ,rr_sq]

lemma relation₁ (t : G) : 12*(points t 0-points t 1)=
    (3-rr)*(2*t+1-rr)*(points t 4-points t 5) := by
  dsimp [points]
  ring_nf
  simp only [rr_sq,rr_cube]
  ring
lemma relation₂ (t : G) : 12*(points t 0-points t 1)=
    (3+rr)*(2*t+1+rr)*(points t 2-points t 3) := by
  dsimp [points]
  ring_nf
  simp only [rr_sq,rr_cube]
  ring
lemma relation₃ (t : G) : 12*(points t 0-points t 2)=
    (3+rr)*(t-1+rr)*(points t 2-points t 3) := by
  dsimp [points]
  ring_nf
  simp only [rr_sq,rr_cube]
  ring
lemma relation₄ (t : G) : 12*(points t 0-points t 3)=
    (3+rr)*(t+2)*(points t 2-points t 3) := by
  dsimp [points]
  ring_nf
  simp only [rr_sq,rr_cube]
  ring
lemma relation₅ (t : G) : 12*(points t 0-points t 4)=
    (3-rr)*(t-1-rr)*(points t 4-points t 5) := by
  dsimp [points]
  ring_nf
  simp only [rr_sq,rr_cube]
  ring
lemma relation₀ (t : G) : 6*t*(points t 0-points t 1)*(points t 0-points t 5)=
    (2*t+1+rr)^2*(points t 0-points t 3)*(points t 2-points t 5) := by
  dsimp [points]
  ring_nf
  simp only [rr_sq,rr_cube]
  ring

lemma constant_norms : norm (3+rr)=12 ∧ norm (3-rr)=12 ∧ norm (12 : G)=144 ∧
    norm (6 : G)=36 := by norm_num [norm_components,rr]

lemma norm_relation {a x y : G}
    (h : 12*x=(3+rr)*a*y ∨ 12*x=(3-rr)*a*y) :
    12*norm x=norm a*norm y := by
  rcases h with h | h
  · have he := congrArg norm h
    simp only [map_mul,constant_norms.1,constant_norms.2.2.1] at he
    linarith only [he]
  · have he := congrArg norm h
    simp only [map_mul,constant_norms.2.1,constant_norms.2.2.1] at he
    linarith only [he]

lemma square_atom {a x y : ℚ} (hy : y≠0) (h : 12*x=a*y)
    (hs : IsSquare (x*y)) : IsSquare (3*a) := by
  convert (IsSquare.sq (6/y)).mul hs using 1
  field_simp
  nlinarith only [h]

lemma first_five {t : G} (hp : Function.Injective (points t)) (h : Common t) :
    IsSquare (3*norm (2*t+1-rr)) ∧ IsSquare (3*norm (2*t+1+rr)) ∧
    IsSquare (3*norm (t-1+rr)) ∧ IsSquare (3*norm (t+2)) ∧
    IsSquare (3*norm (t-1-rr)) := by
  have h45 := edge_ne hp (show (4 : Fin 6)≠5 by decide)
  have h23 := edge_ne hp (show (2 : Fin 6)≠3 by decide)
  exact ⟨square_atom h45 (norm_relation (Or.inr (relation₁ t))) (h 0 1 4 5 (by decide) (by decide)),
    square_atom h23 (norm_relation (Or.inl (relation₂ t))) (h 0 1 2 3 (by decide) (by decide)),
    square_atom h23 (norm_relation (Or.inl (relation₃ t))) (h 0 2 2 3 (by decide) (by decide)),
    square_atom h23 (norm_relation (Or.inl (relation₄ t))) (h 0 3 2 3 (by decide) (by decide)),
    square_atom h45 (norm_relation (Or.inr (relation₅ t))) (h 0 4 4 5 (by decide) (by decide))⟩

lemma center_square {t : G} (hp : Function.Injective (points t)) (h : Common t) :
    IsSquare (norm t) := by
  have he := congrArg norm (relation₀ t)
  simp only [map_mul,map_pow,constant_norms.2.2.2] at he
  change 36*norm t*edge t 0 1*edge t 0 5 =
    norm (2*t+1+rr)^2*edge t 0 3*edge t 2 5 at he
  have h01 := edge_ne hp (show (0 : Fin 6)≠1 by decide)
  have h05 := edge_ne hp (show (0 : Fin 6)≠5 by decide)
  have hs := ((IsSquare.sq (norm (2*t+1+rr)/6)).mul
    (h 0 3 2 5 (by decide) (by decide))).div (h 0 1 0 5 (by decide) (by decide))
  convert hs using 1
  field_simp
  linear_combination he

lemma profile_of_common {t : G} (hp : Function.Injective (points t)) (h : Common t) :
    ∀ i : Fin 6, IsSquare (sixProfile t i) := by
  obtain ⟨h1,h2,h3,h4,h5⟩ := first_five hp h
  intro i
  fin_cases i
  · exact center_square hp h
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5

theorem no_common_hesse (s : G) (hs : s≠0)
    (hp : Function.Injective (points (parameter s))) : ¬Common (parameter s) := by
  intro h
  have hh := profile_of_common hp h
  exact no_six_profile s hs (fun i j => (hh i).mul (hh j))

/-- A common real length scale need not have a rational square. Pair products
of the original rational squared distances are nevertheless rational squares. -/
lemma common_of_scaled_distances {t : G} (hp : Function.Injective (points t))
    (A : ℝ) (hA : 0<A)
    (hd : ∀ i j : Fin 6, i≠j →
      A*dist (toComplex (points t i)) (toComplex (points t j))∈Set.range ((↑) : ℚ → ℝ)) :
    Common t := by
  intro i j k l hij hkl
  obtain ⟨u,hu⟩ := hd i j hij
  obtain ⟨v,hv⟩ := hd k l hkl
  have hdkl : 0<dist (toComplex (points t k)) (toComplex (points t l)) :=
    dist_pos.mpr (toComplex_injective.ne (hp.ne hkl))
  have hv0R : (v : ℝ)≠0 := by rw [hv]; exact mul_ne_zero (ne_of_gt hA) (ne_of_gt hdkl)
  have hv0 : v≠0 := by exact_mod_cast hv0R
  have hsqij := RationalEisenstein.dist_sq (points t i) (points t j)
  have hsqkl := RationalEisenstein.dist_sq (points t k) (points t l)
  change _=(edge t i j : ℝ) at hsqij
  change _=(edge t k l : ℝ) at hsqkl
  refine ⟨u*edge t k l/v,?_⟩
  apply Rat.cast_injective (α := ℝ)
  push_cast
  rw [← pow_two,div_pow,mul_pow,hu,hv,mul_pow,mul_pow,hsqij,hsqkl]
  have hnkl : (edge t k l : ℝ)≠0 := by exact_mod_cast edge_ne hp hkl
  field_simp

/-- This six-point submodel cannot give rational distances under any common
positive real dilation after the full-three-by-six torsion base change. -/
theorem no_scaled_distances (s : G) (hs : s≠0)
    (hp : Function.Injective (points (parameter s))) (A : ℝ) (hA : 0<A) :
    ¬(∀ i j : Fin 6, i≠j → A*dist (toComplex (points (parameter s) i))
      (toComplex (points (parameter s) j))∈Set.range ((↑) : ℚ → ℝ)) := by
  intro h
  exact no_common_hesse s hs hp (common_of_scaled_distances hp A hA h)

#print axioms profile_of_common
#print axioms no_common_hesse
#print axioms no_scaled_distances
end Erdos213.HesseSixDistances
