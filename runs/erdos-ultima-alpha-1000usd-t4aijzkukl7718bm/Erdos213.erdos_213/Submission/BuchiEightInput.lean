import FormalConjecturesUtil

/-! Eight symmetric quadratic square values and a projective direction change.
The leading coefficient is not required to be a square. This supplies arithmetic
input, not an eight-point configuration or a settlement of Erdős 213. -/
namespace Erdos213.BuchiEightInput
noncomputable section
set_option maxHeartbeats 1000000

/-- The original quadratic is `A*r^2+C`. -/
def A : ℚ := 570570/4977361
def C : ℚ := 4406791/4977361

def sourceRoot : Fin 8 → ℚ := ![-7,-5,-3,-1,1,3,5,7]
def squareRoot : Fin 8 → ℚ :=
  ![5689/2231,4321/2231,3089/2231,1,1,3089/2231,4321/2231,5689/2231]

lemma eight_squares : ∀ k, A*sourceRoot k^2+C=squareRoot k^2 := by decide +kernel
lemma positive_coefficients : 0<A ∧ 0<C := by norm_num [A,C]
lemma leading_not_square : ¬IsSquare A := by decide +kernel
lemma next_not_square : ¬IsSquare (A*81+C) := by decide +kernel

/-- Send the direction 7 to infinity and the directions -7,-5 to 0,1. -/
def mapRoot (r : ℚ) : ℚ := 6*(r+7)/(7-r)
def mappedReal (a c : ℚ) : ℚ := -6+588*a/(49*a+c)
def mappedHeight (a c : ℚ) : ℚ := a*c*(-84/(49*a+c))^2

lemma projective_identity (a c r : ℚ) (ha : 49*a+c≠0) (hr : 7-r≠0) :
    (mappedReal a c-mapRoot r)^2+mappedHeight a c =
      84^2*(a*r^2+c)/((7-r)^2*(49*a+c)) := by
  dsimp [mappedReal,mapRoot,mappedHeight]
  generalize hn : 49*a+c=n at *
  field_simp [ha,hr]
  rw [← hn]
  ring

lemma mapped_square (a c r q q7 : ℚ) (ha : 49*a+c≠0) (hr : 7-r≠0)
    (hq : a*r^2+c=q^2) (h7 : 49*a+c=q7^2) :
    IsSquare ((mappedReal a c-mapRoot r)^2+mappedHeight a c) := by
  rw [projective_identity a c r ha hr,hq,h7]
  convert IsSquare.sq (84*q/((7-r)*q7)) using 1
  simp only [div_pow,mul_pow]

lemma mapped_height_pos {a c : ℚ} (ha : 0<a) (hc : 0<c) :
    0 < mappedHeight a c := by
  dsimp [mappedHeight]
  apply mul_pos (mul_pos ha hc)
  apply sq_pos_of_ne_zero
  exact div_ne_zero (by norm_num) (by positivity)

def direction : Fin 7 → ℚ := ![0,1,12/5,9/2,8,15,36]
def directionLength : Fin 7 → ℚ :=
  ![6,30247/5689,129738/28445,46851/11378,31234/5689,64869/5689,181482/5689]
def x : ℚ := 141306834/32364721
def y : ℚ := -84/32364721
def D : ℕ := 2514382740870

lemma actual_reparametrization :
    x=mappedReal A C ∧ (D : ℚ)*y^2=mappedHeight A C := by
  norm_num [x,y,D,mappedReal,mappedHeight,A,C]

lemma norm_identities : ∀ k,
    (x-direction k)^2+(D : ℚ)*y^2=directionLength k^2 := by decide +kernel
lemma direction_injective : Function.Injective direction := by decide +kernel
lemma D_positive : 0<D := by decide +kernel

noncomputable def parameter : ℂ := ⟨(x : ℝ),(y : ℝ)*Real.sqrt D⟩

lemma parameter_nonreal : parameter.im≠0 := by
  apply mul_ne_zero
  · norm_num [y]
  · exact Real.sqrt_ne_zero'.mpr (by norm_num [D])

lemma rational_direction_norms (k : Fin 7) :
    ‖parameter-(direction k : ℂ)‖∈Set.range ((↑) : ℚ → ℝ) := by
  refine ⟨|directionLength k|,?_⟩
  rw [Rat.cast_abs]
  apply (sq_eq_sq₀ (abs_nonneg _) (norm_nonneg _)).mp
  rw [sq_abs,Complex.sq_norm,Complex.normSq_apply]
  have hd := Real.sq_sqrt (show 0≤(D : ℝ) by positivity)
  have he := congrArg ((↑) : ℚ → ℝ) (norm_identities k)
  push_cast at he
  simp only [parameter,Complex.sub_re,Complex.sub_im,Complex.ratCast_re,
    Complex.ratCast_im,sub_zero]
  nlinarith only [he,hd]

#print axioms eight_squares
#print axioms leading_not_square
#print axioms next_not_square
#print axioms projective_identity
#print axioms mapped_square
#print axioms rational_direction_norms
end
end Erdos213.BuchiEightInput
