import FormalConjecturesUtil

/-! Two explicit symmetric polynomial kernels with zero row and sum-line
integrals but a nonzero antisymmetric largest-coordinate CDF pairing.
This is an auxiliary analytic construction, NOT a disproof of Erdős 371.
No claim about the actual prime-factor law is made in this module. -/
namespace Erdos371.ContinuousKernelObstruction
open scoped Interval
set_option autoImplicit false

noncomputable def h0 (x : ℝ) : ℝ := x^3-3*x^4+3*x^5-x^6
noncomputable def h1 (x : ℝ) : ℝ := 3*x^2-12*x^3+15*x^4-6*x^5
noncomputable def h2 (x : ℝ) : ℝ := 6*x-36*x^2+60*x^3-30*x^4
noncomputable def h3 (x : ℝ) : ℝ := 6-72*x+180*x^2-120*x^3

lemma dh0 (x : ℝ) : HasDerivAt h0 (h1 x) x := by
  convert (((hasDerivAt_pow 3 x).sub ((hasDerivAt_pow 4 x).const_mul 3)).add
    ((hasDerivAt_pow 5 x).const_mul 3)).sub (hasDerivAt_pow 6 x) using 1
  norm_num [h0,h1]
  ring

lemma dh1 (x : ℝ) : HasDerivAt h1 (h2 x) x := by
  convert ((((hasDerivAt_pow 2 x).const_mul 3).sub
    ((hasDerivAt_pow 3 x).const_mul 12)).add
    ((hasDerivAt_pow 4 x).const_mul 15)).sub
    ((hasDerivAt_pow 5 x).const_mul 6) using 1
  norm_num [h1,h2]
  ring

lemma dh2 (x : ℝ) : HasDerivAt h2 (h3 x) x := by
  convert ((((hasDerivAt_id x).const_mul 6).sub
    ((hasDerivAt_pow 2 x).const_mul 36)).add
    ((hasDerivAt_pow 3 x).const_mul 60)).sub
    ((hasDerivAt_pow 4 x).const_mul 30) using 1
  norm_num [h2,h3]
  ring

noncomputable def potential (x y : ℝ) : ℝ :=
  h2 x*h0 y-2*h1 x*h1 y+h0 x*h2 y
noncomputable def potentialX (x y : ℝ) : ℝ :=
  h3 x*h0 y-2*h2 x*h1 y+h1 x*h2 y
noncomputable def potentialY (x y : ℝ) : ℝ :=
  h2 x*h1 y-2*h1 x*h2 y+h0 x*h3 y
noncomputable def kernel1 (x y : ℝ) : ℝ :=
  h3 x*h1 y-2*h2 x*h2 y+h1 x*h3 y
noncomputable def potential2 (x y : ℝ) : ℝ := (x+y)/2*potential x y
noncomputable def potential2X (x y : ℝ) : ℝ :=
  potential x y/2+(x+y)/2*potentialX x y
noncomputable def kernel2 (x y : ℝ) : ℝ :=
  (x+y)/2*kernel1 x y+(potentialX x y+potentialY x y)/2

lemma d_potential_x (x y : ℝ) :
    HasDerivAt (fun z => potential z y) (potentialX x y) x := by
  exact (((dh2 x).mul_const (h0 y)).sub
    (((dh1 x).const_mul 2).mul_const (h1 y))).add
    ((dh0 x).mul_const (h2 y))

lemma d_potential_y (x y : ℝ) :
    HasDerivAt (potential x) (potentialY x y) y := by
  exact (((dh0 y).const_mul (h2 x)).sub
    ((dh1 y).const_mul (2*h1 x))).add
    ((dh2 y).const_mul (h0 x))

lemma d_potentialX_y (x y : ℝ) :
    HasDerivAt (potentialX x) (kernel1 x y) y := by
  exact (((dh0 y).const_mul (h3 x)).sub
    ((dh1 y).const_mul (2*h2 x))).add
    ((dh2 y).const_mul (h1 x))

lemma d_potential2_x (x y : ℝ) :
    HasDerivAt (fun z => potential2 z y) (potential2X x y) x := by
  convert (((hasDerivAt_id x).add_const y).div_const 2).mul
    (d_potential_x x y) using 1
  simp only [potential2X,id_eq]
  ring

lemma d_potential2X_y (x y : ℝ) :
    HasDerivAt (potential2X x) (kernel2 x y) y := by
  convert ((d_potential_y x y).div_const 2).add
    ((((hasDerivAt_id y).const_add x).div_const 2).mul
      (d_potentialX_y x y)) using 1
  simp only [kernel2,id_eq]
  ring

lemma kernel1_symm (x y : ℝ) : kernel1 x y = kernel1 y x := by
  unfold kernel1; ring
lemma kernel2_symm (x y : ℝ) : kernel2 x y = kernel2 y x := by
  unfold kernel2 kernel1 potentialX potentialY; ring

lemma kernel1_row (x : ℝ) : (∫ y in (0 : ℝ)..1, kernel1 x y) = 0 := by
  have hc : Continuous (kernel1 x) := by unfold kernel1 h1 h2 h3; fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y _ => d_potentialX_y x y) (hc.intervalIntegrable 0 1)]
  norm_num [potentialX,h0,h1,h2]

lemma kernel2_row (x : ℝ) : (∫ y in (0 : ℝ)..1, kernel2 x y) = 0 := by
  have hc : Continuous (kernel2 x) := by
    unfold kernel2 kernel1 potentialX potentialY h0 h1 h2 h3; fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y _ => d_potential2X_y x y) (hc.intervalIntegrable 0 1)]
  norm_num [potential2X,potential,potentialX,h0,h1,h2]

lemma kernel1_square (t : ℝ) :
    (∫ x in (0 : ℝ)..t, ∫ y in (0 : ℝ)..t, kernel1 x y) = potential t t := by
  have he (x : ℝ) : (∫ y in (0 : ℝ)..t, kernel1 x y) = potentialX x t := by
    have hc : Continuous (kernel1 x) := by unfold kernel1 h1 h2 h3; fun_prop
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun y _ => d_potentialX_y x y) (hc.intervalIntegrable 0 t)]
    norm_num [potentialX,h0,h1,h2]
  simp_rw [he]
  have hc : Continuous (fun x => potentialX x t) := by
    unfold potentialX h1 h2 h3; fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => d_potential_x x t) (hc.intervalIntegrable 0 t)]
  norm_num [potential,h0,h1,h2]

lemma kernel2_square (t : ℝ) :
    (∫ x in (0 : ℝ)..t, ∫ y in (0 : ℝ)..t, kernel2 x y) = potential2 t t := by
  have he (x : ℝ) : (∫ y in (0 : ℝ)..t, kernel2 x y) = potential2X x t := by
    have hc : Continuous (kernel2 x) := by
      unfold kernel2 kernel1 potentialX potentialY h0 h1 h2 h3; fun_prop
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun y _ => d_potential2X_y x y) (hc.intervalIntegrable 0 t)]
    norm_num [potential2X,potential,potentialX,h0,h1,h2]
  simp_rw [he]
  have hc : Continuous (fun x => potential2X x t) := by
    unfold potential2X potential potentialX h0 h1 h2 h3; fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => d_potential2_x x t) (hc.intervalIntegrable 0 t)]
  norm_num [potential2,potential,h0,h1,h2]

noncomputable def linePrimitive (x y : ℝ) : ℝ := h2 x*h1 y-h1 x*h2 y
noncomputable def linePrimitive2 (s x : ℝ) : ℝ :=
  s/2*linePrimitive x (s-x)+(h2 x*h0 (s-x)-h0 x*h2 (s-x))/2

lemma d_linePrimitive (s x : ℝ) :
    HasDerivAt (fun z => linePrimitive z (s-z)) (kernel1 x (s-x)) x := by
  have hd := (hasDerivAt_id x).const_sub s
  have h1c := (dh1 (s-x)).comp x hd
  have h2c := (dh2 (s-x)).comp x hd
  convert (((dh2 x).mul h1c).sub ((dh1 x).mul h2c)) using 1
  simp only [Function.comp_apply,kernel1]
  ring

lemma d_linePrimitive2 (s x : ℝ) :
    HasDerivAt (linePrimitive2 s) (kernel2 x (s-x)) x := by
  have hd := (hasDerivAt_id x).const_sub s
  have h0c := (dh0 (s-x)).comp x hd
  have h2c := (dh2 (s-x)).comp x hd
  convert ((d_linePrimitive s x).const_mul (s/2)).add
    ((((dh2 x).mul h0c).sub ((dh0 x).mul h2c)).div_const 2) using 1
  simp only [Function.comp_apply,kernel2,potentialX,potentialY,kernel1]
  ring

lemma kernel1_sumline_lower (s : ℝ) :
    (∫ x in (0 : ℝ)..s, kernel1 x (s-x)) = 0 := by
  have hc : Continuous (fun x => kernel1 x (s-x)) := by
    unfold kernel1 h1 h2 h3; fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => d_linePrimitive s x) (hc.intervalIntegrable 0 s)]
  norm_num [linePrimitive,h1,h2]

lemma kernel1_sumline_upper (s : ℝ) :
    (∫ x in (s-1)..(1 : ℝ), kernel1 x (s-x)) = 0 := by
  have hc : Continuous (fun x => kernel1 x (s-x)) := by
    unfold kernel1 h1 h2 h3; fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => d_linePrimitive s x) (hc.intervalIntegrable (s-1) 1)]
  norm_num [linePrimitive,h1,h2]

lemma kernel2_sumline_lower (s : ℝ) :
    (∫ x in (0 : ℝ)..s, kernel2 x (s-x)) = 0 := by
  have hc : Continuous (fun x => kernel2 x (s-x)) := by
    unfold kernel2 kernel1 potentialX potentialY h0 h1 h2 h3; fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => d_linePrimitive2 s x) (hc.intervalIntegrable 0 s)]
  norm_num [linePrimitive2,linePrimitive,h0,h1,h2]

lemma kernel2_sumline_upper (s : ℝ) :
    (∫ x in (s-1)..(1 : ℝ), kernel2 x (s-x)) = 0 := by
  have hc : Continuous (fun x => kernel2 x (s-x)) := by
    unfold kernel2 kernel1 potentialX potentialY h0 h1 h2 h3; fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => d_linePrimitive2 s x) (hc.intervalIntegrable (s-1) 1)]
  norm_num [linePrimitive2,linePrimitive,h0,h1,h2]

noncomputable def cdf1 (t : ℝ) : ℝ := potential t t
noncomputable def cdf2 (t : ℝ) : ℝ := potential2 t t
noncomputable def cdf1Deriv (t : ℝ) : ℝ := potentialX t t+potentialY t t
noncomputable def cdf2Deriv (t : ℝ) : ℝ := cdf1 t+t*cdf1Deriv t

lemma cdf1_formula (t : ℝ) : cdf1 t = -6*t^4*(t-1)^4*(2*t^2-2*t+1) := by
  unfold cdf1 potential h0 h1 h2; ring
lemma cdf2_eq (t : ℝ) : cdf2 t = t*cdf1 t := by
  unfold cdf2 cdf1 potential2; ring
lemma d_cdf1 (t : ℝ) : HasDerivAt cdf1 (cdf1Deriv t) t := by
  convert (((dh2 t).mul (dh0 t)).sub
    (((dh1 t).const_mul 2).mul (dh1 t))).add
    ((dh0 t).mul (dh2 t)) using 1
  simp only [cdf1Deriv,potentialX,potentialY]
  ring
lemma d_cdf2 (t : ℝ) : HasDerivAt cdf2 (cdf2Deriv t) t := by
  simp_rw [show cdf2 = fun t => t*cdf1 t from funext cdf2_eq]
  simpa [cdf2Deriv] using (hasDerivAt_id t).mul (d_cdf1 t)

lemma oriented_cdf_pairing_eq_square (t : ℝ) :
    cdf1 t*cdf2Deriv t-cdf2 t*cdf1Deriv t = (cdf1 t)^2 := by
  rw [cdf2_eq]; unfold cdf2Deriv; ring

theorem oriented_cdf_pairing_positive :
    0 < ∫ t in (0 : ℝ)..1, cdf1 t*cdf2Deriv t-cdf2 t*cdf1Deriv t := by
  simp_rw [oriented_cdf_pairing_eq_square]
  apply intervalIntegral.integral_pos (by norm_num)
  · have hc : Continuous (fun t => (cdf1 t)^2) := by
      unfold cdf1 potential h0 h1 h2; fun_prop
    exact hc.continuousOn
  · intro x _; exact sq_nonneg _
  · refine ⟨1/2,by norm_num,?_⟩
    rw [cdf1_formula]; norm_num

#print axioms kernel1_row
#print axioms kernel2_row
#print axioms kernel1_sumline_lower
#print axioms kernel2_sumline_upper
#print axioms kernel1_square
#print axioms kernel2_square
#print axioms oriented_cdf_pairing_positive
end Erdos371.ContinuousKernelObstruction
