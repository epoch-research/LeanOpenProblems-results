import Submission.AffineQuarticSphereRigidity

/-! Quadratic sphere-map rigidity when two coordinate axes have equal images. -/
namespace Erdos322Research.QuadraticSphereEqualAxes
noncomputable section
open Finset Matrix
open scoped Classical
set_option Elab.async false
set_option maxHeartbeats 0

def quad (q : Fin 6 → ℝ) (x : Fin 3 → ℝ) : ℝ :=
  q 0*x 0^2+q 1*x 1^2+q 2*x 2^2+q 3*x 0*x 1+q 4*x 0*x 2+q 5*x 1*x 2

private theorem mixed_zero (q : Fin 4 → Fin 6 → ℝ) (C : ℝ)
    (h : ∀ x : Fin 3 → ℝ, ∑ i, quad (q i) x^4=C*(x ⬝ᵥ x)^4)
    (heq : ∀ i, q i 0=q i 1) (i : Fin 4) : q i 3=0 := by
  have hp := h ![1,1,0]
  have hm := h ![1,-1,0]
  have h0 := h ![1,0,0]
  simp only [quad,dotProduct,Fin.sum_univ_three] at hp hm h0
  dsimp at hp hm h0
  simp only [← heq] at hp hm h0
  have he : ∑ i, (48*(q i 0*q i 3)^2+2*(q i 3)^4)=0 := by
    simp only [Fin.sum_univ_four] at hp hm h0 ⊢
    linear_combination hp+hm-32*h0
  have hh : 48*(q i 0*q i 3)^2+2*(q i 3)^4=0 :=
    (sum_eq_zero_iff_of_nonneg (fun _ _ ↦ by positivity)).mp he i (mem_univ i)
  have hpow : (q i 3)^4=0 := by nlinarith [sq_nonneg (q i 0*q i 3),sq_nonneg ((q i 3)^2)]
  exact eq_zero_of_pow_eq_zero hpow

private def sphereMap (x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![2*x 0*x 2,2*x 1*x 2,x 2^2-x 0^2-x 1^2]

private theorem sphereMap_surjective (y : Fin 3 → ℝ) (hy : y ⬝ᵥ y=1) :
    ∃ x : Fin 3 → ℝ, x ⬝ᵥ x=1 ∧ sphereMap x=y := by
  have hy' : y 0^2+y 1^2+y 2^2=1 := by
    simpa only [dotProduct,Fin.sum_univ_three,pow_two] using hy
  have hylow : -1≤y 2 := by nlinarith [sq_nonneg (y 0),sq_nonneg (y 1),sq_nonneg (y 2+1)]
  by_cases he : y 2 = -1
  · have hy0 : y 0=0 := by nlinarith [sq_nonneg (y 1)]
    have hy1 : y 1=0 := by nlinarith [sq_nonneg (y 0)]
    refine ⟨![1,0,0],by norm_num [dotProduct,Fin.sum_univ_three]; rfl,?_⟩
    funext j
    fin_cases j <;> dsimp [sphereMap] <;> simp [hy0,hy1,he]
  have hypos : 0<(1+y 2)/2 := by
    have hylow' := lt_of_le_of_ne hylow (Ne.symm he)
    linarith
  let t := Real.sqrt ((1+y 2)/2)
  have ht : t≠0 := (Real.sqrt_pos.mpr hypos).ne'
  have ht2 : t^2=(1+y 2)/2 := Real.sq_sqrt hypos.le
  have htt : 2*t≠0 := mul_ne_zero (by norm_num) ht
  let x : Fin 3 → ℝ := ![y 0/(2*t),y 1/(2*t),t]
  have hxy : (y 0/(2*t))^2+(y 1/(2*t))^2=(1-y 2)/2 := by
    apply (eq_div_iff (by norm_num : (2:ℝ)≠0)).mpr
    field_simp
    nlinarith only [hy',ht2]
  refine ⟨x,?_,?_⟩
  · simp only [dotProduct,Fin.sum_univ_three]
    dsimp [x]
    nlinarith only [hxy,ht2]
  · funext j
    fin_cases j
    · dsimp [sphereMap,x]
      field_simp
    · dsimp [sphereMap,x]
      field_simp
    · dsimp [sphereMap,x]
      nlinarith only [hxy,ht2]

/-- A homogeneous quadratic map with constant fourth-power norm on each real
sphere is radial if two orthogonal coordinate directions have the same image. -/
theorem radial_of_equal_axes (q : Fin 4 → Fin 6 → ℝ) (C : ℝ)
    (h : ∀ x : Fin 3 → ℝ, ∑ i, quad (q i) x^4=C*(x ⬝ᵥ x)^4)
    (heq : ∀ i, q i 0=q i 1) :
    ∀ i x, quad (q i) x=q i 0*(x ⬝ᵥ x) := by
  have hz := mixed_zero q C h heq
  let a : Fin 4 → ℝ := fun i ↦ (q i 0+q i 2)/2
  let v : Fin 4 → Fin 3 → ℝ := fun i ↦ ![q i 4/2,q i 5/2,(q i 2-q i 0)/2]
  have hv : v=0 := by
    apply AffineQuarticSphereRigidity.linear_part_zero a v C
    intro y hy
    obtain ⟨x,hx,rfl⟩ := sphereMap_surjective y hy
    have hh := h x
    rw [hx,one_pow,mul_one] at hh
    convert hh using 1
    apply sum_congr rfl
    intro i _
    congr 1
    have hx' : x 0^2+x 1^2+x 2^2=1 := by
      simpa only [dotProduct,Fin.sum_univ_three,pow_two] using hx
    simp only [quad,← heq,hz,dotProduct,Fin.sum_univ_three]
    dsimp [a,v,sphereMap]
    linear_combination -(q i 0+q i 2)/2*hx'
  intro i x
  have h4 : q i 4=0 := by
    have hh := congrFun (congrFun hv i) 0
    dsimp [v] at hh
    linarith
  have h5 : q i 5=0 := by
    have hh := congrFun (congrFun hv i) 1
    dsimp [v] at hh
    linarith
  have h2 : q i 2=q i 0 := by
    have hh := congrFun (congrFun hv i) 2
    dsimp [v] at hh
    linarith
  simp only [quad,← heq,hz,h4,h5,h2,dotProduct,Fin.sum_univ_three]
  ring

/-- The equal-axis hypothesis may concern any of the three pairs. -/
theorem radial_of_some_equal_axes (q : Fin 4 → Fin 6 → ℝ) (C : ℝ)
    (h : ∀ x : Fin 3 → ℝ, ∑ i, quad (q i) x^4=C*(x ⬝ᵥ x)^4)
    (heq : (∀ i, q i 0=q i 1) ∨ (∀ i, q i 0=q i 2) ∨ (∀ i, q i 1=q i 2)) :
    ∃ r : Fin 4 → ℝ, ∀ i x, quad (q i) x=r i*(x ⬝ᵥ x) := by
  rcases heq with heq|heq|heq
  · exact ⟨fun i ↦ q i 0,radial_of_equal_axes q C h heq⟩
  · let q' : Fin 4 → Fin 6 → ℝ := fun i ↦ ![q i 0,q i 2,q i 1,q i 4,q i 3,q i 5]
    have h' : ∀ x : Fin 3 → ℝ, ∑ i, quad (q' i) x^4=C*(x ⬝ᵥ x)^4 := by
      intro x
      have hh := h ![x 0,x 2,x 1]
      simp only [quad,dotProduct,Fin.sum_univ_three] at hh ⊢
      dsimp [q'] at hh ⊢
      convert hh using 1
      · apply sum_congr rfl
        intro i _
        congr 1
        ring
      · ring
    have heq' (i) : q' i 0=q' i 1 := heq i
    have hrad := radial_of_equal_axes q' C h' heq'
    refine ⟨fun i ↦ q i 0,?_⟩
    intro i x
    have hh := hrad i ![x 0,x 2,x 1]
    simp only [quad,dotProduct,Fin.sum_univ_three] at hh ⊢
    dsimp [q'] at hh
    convert hh using 1 <;> ring
  · let q' : Fin 4 → Fin 6 → ℝ := fun i ↦ ![q i 1,q i 2,q i 0,q i 5,q i 3,q i 4]
    have h' : ∀ x : Fin 3 → ℝ, ∑ i, quad (q' i) x^4=C*(x ⬝ᵥ x)^4 := by
      intro x
      have hh := h ![x 2,x 0,x 1]
      simp only [quad,dotProduct,Fin.sum_univ_three] at hh ⊢
      dsimp [q'] at hh ⊢
      convert hh using 1
      · apply sum_congr rfl
        intro i _
        congr 1
        ring
      · ring
    have heq' (i) : q' i 0=q' i 1 := heq i
    have hrad := radial_of_equal_axes q' C h' heq'
    refine ⟨fun i ↦ q i 1,?_⟩
    intro i x
    have hh := hrad i ![x 1,x 2,x 0]
    simp only [quad,dotProduct,Fin.sum_univ_three] at hh ⊢
    dsimp [q'] at hh
    convert hh using 1 <;> ring

end
end Erdos322Research.QuadraticSphereEqualAxes
