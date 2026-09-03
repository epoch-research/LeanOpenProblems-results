import FormalConjecturesUtil

/-! A small-mass obstruction to exact scalar-diagonal splitting for a
rectangle block. These finite kernels are NOT arithmetic covering systems. -/
namespace Erdos7TrimmedBlockDiagonalObstruction
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable def rowKernel (x : Fin 5) (y : Fin 7) : ℝ :=
  if x.val=0 ∧ (y.val=0 ∨ y.val=1) then 1/35 else 0
noncomputable def colKernel (x : Fin 5) (y : Fin 7) : ℝ :=
  if (x.val=0 ∨ x.val=1) ∧ y.val=0 then 1/35 else 0

noncomputable def value (z a b d : ℝ) (x : Fin 5) (y : Fin 7) : ℝ :=
  z + (if x.val=0 then a else 0) + (if y.val=0 then b else 0) +
    (if x.val=0 ∧ y.val=0 then d else 0)

def Feasible (ν : Fin 5 → Fin 7 → ℝ) : Prop :=
  (∀ x y, 0 ≤ ν x y ∧ ν x y ≤ 1/35) ∧
  (∀ x, (∑ y,ν x y) ≤ 1/5) ∧
  (∀ y, (∑ x,ν x y) ≤ 1/7) ∧
  (∑ x, ∑ y, ν x y)=2/35

lemma row_feasible : Feasible rowKernel := by
  refine ⟨?_,?_,?_,?_⟩
  · intro x y; unfold rowKernel; split_ifs <;> norm_num
  · intro x; fin_cases x <;> norm_num [rowKernel,Fin.sum_univ_succ]
  · intro y; fin_cases y <;> norm_num [rowKernel,Fin.sum_univ_succ]
  · norm_num [rowKernel,Fin.sum_univ_succ]

lemma col_feasible : Feasible colKernel := by
  refine ⟨?_,?_,?_,?_⟩
  · intro x y; unfold colKernel; split_ifs <;> norm_num
  · intro x; fin_cases x <;> norm_num [colKernel,Fin.sum_univ_succ]
  · intro y; fin_cases y <;> norm_num [colKernel,Fin.sum_univ_succ]
  · norm_num [colKernel,Fin.sum_univ_succ]

lemma row_value (z a b d : ℝ) :
    (∑ x, ∑ y, rowKernel x y * value z a b d x y) =
      (2*z+2*a+b+d)/35 := by
  norm_num [rowKernel,value,Fin.sum_univ_succ]
  ring
lemma col_value (z a b d : ℝ) :
    (∑ x, ∑ y, colKernel x y * value z a b d x y) =
      (2*z+a+2*b+d)/35 := by
  norm_num [colKernel,value,Fin.sum_univ_succ]
  ring

/-- Both kernels give the same linear test value when all four independently
labelled old weights equal t. This is the trimmed scalar diagonal. -/
lemma diagonal (t : ℝ) :
    (∑ x, ∑ y, rowKernel x y * value t t t t x y) = 6*t/35 ∧
    (∑ x, ∑ y, colKernel x y * value t t t t x y) = 6*t/35 := by
  rw [row_value,col_value]
  constructor <;> ring

/-- Any convex separable majorant for BOTH actual kernels pays a positive
extra cost somewhere on the scalar diagonal, already on [1,2]. The row and
column family arguments are not identified with each other. -/
theorem diagonal_error (f₀ f₁ f₂ f₃ : ℝ → ℝ) (ε : ℝ)
    (h₀ : ConvexOn ℝ Set.univ f₀) (h₃ : ConvexOn ℝ Set.univ f₃)
    (hrow : ∀ z ∈ Set.Icc (1:ℝ) 2, ∀ a ∈ Set.Icc (1:ℝ) 2,
      ∀ b ∈ Set.Icc (1:ℝ) 2, ∀ d ∈ Set.Icc (1:ℝ) 2,
      (∑ x, ∑ y, rowKernel x y * value z a b d x y) ≤
        f₀ z+f₁ a+f₂ b+f₃ d)
    (hcol : ∀ z ∈ Set.Icc (1:ℝ) 2, ∀ a ∈ Set.Icc (1:ℝ) 2,
      ∀ b ∈ Set.Icc (1:ℝ) 2, ∀ d ∈ Set.Icc (1:ℝ) 2,
      (∑ x, ∑ y, colKernel x y * value z a b d x y) ≤
        f₀ z+f₁ a+f₂ b+f₃ d)
    (hdiag : ∀ t ∈ Set.Icc (1:ℝ) 2,
      f₀ t+f₁ t+f₂ t+f₃ t ≤ 6*t/35+ε) :
    (1:ℝ)/70 ≤ ε := by
  have h1 : (1:ℝ) ∈ Set.Icc (1:ℝ) 2 := by constructor <;> norm_num
  have h2 : (2:ℝ) ∈ Set.Icc (1:ℝ) 2 := by constructor <;> norm_num
  have hm : (3/2:ℝ) ∈ Set.Icc (1:ℝ) 2 := by constructor <;> norm_num
  have hr := hrow (3/2) hm 2 h2 1 h1 (3/2) hm
  have hc := hcol (3/2) hm 1 h1 2 h2 (3/2) hm
  rw [row_value] at hr
  rw [col_value] at hc
  have hc0 := h₀.2 (Set.mem_univ (1:ℝ)) (Set.mem_univ (2:ℝ))
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num : (1/2:ℝ)+1/2=1)
  have hc3 := h₃.2 (Set.mem_univ (1:ℝ)) (Set.mem_univ (2:ℝ))
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num : (1/2:ℝ)+1/2=1)
  norm_num [smul_eq_mul] at hc0 hc3 hr hc
  have hd1 := hdiag 1 h1
  have hd2 := hdiag 2 h2
  linarith

#print axioms row_feasible
#print axioms col_feasible
#print axioms diagonal_error
end Erdos7TrimmedBlockDiagonalObstruction
