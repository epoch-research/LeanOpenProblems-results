import FormalConjecturesUtil

/-! A mixed-parity scope witness for joint quadratic fiber rigidity.
The displayed quartic outputs have an additive triple and are not a new
positive-power peak construction. -/
namespace Erdos322Research.JointQuadraticMixedParityExample
noncomputable section
set_option Elab.async false

abbrev Vec := Fin 5 → ℝ

def binaryPart (x : Vec) : ℝ := 3 * x 0 ^ 2 + x 1 ^ 2

def ternaryPart (x : Vec) : ℝ := x 2 ^ 2 + x 3 ^ 2 + x 4 ^ 2

def q₁ (x : Vec) : ℝ := binaryPart x + ternaryPart x

def q₂ (x : Vec) : ℝ := binaryPart x + 2 * ternaryPart x

def outputs (x : Vec) : Fin 4 → ℝ :=
  ![x 0 + x 1, x 0 - x 1, 2 * x 0, ternaryPart x]

/-- The two labels are positive definite diagonal quadratic forms. -/
theorem q₁_pos (x : Vec) (hx : x ≠ 0) : 0 < q₁ x := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
  have hs : 0 < ∑ j : Fin 5, x j ^ 2 :=
    Finset.sum_pos' (fun j _ ↦ sq_nonneg (x j))
      ⟨i, Finset.mem_univ _, sq_pos_of_ne_zero hi⟩
  norm_num [Fin.sum_univ_succ] at hs
  change 0 < x 0 ^ 2 + (x 1 ^ 2 + (x 2 ^ 2 + (x 3 ^ 2 + x 4 ^ 2))) at hs
  dsimp [q₁, binaryPart, ternaryPart]
  nlinarith [sq_nonneg (x 0)]

theorem q₂_pos (x : Vec) (hx : x ≠ 0) : 0 < q₂ x := by
  have hq := q₁_pos x hx
  have hb : 0 ≤ ternaryPart x := by dsimp [ternaryPart]; positivity
  dsimp only [q₁, q₂] at *
  linarith

/-- A polynomial identity with two quadratic labels, but mixed-parity
outputs which need not be constant on their joint fibers. -/
theorem norm_identity (x : Vec) :
    ∑ i, outputs x i ^ 4 = 2 * (2 * q₁ x - q₂ x) ^ 2 + (q₂ x - q₁ x) ^ 4 := by
  simp only [Fin.sum_univ_four, outputs, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, q₁, q₂, binaryPart, ternaryPart]
  simp only [Matrix.head_cons, Matrix.tail_cons]
  ring

/-- The entire family lies in the previously bounded additive-triple locus. -/
theorem additive_relation (x : Vec) : outputs x 0 + outputs x 1 = outputs x 2 := by
  simp only [outputs, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  simp only [Matrix.head_cons, Matrix.tail_cons]
  ring

def leftInput : Vec := ![11, 1, 1, 1, 1]

def rightInput : Vec := ![10, 8, 1, 1, 1]

theorem positive_fiber_collision :
    (∀ j, 0 < leftInput j ∧ 0 < rightInput j) ∧
    q₁ leftInput = q₁ rightInput ∧ q₂ leftInput = q₂ rightInput ∧
    (∀ i, 0 < outputs leftInput i ∧ 0 < outputs rightInput i) ∧
    outputs leftInput ≠ outputs rightInput := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j
    fin_cases j <;> norm_num [leftInput, rightInput]
  · norm_num [q₁, binaryPart, ternaryPart, leftInput, rightInput, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons]
  · norm_num [q₂, binaryPart, ternaryPart, leftInput, rightInput, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons]
  · intro i
    fin_cases i <;> norm_num [outputs, ternaryPart, leftInput, rightInput, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons]
  · intro h
    have hh := congrFun h 0
    norm_num [outputs, leftInput, rightInput] at hh

theorem explicit_target :
    (∑ i, outputs leftInput i ^ 4) = 265073 ∧
    (∑ i, outputs rightInput i ^ 4) = 265073 := by
  norm_num [Fin.sum_univ_four, outputs, ternaryPart, leftInput, rightInput, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons]

end
end Erdos322Research.JointQuadraticMixedParityExample
