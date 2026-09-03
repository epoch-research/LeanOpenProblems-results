import FormalConjecturesUtil

/-!
Exact Jacobian-sign obstructions even when minus one is a nonsquare.
The field is F_11; the polynomial and norm identities are checked directly.
This file does not prove or disprove Erdős 714.
-/

open SimpleGraph MvPolynomial

namespace Erdos714NormJacobianNonsquare

/-- The norm form of the cubic algebra with `θ³ + 2θ - 2 = 0`. -/
def normForm {R : Type*} [CommRing R] (v : Fin 3 → R) : R :=
  v 0 ^ 3 + 2 * v 0 * v 1 ^ 2 + 2 * v 1 ^ 3 - 4 * v 0 ^ 2 * v 2 -
    6 * v 0 * v 1 * v 2 + 4 * v 0 * v 2 ^ 2 + 4 * v 1 * v 2 ^ 2 + 4 * v 2 ^ 3

/-- Multiplication in the displayed cubic algebra. -/
def mul {R : Type*} [CommRing R] (x y : Fin 3 → R) : Fin 3 → R :=
  ![x 0 * y 0 + 2 * (x 1 * y 2 + x 2 * y 1),
    x 0 * y 1 + x 1 * y 0 - 2 * (x 1 * y 2 + x 2 * y 1) + 2 * x 2 * y 2,
    x 0 * y 2 + x 1 * y 1 + x 2 * y 0 - 2 * x 2 * y 2]

theorem normForm_eq_det {R : Type*} [CommRing R] (v : Fin 3 → R) :
    normForm v = Matrix.det
      !![v 0, 2 * v 2, 2 * v 1;
         v 1, v 0 - 2 * v 2, 2 * v 2 - 2 * v 1;
         v 2, v 1, v 0 - 2 * v 2] := by
  simp [Matrix.det_fin_three, normForm]
  ring

abbrev F := ZMod 11
instance : Fact (Nat.Prime 11) := ⟨by decide⟩

abbrev V := Fin 3 → F

def rowPoints : Fin 4 → V := ![![0,0,0], ![1,0,0], ![0,1,0], ![0,0,1]]

def rowWeights : Bool → Fin 4 → F
  | false => ![1,10,2,4]
  | true => ![1,5,8,10]

def columnPoints : Bool → Fin 4 → V
  | false => ![![1,8,10], ![7,2,3], ![4,1,8], ![3,1,2]]
  | true => ![![10,3,6], ![3,9,4], ![2,8,0], ![10,8,5]]

def columnWeights : Bool → Fin 4 → F
  | false => ![5,7,3,1]
  | true => ![6,3,1,5]

def inversePoints : Bool → Fin 4 → V
  | false => ![![2,1,9], ![9,10,8], ![3,1,3], ![10,5,3]]
  | true => ![![5,7,9], ![9,9,8], ![0,6,9], ![3,5,4]]

/-- The three normalized norm polynomials, before subtracting their target weights. -/
noncomputable def equations : Fin 3 → MvPolynomial (Fin 3) F :=
  ![normForm ![1 + X 0, X 1, X 2],
    normForm ![1 + 2 * X 2, X 0 - 2 * X 2, X 1],
    normForm ![1 + 2 * X 1, 2 * X 2 - 2 * X 1, X 0 - 2 * X 2]]

/-- The determinant uses actual formal partial derivatives, not an assigned sign label. -/
noncomputable def jacobian (v : V) : F :=
  Matrix.det (fun i j : Fin 3 => MvPolynomial.eval v (pderiv j (equations i)))

@[simp] theorem pderiv_ofNat (i : Fin 3) (n : ℕ) [n.AtLeastTwo] :
    pderiv i (ofNat(n) : MvPolynomial (Fin 3) F) = 0 := (pderiv i).map_natCast n

def gradient {R : Type*} [CommRing R] (v : Fin 3 → R) : Fin 3 → R :=
  ![3 * v 0 ^ 2 + 2 * v 1 ^ 2 - 8 * v 0 * v 2 - 6 * v 1 * v 2 + 4 * v 2 ^ 2,
    4 * v 0 * v 1 + 6 * v 1 ^ 2 - 6 * v 0 * v 2 + 4 * v 2 ^ 2,
    -4 * v 0 ^ 2 - 6 * v 0 * v 1 + 8 * v 0 * v 2 + 8 * v 1 * v 2 + 12 * v 2 ^ 2]

def jacMatrix {R : Type*} [CommRing R] (v : Fin 3 → R) : Matrix (Fin 3) (Fin 3) R :=
  let g₀ := gradient ![1 + v 0, v 1, v 2]
  let g₁ := gradient ![1 + 2 * v 2, v 0 - 2 * v 2, v 1]
  let g₂ := gradient ![1 + 2 * v 1, 2 * v 2 - 2 * v 1, v 0 - 2 * v 2]
  ![g₀, ![g₁ 1, g₁ 2, 2 * g₁ 0 - 2 * g₁ 1],
    ![g₂ 2, 2 * g₂ 0 - 2 * g₂ 1, 2 * g₂ 1 - 2 * g₂ 2]]

set_option maxHeartbeats 1000000 in
theorem derivative_eq (i j : Fin 3) :
    pderiv j (equations i) = jacMatrix (fun k => X k) i j := by
  fin_cases i <;> fin_cases j <;>
    simp [equations, normForm, jacMatrix, gradient] <;> ring

set_option maxHeartbeats 1000000 in
theorem eval_jacMatrix (v : V) (i j : Fin 3) :
    MvPolynomial.eval v (jacMatrix (fun k => X k) i j) = jacMatrix v i j := by
  fin_cases i <;> fin_cases j <;>
    simp only [jacMatrix, gradient, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      Matrix.cons_val_zero', Matrix.cons_val_succ'] <;>
    simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_neg, eval_ofNat, map_one, eval_X]

theorem jacobian_eq (v : V) : jacobian v = (jacMatrix v).det := by
  unfold jacobian
  congr 1
  ext i j
  rw [derivative_eq, eval_jacMatrix]

def jacobianValues : Bool → Fin 4 → F
  | false => ![2,10,10,2]
  | true => ![3,4,3,4]

set_option maxHeartbeats 1000000 in
theorem jacobian_values (s : Bool) (i : Fin 4) :
    jacobian (inversePoints s i) = jacobianValues s i := by
  rw [jacobian_eq]
  cases s <;> fin_cases i <;> decide

/-- The algebra is not split over the base field. -/
theorem cubic_irreducible :
    Irreducible (Polynomial.X ^ 3 + 2 * Polynomial.X - 2 : Polynomial F) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · have h : (Polynomial.X ^ 3 + 2 * Polynomial.X - 2 : Polynomial F).natDegree = 3 := by
      compute_degree!
    rw [h]
    decide
  · have h : ∀ x : F, x ^ 3 + 2 * x - 2 ≠ 0 := by decide
    simpa [Polynomial.IsRoot] using h

theorem rowPoints_injective : Function.Injective rowPoints := by decide

theorem columnPoints_injective (s : Bool) : Function.Injective (columnPoints s) := by
  cases s <;> decide

theorem inversePoints_injective (s : Bool) : Function.Injective (inversePoints s) := by
  cases s <;> decide

theorem inverses (s : Bool) (i : Fin 4) :
    mul (columnPoints s i) (inversePoints s i) = ![1,0,0] := by
  cases s <;> fin_cases i <;> decide

theorem norm_equations (s : Bool) (i j : Fin 4) :
    normForm (rowPoints i + columnPoints s j) = rowWeights s i * columnWeights s j := by
  cases s <;> fin_cases i <;> fin_cases j <;> decide

theorem nonzero_weights (s : Bool) (i : Fin 4) :
    rowWeights s i ≠ 0 ∧ columnWeights s i ≠ 0 := by
  cases s <;> fin_cases i <;> decide

theorem normForm_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (v : Fin 3 → R) : f (normForm v) = normForm (fun i => f (v i)) := by
  simp only [normForm, map_add, map_sub, map_mul, map_pow, map_ofNat]

set_option maxHeartbeats 1000000 in
theorem eval_equations (v : V) (i : Fin 3) :
    MvPolynomial.eval v (equations i) =
      normForm (![1,0,0] + mul (rowPoints i.succ) v) := by
  fin_cases i <;>
    simp only [equations, Matrix.cons_val_zero', Matrix.cons_val_succ'] <;>
    rw [normForm_map] <;> congr 1 <;> ext k <;> fin_cases k <;>
    simp [rowPoints, mul, Matrix.cons_val_two, eval_add, eval_sub, eval_mul,
      eval_ofNat, map_one, eval_X]
  ring

set_option maxHeartbeats 1000000 in
theorem normalized_equations (s : Bool) (i : Fin 3) (j : Fin 4) :
    MvPolynomial.eval (inversePoints s j) (equations i) = rowWeights s i.succ := by
  rw [eval_equations]
  cases s <;> fin_cases i <;> fin_cases j <;> decide

theorem jacobian_nonzero (s : Bool) (i : Fin 4) : jacobian (inversePoints s i) ≠ 0 := by
  rw [jacobian_values]
  cases s <;> fin_cases i <;> decide

theorem jacobian_square (s : Bool) (i : Fin 4) :
    IsSquare (jacobian (inversePoints s i)) ↔ s = true := by
  rw [jacobian_values]
  cases s <;> fin_cases i <;> decide +kernel

/-- Either square class admits four distinct simple roots of one normalized norm fiber. -/
theorem four_roots_one_sign (s : Bool) :
    ∃ a : Fin 3 → F, ∃ f : Fin 4 ↪ V, ∀ j,
      (∀ i, MvPolynomial.eval (f j) (equations i) = a i) ∧
      jacobian (f j) ≠ 0 ∧ (IsSquare (jacobian (f j)) ↔ s = true) := by
  refine ⟨fun i => rowWeights s i.succ, ⟨inversePoints s, inversePoints_injective s⟩, ?_⟩
  intro j
  exact ⟨fun i => normalized_equations s i j, jacobian_nonzero s j, jacobian_square s j⟩

/-- The new examples meet the nonsquare-minus-one condition. -/
theorem minus_one_not_square : ¬ IsSquare (-1 : F) := by decide +kernel

/-- The additional field condition still permits four distinct simple roots
of either one of the two nonzero Jacobian square classes. -/
theorem nonsquare_minus_one_not_enough (s : Bool) :
    ¬ IsSquare (-1 : F) ∧
      ∃ a : Fin 3 → F, ∃ f : Fin 4 ↪ V, ∀ j,
        (∀ i, MvPolynomial.eval (f j) (equations i) = a i) ∧
        jacobian (f j) ≠ 0 ∧ (IsSquare (jacobian (f j)) ↔ s = true) :=
  ⟨minus_one_not_square, four_roots_one_sign s⟩

/-- The unmodified weighted coordinate norm graph, with nonzero weights on edges. -/
def graph : SimpleGraph (Bool × (V × F)) where
  Adj u v := u.1 ≠ v.1 ∧ u.2.2 ≠ 0 ∧ v.2.2 ≠ 0 ∧
    normForm (u.2.1 + v.2.1) = u.2.2 * v.2.2
  symm := by
    intro u v h
    exact ⟨h.1.symm, h.2.2.1, h.2.1, by simpa [add_comm, mul_comm] using h.2.2.2⟩
  loopless := by intro v h; exact h.1 rfl

def row (s : Bool) (i : Fin 4) : Bool × (V × F) :=
  (false, rowPoints i, rowWeights s i)

def column (s : Bool) (i : Fin 4) : Bool × (V × F) :=
  (true, columnPoints s i, columnWeights s i)

theorem graph_edges (s : Bool) (i j : Fin 4) : graph.Adj (row s i) (column s j) :=
  ⟨Bool.false_ne_true, (nonzero_weights s i).1, (nonzero_weights s j).2,
    norm_equations s i j⟩

/-- Both sign certificates are actual copies with all eight vertices distinct. -/
def copy (s : Bool) :
    (completeBipartiteGraph (Fin 4) (Fin 4)).Copy graph := by
  refine ⟨⟨Sum.elim (row s) (column s), ?_⟩, ?_⟩
  ·
    intro u v h
    cases u with
    | inl i =>
      cases v with
      | inl j => simp at h
      | inr j => exact graph_edges s i j
    | inr i =>
      cases v with
      | inl j => exact (graph_edges s j i).symm
      | inr j => simp at h
  · cases s <;> decide

theorem graph_not_free : ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free graph :=
  fun h => h ⟨copy false⟩

#print axioms nonsquare_minus_one_not_enough
#print axioms normForm_eq_det
#print axioms cubic_irreducible
#print axioms normalized_equations
#print axioms jacobian_values
#print axioms four_roots_one_sign
#print axioms graph_not_free

end Erdos714NormJacobianNonsquare
