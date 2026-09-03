import FormalConjecturesUtil

/-!
An obstruction to the additive quartic norm lift on a trace-zero subspace.
This development does not prove or disprove Erdős Problem 714.
-/

open SimpleGraph

namespace Erdos714QuarticNormLift

variable {F K : Type*} [CommRing F] [CommRing K]

/-- Norm coordinates for `a(z+2)+b(z²+2)+c(z³+2)` when
`z⁴+2z³+2=0` in characteristic three. -/
def normForm (v : Fin 3 → F) : F :=
  -v 0 ^ 4 + v 0 ^ 3 * v 1 - v 0 * v 1 ^ 3 - v 1 ^ 4 -
    v 0 * v 1 ^ 2 * v 2 + v 1 ^ 3 * v 2 - v 0 ^ 2 * v 2 ^ 2 -
    v 0 * v 1 * v 2 ^ 2 - v 1 ^ 2 * v 2 ^ 2 - v 0 * v 2 ^ 3 - v 2 ^ 4

/-- Multiplication matrix of the trace-zero element in the basis `1,z,z²,z³`. -/
def multiplicationMatrix (v : Fin 3 → F) : Matrix (Fin 4) (Fin 4) F :=
  !![-v 0-v 1-v 2, v 2, v 1+v 2, v 0+v 1+v 2;
     v 0, -v 0-v 1-v 2, v 2, v 1+v 2;
     v 1, v 0, -v 0-v 1-v 2, v 2;
     v 2, v 1+v 2, v 0+v 1+v 2, 0]


/-- The displayed quartic is exactly the determinant of this multiplication matrix. -/
theorem normForm_eq_det [CharP F 3] (v : Fin 3 → F) :
    normForm v = (multiplicationMatrix v).det := by
  have h3 : (3 : F) = 0 := CharP.cast_eq_zero F 3
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_four]
  simp only [Matrix.det_fin_three]
  change normForm v =
    ((-1 : F)^0 * (-v 0-v 1-v 2) * ((-v 0-v 1-v 2)*(-v 0-v 1-v 2)*(0) - (-v 0-v 1-v 2)*(v 2)*(v 0+v 1+v 2) - (v 2)*(v 0)*(0) + (v 2)*(v 2)*(v 1+v 2) + (v 1+v 2)*(v 0)*(v 0+v 1+v 2) - (v 1+v 2)*(-v 0-v 1-v 2)*(v 1+v 2))) +
    ((-1 : F)^1 * (v 2) * ((v 0)*(-v 0-v 1-v 2)*(0) - (v 0)*(v 2)*(v 0+v 1+v 2) - (v 2)*(v 1)*(0) + (v 2)*(v 2)*(v 2) + (v 1+v 2)*(v 1)*(v 0+v 1+v 2) - (v 1+v 2)*(-v 0-v 1-v 2)*(v 2))) +
    ((-1 : F)^2 * (v 1+v 2) * ((v 0)*(v 0)*(0) - (v 0)*(v 2)*(v 1+v 2) - (-v 0-v 1-v 2)*(v 1)*(0) + (-v 0-v 1-v 2)*(v 2)*(v 2) + (v 1+v 2)*(v 1)*(v 1+v 2) - (v 1+v 2)*(v 0)*(v 2))) +
    ((-1 : F)^3 * (v 0+v 1+v 2) * ((v 0)*(v 0)*(v 0+v 1+v 2) - (v 0)*(-v 0-v 1-v 2)*(v 1+v 2) - (-v 0-v 1-v 2)*(v 1)*(v 0+v 1+v 2) + (-v 0-v 1-v 2)*(-v 0-v 1-v 2)*(v 2) + (v 2)*(v 1)*(v 1+v 2) - (v 2)*(v 0)*(v 2)))
  unfold normForm
  linear_combination
    (2*(v 0)^3*(v 1) + 2*(v 0)^3*(v 2) + 3*(v 0)^2*(v 1)^2 +
      7*(v 0)^2*(v 1)*(v 2) + 3*(v 0)^2*(v 2)^2 + 2*(v 0)*(v 1)^3 +
      9*(v 0)*(v 1)^2*(v 2) + 11*(v 0)*(v 1)*(v 2)^2 + 4*(v 0)*(v 2)^3 +
      3*(v 1)^3*(v 2) + 6*(v 1)^2*(v 2)^2 + 6*(v 1)*(v 2)^3 + 2*(v 2)^4) * h3

/-- Every element represented by these coordinates has trace zero. -/
theorem multiplicationMatrix_trace [CharP F 3] (v : Fin 3 → F) :
    (multiplicationMatrix v).trace = 0 := by
  have h3 : (3 : F) = 0 := CharP.cast_eq_zero F 3
  simp [multiplicationMatrix, Matrix.trace, Fin.sum_univ_four]
  linear_combination -(v 0 + v 1 + v 2) * h3


section NormInterpretation

variable {E : Type*} [CommRing E] [Algebra F E]

/-- The element in the indicated trace-zero coordinates. In characteristic
three, `z-1` is the same as `z+2`. -/
def coordinateElement (z : E) (v : Fin 3 → F) : E :=
  algebraMap F E (v 0) * (z - 1) + algebraMap F E (v 1) * (z^2 - 1) +
    algebraMap F E (v 2) * (z^3 - 1)

/-- The displayed matrix genuinely represents multiplication in the quartic algebra. -/
theorem leftMulMatrix_coordinate (z : E) (hz : z^4 = z^3 + 1)
    (b : Module.Basis (Fin 4) F E) (hb : ∀ i, b i = z^(i : ℕ)) (v : Fin 3 → F) :
    Algebra.leftMulMatrix b (coordinateElement z v) = multiplicationMatrix v := by
  have hz5 : z^5 = z^3 + z + 1 := by
    calc
      z^5 = z^4*z := by ring
      _ = (z^3+1)*z := by rw [hz]
      _ = z^4+z := by ring
      _ = z^3+z+1 := by rw [hz]; ring
  have hz6 : z^6 = z^3 + z^2 + z + 1 := by
    calc
      z^6 = z^5*z := by ring
      _ = (z^3+z+1)*z := by rw [hz5]
      _ = z^4+z^2+z := by ring
      _ = z^3+z^2+z+1 := by rw [hz]; ring
  have hcol (j : Fin 4) :
      ∑ i, (multiplicationMatrix v i j) • b i = coordinateElement z v * b j := by
    simp only [Fin.sum_univ_four, hb, Algebra.smul_def]
    fin_cases j
    · change algebraMap F E (-v 0-v 1-v 2) * z^0 + algebraMap F E (v 0) * z^1 + algebraMap F E (v 1) * z^2 + algebraMap F E (v 2) * z^3 = coordinateElement z v * z^0
      simp only [map_neg, map_sub]
      unfold coordinateElement
      ring
    · change algebraMap F E (v 2) * z^0 + algebraMap F E (-v 0-v 1-v 2) * z^1 + algebraMap F E (v 0) * z^2 + algebraMap F E (v 1+v 2) * z^3 = coordinateElement z v * z^1
      simp only [map_neg, map_sub, map_add]
      unfold coordinateElement
      ring_nf
      rw [hz]
      ring
    · change algebraMap F E (v 1+v 2) * z^0 + algebraMap F E (v 2) * z^1 + algebraMap F E (-v 0-v 1-v 2) * z^2 + algebraMap F E (v 0+v 1+v 2) * z^3 = coordinateElement z v * z^2
      simp only [map_neg, map_sub, map_add]
      unfold coordinateElement
      ring_nf
      rw [hz5, hz]
      ring
    · change algebraMap F E (v 0+v 1+v 2) * z^0 + algebraMap F E (v 1+v 2) * z^1 + algebraMap F E (v 2) * z^2 + algebraMap F E (0) * z^3 = coordinateElement z v * z^3
      simp only [map_add, map_zero]
      unfold coordinateElement
      ring_nf
      rw [hz5, hz6, hz]
      ring
  ext i j
  rw [Algebra.leftMulMatrix_eq_repr_mul, ← hcol j]
  simp [Finsupp.single_apply]

/-- Identification with the library's algebra norm, given the natural quartic basis. -/
theorem coordinate_norm [CharP F 3] (z : E) (hz : z^4 = z^3 + 1)
    (b : Module.Basis (Fin 4) F E) (hb : ∀ i, b i = z^(i : ℕ)) (v : Fin 3 → F) :
    Algebra.norm F (coordinateElement z v) = normForm v := by
  rw [Algebra.norm_eq_matrix_det b, leftMulMatrix_coordinate z hz b hb,
    ← normForm_eq_det]

/-- Identification of the trace-zero property with the library's algebra trace. -/
theorem coordinate_trace [CharP F 3] (z : E) (hz : z^4 = z^3 + 1)
    (b : Module.Basis (Fin 4) F E) (hb : ∀ i, b i = z^(i : ℕ)) (v : Fin 3 → F) :
    Algebra.trace F E (coordinateElement z v) = 0 := by
  rw [Algebra.trace_eq_matrix_trace b, leftMulMatrix_coordinate z hz b hb,
    multiplicationMatrix_trace]

end NormInterpretation

lemma map_normForm (f : F →+* K) (v : Fin 3 → F) :
    normForm (fun i => f (v i)) = f (normForm v) := by
  simp [normForm]

/-- The additive-weight graph; the weights are arbitrary, not just nonzero. -/
def graph : SimpleGraph (Bool × ((Fin 3 → F) × F)) where
  Adj u v := u.1 ≠ v.1 ∧ normForm (u.2.1 + v.2.1) = u.2.2 + v.2.2
  symm := by
    intro u v h
    exact ⟨h.1.symm, by simpa only [add_comm] using h.2⟩
  loopless := by intro v h; exact h.1 rfl

private def left : Fin 4 → Bool × ((Fin 3 → ZMod 3) × ZMod 3) := fun i =>
  (false, (![![0,0,0], ![0,0,1], ![0,0,-1], ![0,1,0]] i, ![0,1,1,1] i))

private def right : Fin 4 → Bool × ((Fin 3 → ZMod 3) × ZMod 3) := fun i =>
  (true, (![![0,1,1], ![0,-1,-1], ![1,-1,0], ![-1,0,1]] i, 1))

private lemma all_edges (i j : Fin 4) : graph.Adj (left i) (right j) := by
  dsimp only [graph]
  fin_cases i <;> fin_cases j <;> decide

private lemma left_injective : Function.Injective left := by decide
private lemma right_injective : Function.Injective right := by decide

/-- A kernel-checked prime-field certificate. -/
theorem prime_field_not_free :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph (F := ZMod 3)) := by
  intro hfree
  apply hfree
  refine ⟨⟨⟨Sum.elim left right, ?_⟩, ?_⟩⟩
  · intro a b hab
    cases a with
    | inl i =>
      cases b with
      | inl j => simp at hab
      | inr j => exact all_edges i j
    | inr i =>
      cases b with
      | inl j => exact (all_edges j i).symm
      | inr j => simp at hab
  · intro a b hab
    cases a with
    | inl i =>
      cases b with
      | inl j => exact congrArg Sum.inl (left_injective hab)
      | inr j => exact False.elim (Bool.false_ne_true (congrArg Prod.fst hab))
    | inr i =>
      cases b with
      | inl j => exact False.elim (Bool.false_ne_true (congrArg Prod.fst hab).symm)
      | inr j => exact congrArg Sum.inr (right_injective hab)

/-- An injective coefficient map preserves this graph construction. -/
def mapCopy (f : F →+* K) (hf : Function.Injective f) :
    Copy (graph (F := F)) (graph (F := K)) where
  toHom := {
    toFun := fun v => (v.1, (fun i => f (v.2.1 i), f v.2.2))
    map_rel' := by
      intro u v h
      refine ⟨h.1, ?_⟩
      change normForm ((fun i => f (u.2.1 i)) + fun i => f (v.2.1 i)) =
        f u.2.2 + f v.2.2
      have he : ((fun i => f (u.2.1 i)) + fun i => f (v.2.1 i)) =
          (fun i => f ((u.2.1 + v.2.1) i)) := by
        funext i
        simp
      rw [he, map_normForm, h.2, map_add] }
  injective' := by
    intro u v h
    apply Prod.ext
    · exact congrArg (fun w : Bool × ((Fin 3 → K) × K) => w.1) h
    · apply Prod.ext
      · funext i
        exact hf (congrArg (fun w => w.2.1 i) h)
      · exact hf (congrArg (fun w => w.2.2) h)

/-- The same witnesses survive every injective extension of the prime field. -/
theorem not_free_of_prime_field (f : ZMod 3 →+* F) (hf : Function.Injective f) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph (F := F)) := by
  intro hfree
  apply prime_field_not_free
  rintro ⟨c⟩
  exact hfree ⟨(mapCopy f hf).comp c⟩

/-- A uniform obstruction over all nontrivial characteristic-three rings. -/
theorem not_free [Nontrivial F] [CharP F 3] :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph (F := F)) := by
  let f : ZMod 3 →+* F := ZMod.castHom (dvd_refl 3) F
  exact not_free_of_prime_field f f.injective


section ActualNormGraph

variable {E : Type*} [CommRing E] [Algebra F E]

/-- The actual algebra-norm graph on trace-zero elements with additive weights. -/
def normGraph : SimpleGraph (Bool × ({x : E // Algebra.trace F E x = 0} × F)) where
  Adj u v := u.1 ≠ v.1 ∧ Algebra.norm F (u.2.1.val + v.2.1.val) = u.2.2 + v.2.2
  symm := by
    intro u v h
    exact ⟨h.1.symm, by simpa only [add_comm] using h.2⟩
  loopless := by intro v h; exact h.1 rfl

lemma coordinateElement_add (z : E) (v w : Fin 3 → F) :
    coordinateElement z (v+w) = coordinateElement z v + coordinateElement z w := by
  simp [coordinateElement]
  ring

lemma coordinateElement_injective (z : E) (hz : z^4 = z^3 + 1)
    (b : Module.Basis (Fin 4) F E) (hb : ∀ i, b i = z^(i : ℕ)) :
    Function.Injective (coordinateElement (F := F) z) := by
  intro v w h
  have hm := congrArg (Algebra.leftMulMatrix b) h
  rw [leftMulMatrix_coordinate z hz b hb, leftMulMatrix_coordinate z hz b hb] at hm
  funext i
  fin_cases i
  · exact congrArg (fun M : Matrix (Fin 4) (Fin 4) F => M 1 0) hm
  · exact congrArg (fun M : Matrix (Fin 4) (Fin 4) F => M 2 0) hm
  · exact congrArg (fun M : Matrix (Fin 4) (Fin 4) F => M 3 0) hm

/-- The coordinate certificate embeds into the algebra-norm graph itself. -/
def normGraphCopy [CharP F 3] (z : E) (hz : z^4 = z^3 + 1)
    (b : Module.Basis (Fin 4) F E) (hb : ∀ i, b i = z^(i : ℕ)) :
    Copy (graph (F := F)) (normGraph (F := F) (E := E)) where
  toHom := {
    toFun := fun v => (v.1,
      (⟨coordinateElement z v.2.1, coordinate_trace z hz b hb v.2.1⟩, v.2.2))
    map_rel' := by
      intro u v h
      refine ⟨h.1, ?_⟩
      change Algebra.norm F (coordinateElement z u.2.1 + coordinateElement z v.2.1) =
        u.2.2 + v.2.2
      rw [← coordinateElement_add, coordinate_norm z hz b hb]
      exact h.2 }
  injective' := by
    intro u v h
    apply Prod.ext
    · exact congrArg (fun w : Bool × ({x : E // Algebra.trace F E x = 0} × F) => w.1) h
    · apply Prod.ext
      · apply coordinateElement_injective z hz b hb
        exact congrArg (fun w : Bool × ({x : E // Algebra.trace F E x = 0} × F) => w.2.1.val) h
      · exact congrArg (fun w : Bool × ({x : E // Algebra.trace F E x = 0} × F) => w.2.2) h

/-- The quartic-extension candidate fails whenever it has this power basis.
No claim about arbitrary extremal graphs is made. -/
theorem normGraph_not_free [Nontrivial F] [CharP F 3]
    (z : E) (hz : z^4 = z^3 + 1)
    (b : Module.Basis (Fin 4) F E) (hb : ∀ i, b i = z^(i : ℕ)) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (normGraph (F := F) (E := E)) := by
  intro hfree
  apply not_free (F := F)
  rintro ⟨c⟩
  exact hfree ⟨(normGraphCopy z hz b hb).comp c⟩

end ActualNormGraph

end Erdos714QuarticNormLift

#print axioms Erdos714QuarticNormLift.prime_field_not_free
#print axioms Erdos714QuarticNormLift.not_free_of_prime_field

#print axioms Erdos714QuarticNormLift.normForm_eq_det
#print axioms Erdos714QuarticNormLift.multiplicationMatrix_trace
#print axioms Erdos714QuarticNormLift.not_free

#print axioms Erdos714QuarticNormLift.coordinate_norm
#print axioms Erdos714QuarticNormLift.coordinate_trace

#print axioms Erdos714QuarticNormLift.normGraph_not_free
