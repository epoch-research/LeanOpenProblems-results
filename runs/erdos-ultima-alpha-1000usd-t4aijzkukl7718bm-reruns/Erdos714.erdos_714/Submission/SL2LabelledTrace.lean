import Submission.TensorObstruction

/-!
A uniform grid obstruction to arbitrary label laws on relative SL2 traces.
This excludes the full labelled model, not the conjectured extremal bound.
-/
noncomputable section
open SimpleGraph Matrix Classical
open scoped MatrixGroups
set_option maxHeartbeats 1000000
namespace Erdos714SL2LabelledTrace
variable {F A B : Type*} [CommRing F]

/-- A unipotent, with the sign chosen for the inverse-relative trace. -/
def row (t : F) : SL(2,F) :=
  ⟨!![1,-t;0,1],by simp [Matrix.det_fin_two]⟩

/-- A determinant-one pencil with constant zero trace and lower-left entry one. -/
def column (x : F) : SL(2,F) :=
  ⟨!![x,-x^2-1;1,-x],by simp [Matrix.det_fin_two]; ring⟩

lemma column_injective : Function.Injective (column : F → SL(2,F)) := by
  intro x y h
  exact congrArg (fun M : SL(2,F) => M 0 0) h

/-- The original relative matrix, not a presumed surrogate, has the desired
trace for every point of the entire column pencil. -/
lemma relative_trace (t x : F) :
    Matrix.trace (((row t)⁻¹*column x : SL(2,F)) : Matrix (Fin 2) (Fin 2) F)=t := by
  simp only [Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.coe_inv,
    row,column,Matrix.adjugate_fin_two,
    Matrix.mul_fin_two,Matrix.trace,Matrix.diag_apply,Fin.sum_univ_two,
    Matrix.of_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
  ring

/-- Label acceptance can be arbitrary. In particular it may demand that the
specified trace represent an elliptic relative matrix. -/
def graph (m : A → B → F) (P : A → B → Prop) :
    SimpleGraph ((SL(2,F) × A) ⊕ (SL(2,F) × B)) :=
  Erdos714Tensor.incidence (fun p q => P p.2 q.2 ∧
    Matrix.trace ((p.1⁻¹*q.1 : SL(2,F)) : Matrix (Fin 2) (Fin 2) F)=m p.2 q.2)

/-- One fixed opposite label supplies a full grid, one row for each accepted
label and one column for each ring element. Distinct trace values are NOT
required: row-label coordinates already give injectivity. -/
def gridCopy (m : A → B → F) (P : A → B → Prop) (b : B) :
    (completeBipartiteGraph {a : A // P a b} F).Copy (graph m P) := by
  let L : {a : A // P a b} ↪ SL(2,F) × A :=
    ⟨fun a => (row (m a b),a),by
      intro a c h
      exact Subtype.ext (congrArg Prod.snd h)⟩
  let R : F ↪ SL(2,F) × B :=
    ⟨fun x => (column x,b),by
      intro x y h
      exact column_injective (congrArg Prod.fst h)⟩
  have he (a : {a : A // P a b}) (x : F) :
      (graph m P).Adj (.inl (L a)) (.inr (R x)) :=
    ⟨a.property,relative_trace (m a b) x⟩
  refine ⟨⟨L.sumMap R,?_⟩,(L.sumMap R).injective⟩
  intro p q hpq
  cases p with
  | inl a => cases q with
    | inl c => simp at hpq
    | inr x => exact he a x
  | inr x => cases q with
    | inl a => exact (he a x).symm
    | inr y => simp at hpq

/-- Four accepted row labels suffice; no Latin-square or surjectivity
hypothesis on the label law can avoid the grid. -/
def finiteCopy (m : A → B → F) (P : A → B → Prop) (b : B) {r s : ℕ}
    (a : Fin r ↪ {a : A // P a b}) (x : Fin s ↪ F) :
    (completeBipartiteGraph (Fin r) (Fin s)).Copy (graph m P) := by
  apply (gridCopy m P b).comp
  refine ⟨⟨a.sumMap x,?_⟩,(a.sumMap x).injective⟩
  intro p q hpq
  cases p <;> cases q <;> simp_all

/-- In a free full model, each opposite label can accept fewer than r row
labels whenever the field/ring itself has at least r elements. -/
theorem support_bound [Fintype F] [Fintype A] (m : A → B → F) (P : A → B → Prop)
    (b : B) (r : ℕ) (hF : r ≤ Fintype.card F)
    (hf : (completeBipartiteGraph (Fin r) (Fin r)).Free (graph m P)) :
    Fintype.card {a : A // P a b}<r := by
  by_contra! h
  obtain ⟨a⟩ := Function.Embedding.nonempty_of_card_le
    (α := Fin r) (β := {a : A // P a b}) (by simpa using h)
  obtain ⟨x⟩ := Function.Embedding.nonempty_of_card_le
    (α := Fin r) (β := F) (by simpa using hF)
  exact hf ⟨finiteCopy m P b a x⟩

end Erdos714SL2LabelledTrace
#print axioms Erdos714SL2LabelledTrace.relative_trace
#print axioms Erdos714SL2LabelledTrace.gridCopy
#print axioms Erdos714SL2LabelledTrace.support_bound
