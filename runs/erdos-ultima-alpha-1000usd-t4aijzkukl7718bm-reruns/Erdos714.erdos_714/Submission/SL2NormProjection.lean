import FormalConjecturesUtil

/-!
A uniform unipotent-grid obstruction for a cubic-norm projection of relative
SL(2) matrices. This does not prove or disprove Erdős 714.
-/

noncomputable section
open SimpleGraph Matrix Classical
open scoped MatrixGroups

namespace Erdos714SL2NormProjection

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- Projection to the cubic coordinate space, with kernel the scalar matrices. -/
def projection (θ : E) (M : Matrix (Fin 2) (Fin 2) F) : E :=
  algebraMap F E (M 0 0-M 1 1) + algebraMap F E (M 0 1)*θ +
    algebraMap F E (M 1 0)*θ^2

def left (s : F) : SL(2,F) :=
  ⟨!![1+s,s; -s,1-s], by simp [Matrix.det_fin_two]; ring⟩

def upperEntry (c : Fˣ) : F := -(1+(c : F)^2)/(2*(c : F))

lemma right_det (h₂ : (2 : F) ≠ 0) (c : Fˣ) :
    (!![upperEntry c,(c : F); (c : F),-2*(c : F)] : Matrix (Fin 2) (Fin 2) F).det = 1 := by
  rw [Matrix.det_fin_two]
  change upperEntry c*(-2*(c : F))-(c : F)*(c : F)=1
  dsimp [upperEntry]
  field_simp
  ring

def right (h₂ : (2 : F) ≠ 0) (c : Fˣ) : SL(2,F) :=
  ⟨!![upperEntry c,(c : F); (c : F),-2*(c : F)], right_det h₂ c⟩

lemma left_injective : Function.Injective (left : F → SL(2,F)) := by
  intro s t he
  exact congrArg (fun M : SL(2,F) => M 0 1) he

lemma right_injective (h₂ : (2 : F) ≠ 0) : Function.Injective (right h₂) := by
  intro c d he
  apply Units.ext
  exact congrArg (fun M : SL(2,F) => M 0 1) he

lemma cube_nonzero {θ : E} (hθ : ∀ a : F, θ ≠ algebraMap F E a) : θ ≠ 0 := by
  simpa using hθ 0

lemma square_not_base {θ : E} (hθ₃ : θ^3 = 2)
    (hθ : ∀ a : F, θ ≠ algebraMap F E a) (a : F) : θ^2 ≠ algebraMap F E a := by
  intro ha
  have ha0 : a ≠ 0 := by
    intro hz
    have he : θ^2 = 0 := by simpa [hz] using ha
    exact pow_ne_zero 2 (cube_nonzero hθ) he
  apply hθ (2/a)
  rw [map_div₀, map_ofNat]
  apply (eq_div_iff (by simpa using (algebraMap F E).injective.ne ha0)).mpr
  rw [← ha]
  convert hθ₃ using 1
  ring

lemma sum_square_not_base {θ : E} (hθ₃ : θ^3 = 2)
    (hθ : ∀ a : F, θ ≠ algebraMap F E a) (a : F) :
    θ+θ^2 ≠ algebraMap F E a := by
  intro ha
  have he : (algebraMap F E a+1)*θ = algebraMap F E a+2 := by
    linear_combination hθ₃ - (θ-1)*ha
  have hn : a+1 ≠ 0 := by
    intro hz
    have hz' : algebraMap F E a+1 = 0 := by
      simpa only [map_add, map_one, map_zero] using congrArg (algebraMap F E) hz
    rw [hz'] at he
    have h01 : (0 : E) = 1 := by linear_combination he + hz'
    exact zero_ne_one h01
  apply hθ ((a+2)/(a+1))
  rw [map_div₀, map_add, map_add, map_one, map_ofNat]
  apply (eq_div_iff (show algebraMap F E a+1 ≠ 0 by
    simpa only [map_add, map_one, map_zero] using (algebraMap F E).injective.ne hn)).mpr
  simpa only [mul_comm] using he

lemma row_factor_ne_zero {θ : E} (hθ₃ : θ^3 = 2)
    (hθ : ∀ a : F, θ ≠ algebraMap F E a) (s : F) :
    1-algebraMap F E s*(1-θ^2) ≠ 0 := by
  intro he
  by_cases hs : s = 0
  · simp [hs] at he
  have hs' : algebraMap F E s ≠ 0 := by simpa using (algebraMap F E).injective.ne hs
  apply square_not_base hθ₃ hθ (1-1/s)
  simp only [map_sub, map_one, map_div₀]
  field_simp
  linear_combination he

lemma right_projection_ne_zero {θ : E} (hθ₃ : θ^3 = 2)
    (hθ : ∀ a : F, θ ≠ algebraMap F E a) (h₂ : (2 : F) ≠ 0) (c : Fˣ) :
    projection (F := F) θ (right h₂ c) ≠ 0 := by
  intro he
  have hc : algebraMap F E (c : F) ≠ 0 :=
    by simp
  apply sum_square_not_base hθ₃ hθ (-(upperEntry c+2*(c : F))/(c : F))
  simp only [map_div₀, map_neg, map_add, map_mul, map_ofNat]
  apply (eq_div_iff hc).mpr
  simp only [projection, right, Matrix.SpecialLinearGroup.coe_mk,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    map_sub, map_neg, map_mul, map_ofNat] at he
  linear_combination he

/-- The key factorization, before taking any norms. -/
theorem projection_factorization {θ : E} (hθ₃ : θ^3 = 2)
    (h₂ : (2 : F) ≠ 0) (s : F) (c : Fˣ) :
    projection (F := F) θ ((left s)⁻¹*right h₂ c) =
      (1-algebraMap F E s*(1-θ^2))*projection (F := F) θ (right h₂ c) := by
  simp only [projection, Matrix.SpecialLinearGroup.coe_inv, left, right, Matrix.SpecialLinearGroup.coe_mk,
    Matrix.adjugate_fin_two, Matrix.mul_fin_two,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    map_sub, map_add, map_mul, map_neg, map_one, map_ofNat]
  linear_combination -(algebraMap F E s*algebraMap F E (c : F)*(θ+1))*hθ₃

variable [FiniteDimensional F E]

abbrev Vertex (F : Type*) [Field F] := SL(2,F) × Fˣ

def graph (θ : E) : SimpleGraph (Vertex F ⊕ Vertex F) where
  Adj x y := match x,y with
    | .inl u, .inr v => Algebra.norm F (projection (F := F) θ (u.1⁻¹*v.1)) = (u.2 : F)*(v.2 : F)
    | .inr v, .inl u => Algebra.norm F (projection (F := F) θ (u.1⁻¹*v.1)) = (u.2 : F)*(v.2 : F)
    | _, _ => False
  symm := by intro x y; cases x <;> cases y <;> simp_all
  loopless := by intro x; cases x <;> simp

/-- Every base-field parameter on the left and every nonzero parameter on the
right occur in an actual complete bipartite copy. -/
def gridCopy (θ : E) (hθ₃ : θ^3 = 2) (hθ : ∀ a : F, θ ≠ algebraMap F E a)
    (h₂ : (2 : F) ≠ 0) :
    Copy (completeBipartiteGraph F Fˣ) (graph (F := F) θ) := by
  let L : F ↪ Vertex F :=
    ⟨fun s => (left s, Units.mk0 _ (Algebra.norm_ne_zero_iff.mpr (row_factor_ne_zero hθ₃ hθ s))), by
      intro s t he
      exact left_injective (congrArg Prod.fst he)⟩
  let R : Fˣ ↪ Vertex F :=
    ⟨fun c => (right h₂ c, Units.mk0 _ (Algebra.norm_ne_zero_iff.mpr
      (right_projection_ne_zero hθ₃ hθ h₂ c))), by
      intro c d he
      exact right_injective h₂ (congrArg Prod.fst he)⟩
  have he (s : F) (c : Fˣ) : (graph (F := F) θ).Adj (.inl (L s)) (.inr (R c)) := by
    change Algebra.norm F (projection (F := F) θ ((left s)⁻¹*right h₂ c)) =
      Algebra.norm F (1-algebraMap F E s*(1-θ^2))*Algebra.norm F (projection (F := F) θ (right h₂ c))
    rw [projection_factorization hθ₃, map_mul]
  refine ⟨⟨L.sumMap R, ?_⟩, (L.sumMap R).injective⟩
  intro x y h
  cases x with
  | inl s =>
    cases y with
    | inl t => simp at h
    | inr c => exact he s c
  | inr c =>
    cases y with
    | inr d => simp at h
    | inl s => exact he s c

theorem not_free [Fintype F] (θ : E) (hθ₃ : θ^3 = 2)
    (hθ : ∀ a : F, θ ≠ algebraMap F E a) (h₂ : (2 : F) ≠ 0)
    (hcard : 5 ≤ Fintype.card F) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph (F := F) θ) := by
  let e : Fin 4 ↪ F := (Fin.castLEEmb (by omega : 4 ≤ Fintype.card F)).trans
    (Fintype.equivFin F).symm.toEmbedding
  have hc : 4 ≤ Fintype.card Fˣ := by rw [Fintype.card_units]; omega
  let f : Fin 4 ↪ Fˣ := (Fin.castLEEmb hc).trans (Fintype.equivFin Fˣ).symm.toEmbedding
  let small : Copy (completeBipartiteGraph (Fin 4) (Fin 4))
      (completeBipartiteGraph F Fˣ) :=
    ⟨⟨e.sumMap f, by intro x y h; cases x <;> cases y <;> simp_all⟩,
      (e.sumMap f).injective⟩
  intro hf
  exact hf ⟨(gridCopy θ hθ₃ hθ h₂).comp small⟩

end Erdos714SL2NormProjection

#print axioms Erdos714SL2NormProjection.projection_factorization
#print axioms Erdos714SL2NormProjection.gridCopy
#print axioms Erdos714SL2NormProjection.not_free
