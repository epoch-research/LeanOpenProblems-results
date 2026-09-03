import Submission.BinaryConicPoints
import Submission.SL2NormProjection
import Submission.CubicEmbedding

/-! A uniform obstruction to cubic Kummer projections of relative SL₂ matrices.
The two-dimensional rank-drop fiber meets SL₂ in a nonsingular binary conic.
This is an obstruction to this candidate, not to Erdős 714. -/

noncomputable section
open Polynomial Matrix SimpleGraph Classical
open scoped MatrixGroups
open Erdos714SL2NormProjection

namespace Erdos714SL2Kummer
variable {F E : Type*} [Field F] [Field E] [Algebra F E]

-- The chosen nilpotent pencil and its two-dimensional rank-drop fiber.
def nilpotent (s : F) : Matrix (Fin 2) (Fin 2) F := !![s,1;-s^2,-s]

def unipotent (s t : F) : SL(2,F) :=
  ⟨!![1-t*s,-t;t*s^2,1+t*s], by simp [Matrix.det_fin_two]; ring⟩

lemma unipotent_injective (s : F) : Function.Injective (unipotent s) := by
  intro t u h
  have hh := congrArg (fun M : SL(2,F) => M 0 1) h
  exact neg_injective hh

def ca (d s : F) : F := (d+1)*s^3/(s^3+2)
def cb (d s : F) : F := -(d+1)*(d+4)*s^4/((s^3+2)*(d*s^3-2))
def cc (d s : F) : F := -(d+1)*s^2*(2*s^3+1)/((s^3+2)*(d*s^3-2))
def cw (s : F) : F := -3*s/(s^3+2)
def k₀ (d s : F) : F := -s*(d^2*s^3+2*d*s^3+4)/(d^2*s^3+8)
def k₁ (d s : F) : F := (d+4)*s^3/(d^2*s^3+8)
def k₂ (d s : F) : F := s^2*(d*s^3-2)/(d^2*s^3+8)

def fiber (d s A B : F) : Matrix (Fin 2) (Fin 2) F :=
  !![A,B;(cw s-cb d s)*A-cc d s*B,ca d s*A+cw s*B]

lemma fiber_det (d s A B : F) :
    (fiber d s A B).det = ca d s*A^2+cb d s*A*B+cc d s*B^2 := by
  simp [fiber, Matrix.det_fin_two]
  ring

structure Good (d s : F) : Prop where
  s_ne : s ≠ 0
  first : s^3+2 ≠ 0
  second : d*s^3-2 ≠ 0
  third : d^2*s^3+8 ≠ 0
  last : 8*d*s^6+(d^2+12*d)*s^3-8 ≠ 0

lemma coeffs (d s A B : F) (h : Good d s) :
    let C := (cw s-cb d s)*A-cc d s*B
    let D := ca d s*A+cw s*B
    (s*A+C+s^2*B+s*D = k₀ d s*(A-D)+d*k₁ d s*C+d*k₂ d s*B) ∧
    (s*B+D = k₀ d s*B+k₁ d s*(A-D)+d*k₂ d s*C) ∧
    (-s^2*A-s*C = k₀ d s*C+k₁ d s*B+k₂ d s*(A-D)) := by
  dsimp [ca,cb,cc,cw,k₀,k₁,k₂]
  have h₁ := h.first
  have h₂ := h.second
  have h₃ := h.third
  have h₂' : s^3*d-2 ≠ 0 := by simpa only [mul_comm] using h₂
  have h₃' : s^3*d^2+8 ≠ 0 := by simpa only [mul_comm] using h₃
  constructor
  · field_simp [h₁,h₂,h₃,h₂',h₃']; ring
  constructor <;> (field_simp [h₁,h₂,h₃,h₂',h₃']; ring)

lemma discriminant (d s : F) (h : Good d s) :
    (cb d s)^2-4*ca d s*cc d s =
      (d+1)^2*s^5*(8*d*s^6+(d^2+12*d)*s^3-8)/((s^3+2)^2*(d*s^3-2)^2) := by
  dsimp [ca,cb,cc]
  have h₁ := h.first
  have h₂ := h.second
  field_simp
  ring

lemma leading_ne_zero {d s : F} (hd : d+1 ≠ 0) (h : Good d s) : ca d s ≠ 0 :=
  div_ne_zero (mul_ne_zero hd (pow_ne_zero _ h.s_ne)) h.first

lemma discriminant_ne_zero {d s : F} (hd : d+1 ≠ 0) (h : Good d s) :
    (cb d s)^2-4*ca d s*cc d s ≠ 0 := by
  rw [discriminant _ _ h]
  exact div_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hd) (pow_ne_zero _ h.s_ne)) h.last)
    (mul_ne_zero (pow_ne_zero _ h.first) (pow_ne_zero _ h.second))

lemma k₂_ne_zero {d s : F} (h : Good d s) : k₂ d s ≠ 0 :=
  div_ne_zero (mul_ne_zero (pow_ne_zero _ h.s_ne) h.second) h.third

lemma exists_good [Fintype F] (h₂ : (2 : F) ≠ 0) (d : F) (hq : 16 < Fintype.card F) :
    ∃ s : F, Good d s := by
  let p : F[X] := X*(X^3+2)*(C d*X^3-2)*(C (d^2)*X^3+8)*
    (C (8*d)*X^6+C (d^2+12*d)*X^3-8)
  have h8 : (8 : F) ≠ 0 := by
    have he : (8 : F) = 2^3 := by ring
    rw [he]
    exact pow_ne_zero _ h₂
  have hn (q : F[X]) (he : q.eval 0 ≠ 0) : q ≠ 0 := by intro hz; simp [hz] at he
  have hp : p ≠ 0 := by
    dsimp [p]
    apply mul_ne_zero
    · apply mul_ne_zero
      · apply mul_ne_zero
        · exact mul_ne_zero X_ne_zero (hn _ (by simpa using h₂))
        · exact hn _ (by simpa using neg_ne_zero.mpr h₂)
      · exact hn _ (by simpa using h8)
    · exact hn _ (by simpa using neg_ne_zero.mpr h8)
  have hd : p.natDegree ≤ 16 := by dsimp [p]; compute_degree!
  obtain ⟨s,hs⟩ : ∃ s : F, p.eval s ≠ 0 := by
    by_contra he
    push_neg at he
    have hb := Polynomial.card_le_degree_of_subset_roots (p := p) (Z := Finset.univ)
      (fun s _ => (Polynomial.mem_roots hp).mpr (he s))
    simp only [Finset.card_univ] at hb
    omega
  simp only [p, eval_mul, eval_X, eval_add, eval_sub, eval_pow, eval_C, eval_ofNat,
    mul_ne_zero_iff] at hs
  exact ⟨s,⟨hs.1.1.1.1,hs.1.1.1.2,hs.1.1.2,hs.1.2,hs.2⟩⟩

-- Cubic multiplication and the matrix identity, before applying the norm.
def factor (θ : E) (d s : F) : E :=
  algebraMap F E (k₀ d s)+algebraMap F E (k₁ d s)*θ+algebraMap F E (k₂ d s)*θ^2

lemma reduced_product {θ : E} {d : F} (hc : θ^3=algebraMap F E d)
    (a b c u v w : E) :
    (a+b*θ+c*θ^2)*(u+v*θ+w*θ^2) =
      (a*u+algebraMap F E d*b*w+algebraMap F E d*c*v)+
      (a*v+b*u+algebraMap F E d*c*w)*θ+(a*w+b*v+c*u)*θ^2 := by
  linear_combination (b*w+c*v+c*w*θ)*hc

lemma projection_nilpotent {θ : E} {d s : F} (hc : θ^3=algebraMap F E d)
    (h : Good d s) (A B : F) :
    projection (F := F) θ (nilpotent s*fiber d s A B) =
      factor θ d s*projection (F := F) θ (fiber d s A B) := by
  obtain ⟨h₀,h₁,h₂⟩ := coeffs d s A B h
  have e₀ := congrArg (algebraMap F E) h₀
  have e₁ := congrArg (algebraMap F E) h₁
  have e₂ := congrArg (algebraMap F E) h₂
  simp only [projection,factor,nilpotent,fiber,Matrix.mul_fin_two,
    Matrix.of_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,
    map_sub,map_add,map_mul,map_neg,map_one,map_pow] at e₀ e₁ e₂ ⊢
  rw [reduced_product hc]
  linear_combination e₀+θ*e₁+θ^2*e₂

lemma projection_unipotent {θ : E} {d s : F} (hc : θ^3=algebraMap F E d)
    (h : Good d s) (t A B : F) :
    projection (F := F) θ ((unipotent s t)⁻¹*fiber d s A B) =
      (1+algebraMap F E t*factor θ d s)*projection (F := F) θ (fiber d s A B) := by
  have he := projection_nilpotent hc h A B
  simp only [projection,nilpotent,fiber,unipotent,Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_fin_two,Matrix.mul_fin_two,
    Matrix.of_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,
    map_sub,map_add,map_mul,map_neg,map_one,map_pow] at he ⊢
  linear_combination algebraMap F E t*he

variable [FiniteDimensional F E]

omit [FiniteDimensional F E] in
lemma kummer_not_base {θ : E} {d : F} (hc : θ^3=algebraMap F E d)
    (hd : ∀ a : F, a^3 ≠ d) : ¬ ∃ a : F, algebraMap F E a = θ := by
  rintro ⟨a,ha⟩
  apply hd a
  apply (algebraMap F E).injective
  simpa only [map_pow,ha] using hc

lemma factor_not_base (hdegree : Module.finrank F E=3) {θ : E} {d s : F}
    (hc : θ^3=algebraMap F E d) (hd : ∀ a : F, a^3 ≠ d) (h : Good d s) :
    ∀ a : F, factor θ d s ≠ algebraMap F E a := by
  intro a he
  have he' : algebraMap F E (k₂ d s)*θ^2+algebraMap F E (k₁ d s)*θ+
      algebraMap F E (k₀ d s-a)=0 := by
    simp only [map_sub]
    dsimp [factor] at he
    linear_combination he
  have hz := Erdos714CubicEmbedding.quadratic_coefficients_zero hdegree
    (kummer_not_base hc hd) _ _ _ he'
  exact k₂_ne_zero h hz.1

lemma row_factor_ne_zero (hdegree : Module.finrank F E=3) {θ : E} {d s : F}
    (hc : θ^3=algebraMap F E d) (hd : ∀ a : F, a^3 ≠ d) (h : Good d s) (t : F) :
    1+algebraMap F E t*factor θ d s ≠ 0 := by
  intro he
  by_cases ht : t=0
  · simp [ht] at he
  have ht' : algebraMap F E t ≠ 0 := by simpa using (algebraMap F E).injective.ne ht
  apply factor_not_base hdegree hc hd h (-1/t)
  simp only [map_div₀,map_neg,map_one]
  apply (eq_div_iff ht').mpr
  linear_combination he

abbrev Conic (d s : F) := {p : F × F // ca d s*p.1^2+cb d s*p.1*p.2+cc d s*p.2^2=1}

def conicMatrix (d s : F) (p : Conic d s) : SL(2,F) :=
  ⟨fiber d s p.val.1 p.val.2, by rw [fiber_det]; exact p.property⟩

lemma conicMatrix_injective (d s : F) : Function.Injective (conicMatrix d s) := by
  intro p q he
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun M : SL(2,F) => M 0 0) he
  · exact congrArg (fun M : SL(2,F) => M 0 1) he

lemma conic_projection_ne_zero (hdegree : Module.finrank F E=3) {θ : E} {d s : F}
    (hc : θ^3=algebraMap F E d) (hd : ∀ a : F, a^3 ≠ d) (h : Good d s)
    (p : Conic d s) : projection (F := F) θ (conicMatrix d s p) ≠ 0 := by
  intro he
  let A := p.val.1
  let B := p.val.2
  let C := (cw s-cb d s)*A-cc d s*B
  let D := ca d s*A+cw s*B
  have he' : algebraMap F E C*θ^2+algebraMap F E B*θ+algebraMap F E (A-D)=0 := by
    change algebraMap F E (A-D)+algebraMap F E B*θ+algebraMap F E C*θ^2=0 at he
    linear_combination he
  obtain ⟨hC,hB,hAD⟩ := Erdos714CubicEmbedding.quadratic_coefficients_zero hdegree
    (kummer_not_base hc hd) _ _ _ he'
  have he₁ : s*B+D=k₀ d s*B+k₁ d s*(A-D)+d*k₂ d s*C := (coeffs d s A B h).2.1
  rw [hB,hAD,hC] at he₁
  have hD : D=0 := by simpa using he₁
  have hA : A=0 := by linear_combination hAD+hD
  have hp : ca d s*A^2+cb d s*A*B+cc d s*B^2=1 := p.property
  simp [hA,hB] at hp

/-- The rank-drop conic gives a complete bipartite copy, with all nonzero norm
weights and both injections checked. -/
def gridCopy (hdegree : Module.finrank F E=3) (θ : E) (d s : F)
    (hc : θ^3=algebraMap F E d) (hd : ∀ a : F, a^3 ≠ d) (h : Good d s) :
    Copy (completeBipartiteGraph F (Conic d s)) (graph (F := F) θ) := by
  let L : F ↪ Vertex F :=
    ⟨fun t => (unipotent s t, Units.mk0 _ (Algebra.norm_ne_zero_iff.mpr
      (row_factor_ne_zero hdegree hc hd h t))), by
      intro t u he
      exact unipotent_injective s (congrArg Prod.fst he)⟩
  let R : Conic d s ↪ Vertex F :=
    ⟨fun p => (conicMatrix d s p, Units.mk0 _ (Algebra.norm_ne_zero_iff.mpr
      (conic_projection_ne_zero hdegree hc hd h p))), by
      intro p q he
      exact conicMatrix_injective d s (congrArg Prod.fst he)⟩
  have he (t : F) (p : Conic d s) : (graph (F := F) θ).Adj (.inl (L t)) (.inr (R p)) := by
    change Algebra.norm F (projection (F := F) θ ((unipotent s t)⁻¹*conicMatrix d s p)) =
      Algebra.norm F (1+algebraMap F E t*factor θ d s)*
        Algebra.norm F (projection (F := F) θ (conicMatrix d s p))
    change Algebra.norm F (projection (F := F) θ ((unipotent s t)⁻¹*fiber d s p.val.1 p.val.2)) = _
    rw [projection_unipotent hc h, map_mul]
    rfl
  refine ⟨⟨L.sumMap R, ?_⟩, (L.sumMap R).injective⟩
  intro x y hh
  cases x with
  | inl t =>
    cases y with
    | inl u => simp at hh
    | inr p => exact he t p
  | inr p =>
    cases y with
    | inr q => simp at hh
    | inl t => exact he t p

variable [Fintype F]

/-- For every noncube Kummer parameter over an odd finite field of order >16,
the proposed cubic projection graph contains K₄,₄. -/
theorem not_free (hdegree : Module.finrank F E=3) (h₂ : (2 : F) ≠ 0)
    (θ : E) (d : F) (hc : θ^3=algebraMap F E d) (hd : ∀ a : F, a^3 ≠ d)
    (hq : 16 < Fintype.card F) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph (F := F) θ) := by
  obtain ⟨s,hs⟩ := exists_good h₂ d hq
  have hd' : d+1 ≠ 0 := by
    intro hz
    apply hd (-1)
    linear_combination -hz
  have hb := Erdos714BinaryConic.quadratic_level_card h₂ (ca d s) (cb d s) (cc d s)
    (leading_ne_zero hd' hs) (discriminant_ne_zero hd' hs)
  have hcard : 4 ≤ Fintype.card (Conic d s) := by dsimp [Conic]; omega
  let e : Fin 4 ↪ F := (Fin.castLEEmb (by omega : 4 ≤ Fintype.card F)).trans
    (Fintype.equivFin F).symm.toEmbedding
  let f : Fin 4 ↪ Conic d s := (Fin.castLEEmb hcard).trans
    (Fintype.equivFin (Conic d s)).symm.toEmbedding
  let small : Copy (completeBipartiteGraph (Fin 4) (Fin 4))
      (completeBipartiteGraph F (Conic d s)) :=
    ⟨⟨e.sumMap f, by intro x y hh; cases x <;> cases y <;> simp_all⟩,
      (e.sumMap f).injective⟩
  intro hf
  exact hf ⟨(gridCopy hdegree θ d s hc hd hs).comp small⟩

end Erdos714SL2Kummer
#print axioms Erdos714SL2Kummer.exists_good
#print axioms Erdos714SL2Kummer.gridCopy
#print axioms Erdos714SL2Kummer.not_free
