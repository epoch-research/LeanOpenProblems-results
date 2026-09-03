import Submission.WeightedTagShift
import Submission.QuadraticProfileThinning

/-!
Affine dependence on a quadratic-field row point is incompatible with
critical-density K44-free thinning. Coefficients may depend arbitrarily on
the row tag and the whole column. No bounded-degree assumption is made on
those parameters. This is an obstruction, not a resolution of Erdős 714.
-/

noncomputable section
open Classical Finset SimpleGraph
set_option maxHeartbeats 3000000
namespace Erdos714WeightedAffineNorm
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Fintype F] [Fintype E]

/-- The actual finite-field norm is quadratic along every affine scalar line,
including in characteristic two. -/
lemma norm_affine (hE : Fintype.card E=Fintype.card F^2) (u v : E) (t : F) :
    Algebra.norm F (u+t • v) = Algebra.norm F u +
      (Algebra.norm F (u+v)-Algebra.norm F u-Algebra.norm F v)*t +
      Algebra.norm F v*t^2 := by
  let σ := FiniteField.frobeniusAlgHom F E
  have hn (z : E) : algebraMap F E (Algebra.norm F z)=z*σ z := by
    rw [Erdos714TranslatedNorm.quadratic_norm_power hE,pow_succ]
    change z^Fintype.card F*z=z*z^Fintype.card F
    ring
  apply (algebraMap F E).injective
  simp only [map_add,map_mul,map_sub,map_pow,hn,Algebra.smul_def,AlgHom.commutes]
  ring

variable {C U : Type*} [Fintype C] [Fintype U]

/-- The multiplicative weight is recovered as the code symbol. -/
def code (L : U → C → E →ₗ[F] E) (d : U → C → E) (b : C → Fˣ)
    (c : C) (i : U × E) : F := Algebra.norm F (L i.1 c i.2+d i.1 c)/(b c : F)

def graph (L : U → C → E →ₗ[F] E) (d : U → C → E) (b : C → Fˣ) :
    SimpleGraph (C ⊕ ((U × E) × F)) := Erdos714Coding.graph (code L d b)

omit [Fintype F] [Fintype C] in
@[simp] lemma cross_adj (L : U → C → E →ₗ[F] E) (d : U → C → E) (b : C → Fˣ)
    (c : C) (u : U) (x : E) (a : F) :
    (graph L d b).Adj (.inl c) (.inr ((u,x),a)) ↔
      Algebra.norm F (L u c x+d u c)=a*(b c : F) := by
  simp only [graph,Erdos714Coding.graph,Erdos714Packing.incidence,
    Erdos714Coding.mem_symbols,code]
  exact div_eq_iff (b c).ne_zero

/-- No invertibility hypothesis on the affine linear maps is needed for counts. -/
theorem edge_count (L : U → C → E →ₗ[F] E) (d : U → C → E) (b : C → Fˣ) :
    (graph L d b).edgeFinset.card=Fintype.card C*Fintype.card U*Fintype.card E := by
  rw [graph,Erdos714Coding.edge_count,Fintype.card_prod,mul_assoc]

omit [Fintype C] in
def coordinateEquiv (coord : (F × F) ≃ₗ[F] E) : ((U × F) × F) ≃ (U × E) :=
  (Equiv.prodAssoc U F F).trans ((Equiv.refl U).prodCongr coord.toEquiv)

omit [Fintype C] [Fintype F] [Fintype E] [Fintype U] in
lemma coordinate_apply (coord : (F × F) ≃ₗ[F] E) (u : U) (z t : F) :
    coordinateEquiv (U := U) coord ((u,z),t)=(u,coord (z,t)) := rfl

omit [Fintype C] [Fintype U] [Fintype F] [Fintype E] in
lemma coordinate_line (coord : (F × F) ≃ₗ[F] E) (z t : F) :
    coord (z,t)=coord (z,0)+t • coord (0,1) := by
  rw [←map_smul,←map_add]
  congr 1
  simp

/-- Every arbitrary selected subgraph of this actual norm host obeys a
subcritical fourth-power bound. Column data can be completely nonlinear. -/
theorem fourth_power (hE : Fintype.card E=Fintype.card F^2)
    (L : U → C → E →ₗ[F] E) (d : U → C → E) (b : C → Fˣ)
    (hU : Fintype.card U ≤ Fintype.card F) (hC : Fintype.card C ≤ Fintype.card F^4)
    (H : SimpleGraph (C ⊕ ((U × E) × F))) (hH : H ≤ graph L d b)
    (hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H) :
    H.edgeFinset.card^4 ≤ 165888*Fintype.card F^27 := by
  have hd : Module.finrank F E=2 := by
    apply Nat.pow_right_injective (a := Fintype.card F) Fintype.one_lt_card
    change Fintype.card F^Module.finrank F E=Fintype.card F^2
    rw [← Module.card_eq_pow_finrank,hE]
  let coord : (F × F) ≃ₗ[F] E := LinearEquiv.ofFinrankEq _ _ (by
    simp only [Module.finrank_prod,Module.finrank_self,hd])
  let e := Equiv.sumCongr (Equiv.refl C)
    ((coordinateEquiv (U := U) coord).prodCongr (Equiv.refl F))
  let H' := H.comap e
  let f (c : C) (i : (U × F) × F) := code L d b c (coordinateEquiv coord i)
  have hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H' :=
    Erdos714GraphAveraging.free_comap _ H e.toEmbedding hf
  have hhost : H' ≤ Erdos714Coding.graph f := by
    intro v w hvw
    have h := hH hvw
    cases v with
    | inl c =>
      cases w with
      | inl c' => exact False.elim h
      | inr p =>
        change p ∈ Erdos714Coding.symbols f c
        apply (Erdos714Coding.mem_symbols f c p.1 p.2).mpr
        exact (Erdos714Coding.mem_symbols (code L d b) c (coordinateEquiv coord p.1) p.2).mp h
    | inr p =>
      cases w with
      | inr p' => exact False.elim h
      | inl c =>
        change p ∈ Erdos714Coding.symbols f c
        apply (Erdos714Coding.mem_symbols f c p.1 p.2).mpr
        exact (Erdos714Coding.mem_symbols (code L d b) c (coordinateEquiv coord p.1) p.2).mp h
  let base (i : U × F) (c : C) := L i.1 c (coord (i.2,0))+d i.1 c
  let slope (i : U × F) (c : C) := L i.1 c (coord (0,1))
  have hpoly (c : C) (i : U × F) (t : F) :
      f c (i,t) = Algebra.norm F (base i c)/(b c : F) +
        ((Algebra.norm F (base i c+slope i c)-Algebra.norm F (base i c)-
          Algebra.norm F (slope i c))/(b c : F))*t +
        (Algebra.norm F (slope i c)/(b c : F))*t^2 := by
    change Algebra.norm F (L i.1 c (coord (i.2,t))+d i.1 c)/(b c : F)=_
    rw [coordinate_line coord,(L i.1 c).map_add,(L i.1 c).map_smul]
    rw [show L i.1 c (coord (i.2,0))+t • L i.1 c (coord (0,1))+d i.1 c =
      base i c+t • slope i c by dsimp [base,slope]; abel]
    rw [norm_affine hE]
    ring
  have hX : Fintype.card (U × F) ≤ Fintype.card F^2 := by
    rw [Fintype.card_prod,pow_two]
    exact Nat.mul_le_mul_right _ hU
  have h := Erdos714QuadraticProfileThinning.fourth_power_bound f
    (fun i c => Algebra.norm F (base i c)/(b c : F))
    (fun i c => (Algebra.norm F (base i c+slope i c)-Algebra.norm F (base i c)-
      Algebra.norm F (slope i c))/(b c : F))
    (fun i c => Algebra.norm F (slope i c)/(b c : F)) hpoly H' hhost hfree hX hC
  let iso : H' ≃g H := ⟨e,Iff.rfl⟩
  rw [iso.card_edgeFinset_eq] at h
  exact h

/-- The general affine-data model has the exact critical host size. -/
theorem host_size (hE : Fintype.card E=Fintype.card F^2)
    (L : U → C → E →ₗ[F] E) (d : U → C → E) (b : C → Fˣ)
    (hU : Fintype.card U=Fintype.card F) (hC : Fintype.card C=Fintype.card F^4) :
    Fintype.card (C ⊕ ((U × E) × F))=2*Fintype.card F^4 ∧
    (graph L d b).edgeFinset.card=Fintype.card F^7 := by
  constructor
  · simp only [Fintype.card_sum,Fintype.card_prod,hU,hC,hE]
    ring
  · rw [edge_count,hU,hC,hE]
    ring

/-- No bounded critical edge budget survives unbounded field order. -/
theorem size_budget (hE : Fintype.card E=Fintype.card F^2)
    (L : U → C → E →ₗ[F] E) (d : U → C → E) (b : C → Fˣ)
    (hU : Fintype.card U ≤ Fintype.card F) (hC : Fintype.card C ≤ Fintype.card F^4)
    (H : SimpleGraph (C ⊕ ((U × E) × F))) (hH : H ≤ graph L d b)
    (hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H)
    (K : ℕ) (hdense : Fintype.card F^7 ≤ K*H.edgeFinset.card) :
    Fintype.card F ≤ 165888*K^4 := by
  have he := fourth_power hE L d b hU hC H hH hf
  have h : Fintype.card F^27*Fintype.card F ≤ Fintype.card F^27*(165888*K^4) := by
    calc
      _ = (Fintype.card F^7)^4 := by ring
      _ ≤ (K*H.edgeFinset.card)^4 := Nat.pow_le_pow_left hdense 4
      _ = K^4*H.edgeFinset.card^4 := by ring
      _ ≤ K^4*(165888*Fintype.card F^27) := Nat.mul_le_mul_left _ he
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_left h (pow_pos Fintype.card_pos 27)

#print axioms norm_affine
#print axioms cross_adj
#print axioms edge_count
#print axioms coordinateEquiv
#print axioms coordinate_line
#print axioms fourth_power
#print axioms host_size
#print axioms size_budget
end Erdos714WeightedAffineNorm
