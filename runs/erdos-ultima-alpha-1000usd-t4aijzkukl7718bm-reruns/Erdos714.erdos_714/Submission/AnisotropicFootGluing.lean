import Submission.AffineLineReplacement

/-! Anisotropic orthogonal origins do not in general make local polarity
replacements globally free. The characteristic-three certificate transfers
through actual field embeddings. This does not settle Erdős 714. -/
noncomputable section
open Classical SimpleGraph
set_option maxHeartbeats 2000000
namespace Erdos714AnisotropicFoot
open Erdos714AffineLineReplacement

variable {E : Type*} [Field E]

def footShift (D m b : E) : E := D*m*b/(D*m*m-1)

lemma denominator_ne_zero (D : E) (hD : ¬IsSquare D) (m : E) : D*m*m-1 ≠ 0 := by
  intro h
  have he : D*m*m=1 := sub_eq_zero.mp h
  have hm : m ≠ 0 := by intro h; simp [h] at he
  apply hD
  refine ⟨m⁻¹,?_⟩
  apply (mul_right_cancel₀ (pow_ne_zero 2 hm))
  calc
    D*m^2 = 1 := by simpa only [pow_two,mul_assoc] using he
    _ = (m⁻¹*m⁻¹)*m^2 := by field_simp

/-- The chosen local origin is orthogonal to the direction (1,m) for
Q(x,y)=x²-Dy². -/
theorem foot_orthogonal (D : E) (hD : ¬IsSquare D) (m b : E) :
    -(footShift D m b)-D*(b-m*footShift D m b)*m=0 := by
  have h : footShift D m b*(D*m*m-1)=D*m*b :=
    div_mul_cancel₀ _ (denominator_ne_zero D hD m)
  linear_combination h

/-- Translation to that origin removes the mixed term of the quadratic form. -/
theorem foot_quadratic (D : E) (hD : ¬IsSquare D) (m b t : E) :
    (t-footShift D m b)^2-D*(m*(t-footShift D m b)+b)^2 =
      (footShift D m b)^2-D*(b-m*footShift D m b)^2+(1-D*m^2)*t^2 := by
  have h := foot_orthogonal D hD m b
  linear_combination 2*t*h

variable [Fintype E]

/-- The original line-replacement graph expressed without a search over lines. -/
lemma replacement_adj_iff (C : E → E → E) (R : E → E → Prop) (P Q : E × E) :
    (graph C R).Adj (.inl P) (.inr Q) ↔
      P.1 ≠ Q.1 ∧
        let m := (Q.2-P.2)/(Q.1-P.1)
        let b := P.2-m*P.1
        R (P.1+C m b) (Q.1+C m b) := by
  by_cases hx : P.1=Q.1
  · simp only [hx,ne_eq,not_true_eq_false,false_and,iff_false]
    intro he
    change Q ∈ Finset.univ.filter (fun y => (P,y) ∈ Set.range (pair C R)) at he
    obtain ⟨⟨m,b,⟨⟨s,t⟩,hst,hR⟩⟩,hh⟩ := (Finset.mem_filter.mp he).2
    have h₁ := congrArg (fun z : (E×E)×(E×E) => z.1.1) hh
    have h₂ := congrArg (fun z : (E×E)×(E×E) => z.2.1) hh
    exact hst (sub_left_injective (h₁.trans (hx.trans h₂.symm)))
  · let m := (Q.2-P.2)/(Q.1-P.1)
    let b := P.2-m*P.1
    have hp : point C m b (P.1+C m b)=P := by ext <;> simp [point,b]
    have hq : point C m b (Q.1+C m b)=Q := by
      apply Prod.ext
      · simp [point]
      · change m*((Q.1+C m b)-C m b)+b=Q.2
        simp only [add_sub_cancel_right]
        dsimp [b,m]
        field_simp [sub_ne_zero.mpr (Ne.symm hx)]
        ring
    rw [←hp,←hq,on_line_iff]
    simpa only [hp,hq,add_left_inj] using
      (show (P.1+C m b ≠ Q.1+C m b ∧ R (P.1+C m b) (Q.1+C m b)) ↔
        P.1 ≠ Q.1 ∧ R (P.1+C m b) (Q.1+C m b) from by simp)

section Coordinates
variable (F : Type*) [Field F]
abbrev Ext := QuadraticAlgebra F (-1) 0

def parameter : Ext F := ⟨-1,1⟩

def pointRelation [Fact (∀ r : F, r^2 ≠ -1+(0:F)*r)] (P Q : Ext F × Ext F) : Prop :=
  P.1 ≠ Q.1 ∧
    let m := (Q.2-P.2)/(Q.1-P.1)
    let b := P.2-m*P.1
    let s := P.1+footShift (parameter F) m b
    let t := Q.1+footShift (parameter F) m b
    s.re+t.re=s.im*t.im

def footGraph [Fact (∀ r : F, r^2 ≠ -1+(0:F)*r)] :
    SimpleGraph ((Ext F × Ext F) ⊕ (Ext F × Ext F)) where
  Adj x y := match x,y with
    | .inl P,.inr Q => pointRelation F P Q
    | .inr Q,.inl P => pointRelation F P Q
    | _,_ => False
  symm := by intro x y; cases x <;> cases y <;> exact id
  loopless := by intro x; cases x <;> exact not_false

instance [Fintype F] : Fintype (Ext F) :=
  Fintype.ofEquiv (F×F) (QuadraticAlgebra.equivProd (-1:F) 0).symm

lemma footGraph_eq [Fintype F] [Fact (∀ r : F, r^2 ≠ -1+(0:F)*r)] :
    footGraph F=graph (footShift (parameter F)) (polarity (QuadraticAlgebra.equivProd (-1:F) 0)) := by
  ext x y
  cases x with
  | inl P =>
    cases y with
    | inl Q => rfl
    | inr Q => exact (replacement_adj_iff (footShift (parameter F))
        (polarity (QuadraticAlgebra.equivProd (-1:F) 0)) P Q).symm
  | inr Q =>
    cases y with
    | inr P => rfl
    | inl P => exact (replacement_adj_iff (footShift (parameter F))
        (polarity (QuadraticAlgebra.equivProd (-1:F) 0)) P Q).symm

/-- The exact number of edges remains at the desired fourth-case scale. -/
theorem foot_edge_count [Fintype F] [Fact (∀ r : F, r^2 ≠ -1+(0:F)*r)] (h2 : (2:F) ≠ 0) :
    (footGraph F).edgeFinset.card=Fintype.card F^7-Fintype.card F^5 := by
  rw [footGraph_eq]
  exact polarity_edge_count _ _ h2

section Transfer
variable {F G : Type*} [Field F] [Field G]

def coordMap (f : F →+* G) : Ext F →+* Ext G where
  toFun x := ⟨f x.re,f x.im⟩
  map_zero' := by ext <;> simp
  map_one' := by ext <;> simp [QuadraticAlgebra.re_one,QuadraticAlgebra.im_one]
  map_add' x y := by ext <;> simp
  map_mul' x y := by
    ext <;> simp [QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul]

@[simp] lemma coordMap_re (f : F →+* G) (x : Ext F) : (coordMap f x).re=f x.re := rfl
@[simp] lemma coordMap_im (f : F →+* G) (x : Ext F) : (coordMap f x).im=f x.im := rfl
@[simp] lemma coordMap_parameter (f : F →+* G) : coordMap f (parameter F)=parameter G := by
  ext <;> simp [parameter]

variable [Fact (∀ r : F, r^2 ≠ -1+(0:F)*r)] [Fact (∀ r : G, r^2 ≠ -1+(0:G)*r)]

lemma map_footShift (f : F →+* G) (D m b : Ext F) :
    coordMap f (footShift D m b)=footShift (coordMap f D) (coordMap f m) (coordMap f b) := by
  simp only [footShift,map_div₀,map_mul,map_sub,map_one]

def pointMap (f : F →+* G) : Ext F × Ext F → Ext G × Ext G :=
  Prod.map (coordMap f) (coordMap f)

omit [Fact (∀ r : G, r^2 ≠ -1+(0:G)*r)] in
lemma pointMap_injective (f : F →+* G) : Function.Injective (pointMap f) :=
  Prod.map_injective.mpr ⟨(coordMap f).injective,(coordMap f).injective⟩

lemma pointRelation_map (f : F →+* G) {P Q : Ext F × Ext F}
    (h : pointRelation F P Q) : pointRelation G (pointMap f P) (pointMap f Q) := by
  obtain ⟨hx,h⟩ := h
  constructor
  · exact (coordMap f).injective.ne hx
  · dsimp only [pointRelation,pointMap,Prod.map_fst,Prod.map_snd] at *
    simp only [←coordMap_parameter f,←map_sub,←map_div₀,←map_mul,
      ←map_footShift,←map_add,coordMap_re,coordMap_im]
    simpa only [map_add,map_mul] using congrArg f h

end Transfer

end Coordinates

section Certificate
abbrev K := ZMod 3
instance : Fact (Nat.Prime 3) := ⟨by decide⟩
instance : Fact (∀ r : K, r^2 ≠ -1+(0:K)*r) := ⟨by decide⟩

/-- All coordinates lie in the actual quadratic field over F3. -/
def rows : Fin 4 → Ext K × Ext K :=
  ![(⟨0,0⟩,0),(⟨1,0⟩,0),(⟨1,2⟩,0),(⟨1,1⟩,0)]
def columns : Fin 4 → Ext K × Ext K :=
  ![(⟨0,1⟩,⟨2,0⟩),(⟨0,1⟩,⟨1,0⟩),(⟨0,2⟩,⟨2,1⟩),(⟨0,2⟩,⟨1,2⟩)]

lemma rows_injective : Function.Injective rows := by decide
lemma columns_injective : Function.Injective columns := by decide
lemma certificate_edges (i j : Fin 4) : pointRelation K (rows i) (columns j) := by
  fin_cases i <;> fin_cases j <;> unfold pointRelation <;> dsimp only <;> decide

variable (F : Type*) [Field F] [CharP F 3] [Fact (∀ r : F, r^2 ≠ -1+(0:F)*r)]

def characteristicThreeCopy :
    Copy (completeBipartiteGraph (Fin 4) (Fin 4)) (footGraph F) := by
  let f : K →+* F := ZMod.castHom (dvd_refl 3) F
  let l : Fin 4 ↪ Ext F × Ext F :=
    ⟨pointMap f ∘ rows,(pointMap_injective f).comp rows_injective⟩
  let r : Fin 4 ↪ Ext F × Ext F :=
    ⟨pointMap f ∘ columns,(pointMap_injective f).comp columns_injective⟩
  refine ⟨⟨l.sumMap r,?_⟩,(l.sumMap r).injective⟩
  intro x y hxy
  cases x with
  | inl i =>
    cases y with
    | inl j => simp at hxy
    | inr j => exact pointRelation_map f (certificate_edges i j)
  | inr j =>
    cases y with
    | inr i => simp at hxy
    | inl i => exact pointRelation_map f (certificate_edges i j)

theorem characteristicThree_not_free :
    ¬(completeBipartiteGraph (Fin 4) (Fin 4)).Free (footGraph F) := by
  intro h
  exact h ⟨characteristicThreeCopy F⟩

omit [Fact (∀ r : F, r^2 ≠ -1+(0:F)*r)] in
lemma parameter_norm : QuadraticAlgebra.norm (parameter F)=(-1:F) := by
  have h3 : (3:F)=0 := CharP.cast_eq_zero F 3
  change (-1)*(-1)+0*(-1)*1-(-1)*1*1=(-1:F)
  linear_combination h3

lemma parameter_nonsquare : ¬IsSquare (parameter F) := by
  rintro ⟨t,ht⟩
  have h := congrArg QuadraticAlgebra.norm ht
  rw [map_mul,parameter_norm F] at h
  apply (Fact.out : ∀ r : F, r^2 ≠ -1+(0:F)*r) (QuadraticAlgebra.norm t)
  simpa only [pow_two,zero_mul,add_zero] using h.symm

end Certificate
instance oddGalois_rootless (k : ℕ) :
    Fact (∀ r : GaloisField 3 (2*k+1), r^2 ≠ -1+(0:GaloisField 3 (2*k+1))*r) := by
  letI : Fintype (GaloisField 3 (2*k+1)) := Fintype.ofFinite _
  have hn : ¬IsSquare (-1:GaloisField 3 (2*k+1)) := by
    rw [FiniteField.isSquare_neg_one_iff,Fintype.card_eq_nat_card,
      GaloisField.card 3 (2*k+1) (by omega),pow_add,pow_mul]
    norm_num [Nat.mul_mod,Nat.pow_mod]
  refine ⟨fun r hr => hn ⟨r,?_⟩⟩
  simpa only [zero_mul,add_zero,pow_two] using hr.symm

theorem oddGalois_not_free (k : ℕ) :
    ¬(completeBipartiteGraph (Fin 4) (Fin 4)).Free (footGraph (GaloisField 3 (2*k+1))) :=
  characteristicThree_not_free _

section Scaling
variable {F : Type*} [Field F] [Fintype F]
  [Fact (∀ r : F, r^2 ≠ -1+(0:F)*r)]

def vertical (c : Ext F) (P : Ext F × Ext F) : Ext F × Ext F := (P.1,c*P.2)

omit [Fintype F] in
lemma vertical_injective {c : Ext F} (hc : c ≠ 0) : Function.Injective (vertical c) := by
  intro P Q he
  change (P.1,c*P.2)=(Q.1,c*Q.2) at he
  have h₁ := congrArg (fun z : Ext F × Ext F => z.1) he
  have h₂ := congrArg (fun z : Ext F × Ext F => z.2) he
  exact Prod.ext h₁ (mul_left_cancel₀ hc h₂)

omit [Fintype F] in
lemma footShift_scale (D c m b : Ext F) :
    footShift D (c*m) (c*b)=footShift (D*c^2) m b := by
  unfold footShift
  congr 1 <;> ring

lemma vertical_adj {D₀ D c : Ext F} (hD : D*c^2=D₀) (P Q : Ext F × Ext F)
    (h : (graph (footShift D₀) (polarity (QuadraticAlgebra.equivProd (-1:F) 0))).Adj
      (.inl P) (.inr Q)) :
    (graph (footShift D) (polarity (QuadraticAlgebra.equivProd (-1:F) 0))).Adj
      (.inl (vertical c P)) (.inr (vertical c Q)) := by
  rw [replacement_adj_iff] at h ⊢
  refine ⟨h.1,?_⟩
  dsimp only [vertical]
  have hm : (c*Q.2-c*P.2)/(Q.1-P.1)=c*((Q.2-P.2)/(Q.1-P.1)) := by ring
  rw [hm]
  have hb : c*P.2-c*((Q.2-P.2)/(Q.1-P.1))*P.1=
      c*(P.2-((Q.2-P.2)/(Q.1-P.1))*P.1) := by ring
  rw [hb,footShift_scale,hD]
  exact h.2

/-- Scaling the vertical coordinate transports all incidences, not only the
particular finite certificate. -/
def verticalCopy (D₀ D c : Ext F) (hc : c ≠ 0) (hD : D*c^2=D₀) :
    Copy (graph (footShift D₀) (polarity (QuadraticAlgebra.equivProd (-1:F) 0)))
      (graph (footShift D) (polarity (QuadraticAlgebra.equivProd (-1:F) 0))) := by
  let e : (Ext F × Ext F) ↪ (Ext F × Ext F) := ⟨vertical c,vertical_injective hc⟩
  refine ⟨⟨e.sumMap e,?_⟩,(e.sumMap e).injective⟩
  intro x y hxy
  cases x with
  | inl P =>
    cases y with
    | inl Q => exact False.elim hxy
    | inr Q => exact vertical_adj hD P Q hxy
  | inr Q =>
    cases y with
    | inr P => exact False.elim hxy
    | inl P => exact vertical_adj hD P Q hxy

end Scaling

/-- Two nonsquares in a finite field differ by a nonzero square factor. -/
lemma nonsquare_scaling {L : Type*} [Field L] [Fintype L] (D₀ D : L)
    (h₀ : ¬IsSquare D₀) (hD : ¬IsSquare D) : ∃ c : L, c ≠ 0 ∧ D*c^2=D₀ := by
  have hn₀ : D₀ ≠ 0 := fun he => h₀ (he.symm ▸ IsSquare.zero)
  have hnD : D ≠ 0 := fun he => hD (he.symm ▸ IsSquare.zero)
  have hs : IsSquare (D*D₀) := by
    apply (quadraticChar_one_iff_isSquare (mul_ne_zero hnD hn₀)).mp
    rw [map_mul,quadraticChar_neg_one_iff_not_isSquare.mpr hD,
      quadraticChar_neg_one_iff_not_isSquare.mpr h₀]
    norm_num
  obtain ⟨t,ht⟩ := hs
  have htn : t ≠ 0 := by intro he; rw [he,mul_zero] at ht; exact mul_ne_zero hnD hn₀ ht
  refine ⟨t/D,div_ne_zero htn hnD,?_⟩
  field_simp [hnD]
  linear_combination -ht

/-- No choice of anisotropic direction parameter repairs this particular
orthogonal-origin construction in characteristic three. -/
theorem all_parameters_not_free (F : Type*) [Field F] [Fintype F] [CharP F 3]
    [Fact (∀ r : F, r^2 ≠ -1+(0:F)*r)] (D : Ext F) (hD : ¬IsSquare D) :
    ¬(completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (graph (footShift D) (polarity (QuadraticAlgebra.equivProd (-1:F) 0))) := by
  obtain ⟨c,hc,he⟩ := nonsquare_scaling (parameter F) D (parameter_nonsquare F) hD
  have base : Copy (completeBipartiteGraph (Fin 4) (Fin 4))
      (graph (footShift (parameter F)) (polarity (QuadraticAlgebra.equivProd (-1:F) 0))) := by
    rw [←footGraph_eq F]
    exact characteristicThreeCopy F
  intro hf
  exact hf ⟨(verticalCopy (parameter F) D c hc he).comp base⟩

local instance (k : ℕ) : Fintype (GaloisField 3 (2*k+1)) := Fintype.ofFinite _

theorem oddGalois_all_parameters (k : ℕ) (D : Ext (GaloisField 3 (2*k+1)))
    (hD : ¬IsSquare D) :
    ¬(completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (graph (footShift D)
        (polarity (QuadraticAlgebra.equivProd (-1:GaloisField 3 (2*k+1)) 0))) :=
  all_parameters_not_free _ D hD

end Erdos714AnisotropicFoot
#print axioms Erdos714AnisotropicFoot.foot_quadratic
#print axioms Erdos714AnisotropicFoot.foot_edge_count
#print axioms Erdos714AnisotropicFoot.certificate_edges

#print axioms Erdos714AnisotropicFoot.characteristicThree_not_free
#print axioms Erdos714AnisotropicFoot.parameter_nonsquare

#print axioms Erdos714AnisotropicFoot.oddGalois_not_free

#print axioms Erdos714AnisotropicFoot.verticalCopy
#print axioms Erdos714AnisotropicFoot.all_parameters_not_free

#print axioms Erdos714AnisotropicFoot.oddGalois_all_parameters
