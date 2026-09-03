import Submission.AffineFiberThinning
import Submission.QuadraticEvaluationBinary

/-!
Arbitrary K44-free edge selections in the binary quadratic-evaluation host
satisfy a subcritical fourth-power bound. This is a construction obstruction,
not a resolution of Erdős714.
-/
noncomputable section
open Classical Finset SimpleGraph
set_option maxHeartbeats 3000000
namespace Erdos714QuadraticEvaluationThinning
open Erdos714QuadraticEvaluation (Coeff Vertex extensionEval normGraph)
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [CharP F 2] [CharP E 2]

def fiberMap (h m l b : F) : (F × F) →+ F where
  toFun v := (h*v.1+v.2)^2+l*(h*v.1+v.2)+b*(m*v.1+v.2)
  map_zero' := by simp
  map_add' := by intro v w; dsimp; ring_nf; reduce_mod_char!

lemma kernel_card [Fintype F] (h m l b : F) (hb : b ≠ 0) (hm : h+m ≠ 0) :
    (univ.filter (fun v => fiberMap h m l b v=0)).card ≤ Fintype.card F := by
  apply (card_le_card_of_injOn (fun v : F × F => h*v.1+v.2) (t := univ)
    (fun _ _ => mem_univ _) ?_).trans_eq (card_univ)
  intro v hv w hw he
  have hv' := (mem_filter.mp hv).2
  have hw' := (mem_filter.mp hw).2
  change (h*v.1+v.2)^2+l*(h*v.1+v.2)+b*(m*v.1+v.2)=0 at hv'
  change (h*w.1+w.2)^2+l*(h*w.1+w.2)+b*(m*w.1+w.2)=0 at hw'
  have he' : h*v.1+v.2=h*w.1+w.2 := he
  have he2 : m*v.1+v.2=m*w.1+w.2 := by
    apply mul_left_cancel₀ hb
    rw [he'] at hv'
    linear_combination hv'-hw'
  have hvw : v.1=w.1 := by
    apply mul_left_cancel₀ hm
    linear_combination (norm := (ring_nf;reduce_mod_char!)) he'+he2
  exact Prod.ext hvw (by rw [hvw] at he'; exact add_left_cancel he')

omit [CharP F 2] in
/-- Coordinates of the actual extension evaluation in a binary power basis. -/
lemma extensionEval_eq (δ : F) (θ : E) (hθ : θ^2=θ+algebraMap F E δ)
    (p : Coeff F) (t : F) :
    extensionEval θ p t=algebraMap F E (Erdos714QuadraticEvaluation.eval p t+δ*p.1)+
      algebraMap F E (p.1+p.2.1)*θ := by
  dsimp [extensionEval,Erdos714QuadraticEvaluation.eval]
  simp only [map_add,map_mul,map_pow]
  linear_combination (norm := (ring_nf;reduce_mod_char!)) (algebraMap F E p.1)*hθ

def row (s r : F) (v : F × F) : Vertex F := (s,v.1,v.1+r,v.2)

omit [CharP F 2] in
lemma row_injective (s r : F) : Function.Injective (row s r) := by
  intro v w he
  exact Prod.ext (congrArg (fun x : Vertex F => x.2.1) he)
    (congrArg (fun x : Vertex F => x.2.2.2) he)

def beta (s : F) (y : Vertex F) : F := Erdos714QuadraticEvaluation.eval y.2 s

def effectiveBeta (s : F) (y : Vertex F) : F := if beta s y=0 then 1 else beta s y

omit [CharP F 2] in
lemma effectiveBeta_ne_zero (s : F) (y : Vertex F) : effectiveBeta s y ≠ 0 := by
  unfold effectiveBeta
  split_ifs with h <;> simp_all

def layerMap (δ s r : F) (y : Vertex F) : (F × F) →+ F :=
  fiberMap (y.1^2+y.1+δ) (y.1^2+y.1) (r+y.2.1+y.2.2.1) (effectiveBeta s y)

def level (δ s r : F) (y : Vertex F) : F :=
  beta s y*r*y.1+(r*y.1+beta s y+δ*y.2.1)^2+
    (r+y.2.1+y.2.2.1)*(r*y.1+beta s y+δ*y.2.1)+δ*(r+y.2.1+y.2.2.1)^2

lemma layer_kernel_card [Fintype F] (δ s r : F) (hδ : δ ≠ 0) (y : Vertex F) :
    (univ.filter (fun v => layerMap δ s r y v=0)).card ≤ Fintype.card F := by
  apply kernel_card _ _ _ _ (effectiveBeta_ne_zero s y)
  convert hδ using 1
  ring_nf
  reduce_mod_char!

/-- Every genuine norm edge lies in the asserted affine additive fiber. -/
lemma edge_fiber (δ s r : F) (θ : E) (hθ : θ^2=θ+algebraMap F E δ)
    (B : Module.Basis (Fin 2) F E) (hB : ∀ i, B i=θ^(i : ℕ))
    (y : Vertex F) (v : F × F)
    (he : (normGraph θ).Adj (.inl (row s r v)) (.inr y)) :
    layerMap δ s r y v=level δ s r y := by
  have hb : beta s y ≠ 0 := he.2.2.2.1
  have hn := he.2.2.2.2
  change Algebra.norm F (extensionEval θ (row s r v).2 y.1+extensionEval θ y.2 s)=
    Erdos714QuadraticEvaluation.eval (row s r v).2 y.1*beta s y at hn
  rw [extensionEval_eq δ θ hθ,extensionEval_eq δ θ hθ] at hn
  rw [show algebraMap F E (Erdos714QuadraticEvaluation.eval (row s r v).2 y.1+δ*(row s r v).2.1)+
      algebraMap F E ((row s r v).2.1+(row s r v).2.2.1)*θ+
      (algebraMap F E (Erdos714QuadraticEvaluation.eval y.2 s+δ*y.2.1)+
        algebraMap F E (y.2.1+y.2.2.1)*θ)=
      algebraMap F E (Erdos714QuadraticEvaluation.eval (row s r v).2 y.1+δ*(row s r v).2.1+
        Erdos714QuadraticEvaluation.eval y.2 s+δ*y.2.1)+
      algebraMap F E ((row s r v).2.1+(row s r v).2.2.1+y.2.1+y.2.2.1)*θ by
        simp only [map_add]; ring] at hn
  rw [Erdos714QuadraticEvaluationBinary.norm_pair δ θ hθ B hB] at hn
  dsimp [layerMap,fiberMap,level]
  rw [effectiveBeta,if_neg hb]
  dsimp [row,Erdos714QuadraticEvaluation.eval,beta] at *
  linear_combination (norm := (ring_nf;reduce_mod_char!)) hn


variable [Fintype F]

def neighborhoods (H : SimpleGraph (Vertex F ⊕ Vertex F)) (s r : F)
    (y : Vertex F) : Finset (F × F) :=
  univ.filter (fun v => H.Adj (.inl (row s r v)) (.inr y))

def layerCopy (H : SimpleGraph (Vertex F ⊕ Vertex F)) (s r : F) :
    (Erdos714Packing.incidence (neighborhoods H s r)).Copy H where
  toHom := {
    toFun := Sum.elim Sum.inr (fun v => Sum.inl (row s r v))
    map_rel' := by
      intro x y he
      cases x with
      | inl x =>
        cases y with
        | inl y => exact False.elim he
        | inr y => exact ((mem_filter.mp he).2).symm
      | inr x =>
        cases y with
        | inl y => exact (mem_filter.mp he).2
        | inr y => exact False.elim he }
  injective' := by
    intro x y he
    cases x with
    | inl x =>
      cases y with
      | inl y => exact congrArg Sum.inl (Sum.inr.inj he)
      | inr y => exact False.elim (Sum.inr_ne_inl he)
    | inr x =>
      cases y with
      | inl y => exact False.elim (Sum.inl_ne_inr he)
      | inr y => exact congrArg Sum.inr (row_injective s r (Sum.inl.inj he))

/-- A layer has q² rows and q⁴ columns; its selected edge count is subcritical. -/
theorem layer_bound (δ s r : F) (θ : E) (hθ : θ^2=θ+algebraMap F E δ)
    (B : Module.Basis (Fin 2) F E) (hB : ∀ i, B i=θ^(i : ℕ))
    (H : SimpleGraph (Vertex F ⊕ Vertex F)) (hH : H ≤ normGraph θ)
    (hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H) :
    (∑ y, (neighborhoods H s r y).card)^4 ≤ 7*Fintype.card F^19 := by
  have hδ := Erdos714QuadraticEvaluationBinary.parameter_ne_zero δ θ hθ B hB
  apply Erdos714AffineFibers.critical_layer (layerMap δ s r) (level δ s r)
    (Fintype.card F) (layer_kernel_card δ s r hδ)
  · simp [Fintype.card_prod,pow_two]
  · simp only [Vertex,Coeff,Fintype.card_prod]
    exact le_of_eq (by ring)
  · intro y v hv
    exact edge_fiber δ s r θ hθ B hB y v (hH (mem_filter.mp hv).2)
  · rintro ⟨c⟩
    exact hf ⟨(layerCopy H s r).comp c⟩

/-- The row layers form an exact partition, not a covering with multiplicity. -/
def rowEquiv : ((F × F) × (F × F)) ≃ Vertex F where
  toFun p := row p.1.1 p.1.2 p.2
  invFun x := ((x.1,x.2.1+x.2.2.1),(x.2.1,x.2.2.2))
  left_inv := by
    rintro ⟨⟨s,r⟩,⟨a,c⟩⟩
    simp [row,CharTwo.add_self_eq_zero,←add_assoc]
  right_inv := by
    rintro ⟨s,a,b,c⟩
    simp [row,CharTwo.add_self_eq_zero,←add_assoc]

def allNeighborhoods (H : SimpleGraph (Vertex F ⊕ Vertex F)) (y : Vertex F) :
    Finset ((F × F) × (F × F)) :=
  univ.filter (fun p => H.Adj (.inl (rowEquiv p)) (.inr y))

def thinningIso (θ : E) (H : SimpleGraph (Vertex F ⊕ Vertex F))
    (hH : H ≤ normGraph θ) :
    Erdos714Packing.incidence (allNeighborhoods H) ≃g H where
  toEquiv := (Equiv.sumComm _ _).trans (rowEquiv.sumCongr (Equiv.refl _))
  map_rel_iff' := by
    intro x y
    cases x with
    | inl x =>
      cases y with
      | inl y =>
        change H.Adj (.inr x) (.inr y) ↔ False
        exact ⟨fun h => hH h,False.elim⟩
      | inr y =>
        change H.Adj (.inr x) (.inl (rowEquiv y)) ↔ y ∈ allNeighborhoods H x
        simp only [allNeighborhoods,mem_filter,mem_univ,true_and]
        exact H.adj_comm _ _
    | inr x =>
      cases y with
      | inl y =>
        change H.Adj (.inl (rowEquiv x)) (.inr y) ↔ x ∈ allNeighborhoods H y
        simp [allNeighborhoods]
      | inr y =>
        change H.Adj (.inl (rowEquiv x)) (.inl (rowEquiv y)) ↔ False
        exact ⟨fun h => hH h,False.elim⟩

omit [CharP E 2] in
lemma edge_partition (θ : E) (H : SimpleGraph (Vertex F ⊕ Vertex F))
    (hH : H ≤ normGraph θ) :
    H.edgeFinset.card=∑ p : F × F, ∑ y, (neighborhoods H p.1 p.2 y).card := by
  rw [← (thinningIso θ H hH).card_edgeFinset_eq,Erdos714Packing.incidence_edges,sum_comm]
  apply sum_congr rfl
  intro y _
  simp only [allNeighborhoods,card_filter,Fintype.sum_prod_type,neighborhoods,rowEquiv]
  rfl

/-- Arbitrary K44-free edge thinnings lose a quarter power from q⁷. -/
theorem fourth_power (δ : F) (θ : E) (hθ : θ^2=θ+algebraMap F E δ)
    (B : Module.Basis (Fin 2) F E) (hB : ∀ i, B i=θ^(i : ℕ))
    (H : SimpleGraph (Vertex F ⊕ Vertex F)) (hH : H ≤ normGraph θ)
    (hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H) :
    H.edgeFinset.card^4 ≤ 7*Fintype.card F^27 := by
  rw [edge_partition θ H hH]
  calc
    _ ≤ Fintype.card (F × F)^3*∑ p : F × F, (∑ y, (neighborhoods H p.1 p.2 y).card)^4 := by
      simpa using Erdos714EnergyThinning.fourth_moment (univ : Finset (F × F))
        (fun p => ∑ y, (neighborhoods H p.1 p.2 y).card)
    _ ≤ Fintype.card (F × F)^3*∑ _p : F × F, 7*Fintype.card F^19 := by
      exact Nat.mul_le_mul_left _ (sum_le_sum (fun p _ => layer_bound δ p.1 p.2 θ hθ B hB H hH hf))
    _ = _ := by simp [Fintype.card_prod]; ring

/-- A fixed critical edge budget bounds the field order. -/
theorem size_budget (δ : F) (θ : E) (hθ : θ^2=θ+algebraMap F E δ)
    (B : Module.Basis (Fin 2) F E) (hB : ∀ i, B i=θ^(i : ℕ))
    (H : SimpleGraph (Vertex F ⊕ Vertex F)) (hH : H ≤ normGraph θ)
    (hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H)
    (K : ℕ) (hdense : Fintype.card F^7 ≤ K*H.edgeFinset.card) :
    Fintype.card F ≤ 7*K^4 := by
  have he := fourth_power δ θ hθ B hB H hH hf
  have h : Fintype.card F^27*Fintype.card F ≤ Fintype.card F^27*(7*K^4) := by
    calc
      _ = (Fintype.card F^7)^4 := by ring
      _ ≤ (K*H.edgeFinset.card)^4 := Nat.pow_le_pow_left hdense 4
      _ = K^4*H.edgeFinset.card^4 := by ring
      _ ≤ K^4*(7*Fintype.card F^27) := Nat.mul_le_mul_left _ he
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_left h (pow_pos Fintype.card_pos 27)

#print axioms kernel_card
#print axioms edge_fiber
#print axioms layer_bound
#print axioms edge_partition
#print axioms fourth_power
#print axioms size_budget
end Erdos714QuadraticEvaluationThinning
