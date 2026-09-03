import Submission.SmallProfileThinning
import Submission.PolynomialExceptionalDensity

/-! Projective bilinear profiles, with the zero polynomial explicitly excluded.
This supplies a restricted-model thinning bound, not a conjecture solution. -/
noncomputable section
open Classical Finset SimpleGraph MvPolynomial
set_option maxHeartbeats 3000000
namespace Erdos714BilinearProfiles
variable {F : Type*} [Field F]
abbrev Coeff (F : Type*) := Fin 4 → F
abbrev Profile (F : Type*) := Fin 4 × (Fin 3 → F)

def form (v : Coeff F) (x : F × F) : F :=
  v 0+v 1*x.1+v 2*x.2+v 3*x.1*x.2

def exponents : Fin 4 → (Fin 2 →₀ ℕ) :=
  ![0,Finsupp.single 0 1,Finsupp.single 1 1,Finsupp.single 0 1+Finsupp.single 1 1]
lemma exponents_injective : Function.Injective exponents := by
  intro i j h
  have h0 := congrArg (fun v => v 0) h
  have h1 := congrArg (fun v => v 1) h
  fin_cases i <;> fin_cases j <;> simp [exponents] at h0 h1 ⊢

def polynomial (v : Coeff F) : MvPolynomial (Fin 2) F :=
  ∑ i, monomial (exponents i) (v i)
lemma polynomial_coeff (v : Coeff F) (i : Fin 4) :
    coeff (exponents i) (polynomial v)=v i := by
  simp [polynomial,coeff_sum,coeff_monomial,exponents_injective.eq_iff]
lemma polynomial_ne_zero {v : Coeff F} (hv : v ≠ 0) : polynomial v ≠ 0 := by
  intro h
  apply hv
  funext i
  have hi := congrArg (coeff (exponents i)) h
  simpa [polynomial_coeff] using hi

lemma sum_degree_le {I σ : Type*} [Fintype I] (p : I → MvPolynomial σ F) (d : ℕ)
    (h : ∀ i, (p i).totalDegree ≤ d) : (∑ i, p i).totalDegree ≤ d := by
  have hs (s : Finset I) : (∑ i ∈ s, p i).totalDegree ≤ d := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      rw [sum_insert ha]
      exact (totalDegree_add _ _).trans (max_le (h a) ih)
  exact hs univ

lemma polynomial_degree (v : Coeff F) : (polynomial v).totalDegree ≤ 2 := by
  apply sum_degree_le
  intro i
  apply (totalDegree_monomial_le _ _).trans
  fin_cases i <;> simp [exponents,Finsupp.sum_fintype,Fin.sum_univ_two]

lemma polynomial_eval (v : Coeff F) (x : F × F) :
    eval ![x.1,x.2] (polynomial v)=form v x := by
  simp [polynomial,Fin.sum_univ_four,exponents,eval_monomial,
    Finsupp.prod_fintype,Fin.prod_univ_two,form,mul_assoc]

def pairEncoding : (F × F) ↪ (Fin 2 → F) :=
  ⟨fun x => ![x.1,x.2],by
    intro x y h
    exact Prod.ext (congrFun h 0) (congrFun h 1)⟩

variable [Fintype F]
def zeros (v : Coeff F) : Finset (F × F) := univ.filter (fun x => form v x=0)
lemma zeros_bound {v : Coeff F} (hv : v ≠ 0) : (zeros v).card ≤ 2*Fintype.card F := by
  have h := Erdos714PolynomialExceptionalDensity.encoded_zero_card
    2 (by decide) pairEncoding (polynomial v) (polynomial_ne_zero hv)
  have heval (x : F × F) : eval (pairEncoding x) (polynomial v)=form v x :=
    polynomial_eval v x
  simp only [heval,show 2-1=1 by decide,pow_one] at h
  exact h.trans (Nat.mul_le_mul_right _ (polynomial_degree v))

omit [Fintype F] in
lemma exists_nonzero {v : Coeff F} (hv : v ≠ 0) : ∃ i, v i ≠ 0 := by
  by_contra! h
  exact hv (funext h)

def pivot (v : Coeff F) : Fin 4 :=
  if h : ∃ i, v i ≠ 0 then Classical.choose h else 0
omit [Fintype F] in
lemma pivot_ne_zero {v : Coeff F} (hv : v ≠ 0) : v (pivot v) ≠ 0 := by
  have h := exists_nonzero hv
  unfold pivot
  rw [dif_pos h]
  exact Classical.choose_spec h

def decode (p : Profile F) : Coeff F := p.1.insertNth 1 p.2
omit [Fintype F] in
lemma decode_ne_zero (p : Profile F) : decode p ≠ 0 := by
  intro h
  have hh := congrFun h p.1
  simp [decode] at hh

def label (v : Coeff F) : Profile F :=
  (pivot v,fun j => v ((pivot v).succAbove j)/v (pivot v))

omit [Fintype F] in
lemma normalized (v : Coeff F) : v=v (pivot v) • decode (label v) := by
  by_cases hv : v=0
  · subst v; simp
  · have hp := pivot_ne_zero hv
    funext j
    refine Fin.succAboveCases (pivot v) ?_ (fun k => ?_) j
    · simp [decode,label]
    · simp only [decode,label,Fin.insertNth_apply_succAbove,Pi.smul_apply,smul_eq_mul]
      field_simp

omit [Fintype F] in
lemma normalized_form (v : Coeff F) (x : F × F) :
    form v x=v (pivot v)*form (decode (label v)) x := by
  conv_lhs => rw [normalized v]
  simp only [form,Pi.smul_apply,smul_eq_mul]
  ring

lemma form_zero_iff {v : Coeff F} (hv : v ≠ 0) (x : F × F) :
    form v x=0 ↔ x ∈ zeros (decode (label v)) := by
  rw [normalized_form]
  simp [zeros,pivot_ne_zero hv]

variable {C X : Type*} [Fintype C] [Fintype X]
def goodNeighbors (A : X → C → Coeff F) (c : C) : Finset (X × (F × F)) :=
  univ.filter (fun x => A x.1 c ≠ 0 ∧ form (A x.1 c) x.2=0)
def goodGraph (A : X → C → Coeff F) : SimpleGraph (C ⊕ (X × (F × F))) :=
  Erdos714Packing.incidence (goodNeighbors A)

/-- Only nonzero coefficient profiles belong to this host. Identically
zero fibers must be bounded separately before applying this theorem. -/
theorem good_thinning_bound (A : X → C → Coeff F)
    (H : SimpleGraph (C ⊕ (X × (F × F)))) (hH : H ≤ goodGraph A)
    (hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H)
    (hX : Fintype.card X ≤ Fintype.card F^2)
    (hC : Fintype.card C ≤ Fintype.card F^4) :
    H.edgeFinset.card^4 ≤ 829440000*Fintype.card F^27 := by
  let g (x : X) (c : C) := label (A x c)
  let Z (_ : X) (p : Profile F) := zeros (decode p)
  have hsub : goodGraph A ≤ Erdos714SmallProfiles.graph g Z := by
    intro u v huv
    cases u with
    | inl c =>
      cases v with
      | inl d => exact False.elim huv
      | inr x =>
        obtain ⟨hn,he⟩ := (mem_filter.mp huv).2
        have ht : x.2 ∈ Z x.1 (g x.1 c) := (form_zero_iff hn x.2).mp he
        simpa only [Erdos714SmallProfiles.graph,Erdos714Packing.incidence,
          Erdos714SmallProfiles.neighbors,mem_filter,mem_univ,true_and] using ht
    | inr x =>
      cases v with
      | inr y => exact False.elim huv
      | inl c =>
        obtain ⟨hn,he⟩ := (mem_filter.mp huv).2
        have ht : x.2 ∈ Z x.1 (g x.1 c) := (form_zero_iff hn x.2).mp he
        simpa only [Erdos714SmallProfiles.graph,Erdos714Packing.incidence,
          Erdos714SmallProfiles.neighbors,mem_filter,mem_univ,true_and] using ht
  apply Erdos714SmallProfiles.critical_bound g Z (Fintype.card F)
    Fintype.card_pos (fun _ p => zeros_bound (decode_ne_zero p)) hX hC _ H
    (hH.trans hsub) hf
  simp [Profile]

#print axioms zeros_bound
#print axioms normalized
#print axioms good_thinning_bound
end Erdos714BilinearProfiles
