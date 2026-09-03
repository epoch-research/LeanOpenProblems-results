import Submission.BilinearProfiles

/-!
A thinning obstruction for the explicit four-dimensional Grassmannian chart
(1,a,b,c,d,a^2-bd,ab-cd,b^2-ac), paired by any linear equivalence of F^8.
The identically zero bilinear fibers are counted separately. This is not a
classification of projective varieties and does not settle Erdős 714.
-/
noncomputable section
open Classical Finset SimpleGraph MvPolynomial
set_option maxHeartbeats 5000000
namespace Erdos714GrassmannFourChart
open Erdos714BilinearProfiles (Coeff form sum_degree_le pairEncoding)
variable {F : Type*} [Field F]
abbrev Point (F : Type*) := (F × F) × (F × F)
abbrev Ambient (F : Type*) := Fin 8 → F

def chart (p : Point F) : Ambient F :=
  let a := p.1.1; let b := p.1.2; let c := p.2.1; let d := p.2.2
  ![1,a,b,c,d,a^2-b*d,a*b-c*d,b^2-a*c]
lemma chart_ne_zero (p : Point F) : chart p ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp [chart] at h0
lemma chart_injective : Function.Injective (chart (F := F)) := by
  intro p q h
  exact Prod.ext (Prod.ext (congrFun h 1) (congrFun h 2))
    (Prod.ext (congrFun h 3) (congrFun h 4))

def dot (l v : Ambient F) : F := ∑ i, l i*v i

/-- An actual rank-two matrix producing the Grassmannian coordinates. -/
def firstRow (p : Point F) : Fin 5 → F := ![1,0,p.1.1,p.1.2,p.2.1]
def secondRow (p : Point F) : Fin 5 → F := ![0,1,p.2.2,p.1.1,p.1.2]
def pairIndices : Fin 10 → Fin 5 × Fin 5 :=
  ![(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)]
def plucker (p : Point F) : Fin 10 → F :=
  ![1,p.2.2,p.1.1,p.1.2,-p.1.1,-p.1.2,-p.2.1,
    p.1.1^2-p.1.2*p.2.2,p.1.1*p.1.2-p.2.1*p.2.2,p.1.2^2-p.1.1*p.2.1]
lemma plucker_minors (p : Point F) (i : Fin 10) : plucker p i =
    firstRow p (pairIndices i).1*secondRow p (pairIndices i).2-
    firstRow p (pairIndices i).2*secondRow p (pairIndices i).1 := by
  fin_cases i <;> simp [plucker,firstRow,secondRow,pairIndices] <;> ring
lemma rows_independent (p : Point F) (s t : F)
    (h : s • firstRow p+t • secondRow p=0) : s=0 ∧ t=0 := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simpa [firstRow,secondRow] using And.intro h0 h1
lemma linear_sections (p : Point F) :
    plucker p 0=1 ∧ plucker p 2+plucker p 4=0 ∧ plucker p 3+plucker p 5=0 := by
  simp [plucker]
lemma plucker_quadrics (p : Point F) :
    plucker p 0*plucker p 7-plucker p 1*plucker p 5+plucker p 2*plucker p 4=0 ∧
    plucker p 0*plucker p 8-plucker p 1*plucker p 6+plucker p 3*plucker p 4=0 ∧
    plucker p 0*plucker p 9-plucker p 2*plucker p 6+plucker p 3*plucker p 5=0 ∧
    plucker p 1*plucker p 9-plucker p 2*plucker p 8+plucker p 3*plucker p 7=0 ∧
    plucker p 4*plucker p 9-plucker p 5*plucker p 8+plucker p 6*plucker p 7=0 := by
  simp only [plucker]
  dsimp
  constructor
  · ring
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring


def exponents : Fin 11 → (Fin 4 →₀ ℕ) :=
  ![0,Finsupp.single 0 1,Finsupp.single 1 1,Finsupp.single 2 1,Finsupp.single 3 1,
    Finsupp.single 0 2,Finsupp.single 0 1+Finsupp.single 1 1,Finsupp.single 1 2,
    Finsupp.single 1 1+Finsupp.single 3 1,Finsupp.single 2 1+Finsupp.single 3 1,
    Finsupp.single 0 1+Finsupp.single 2 1]
lemma exponents_injective : Function.Injective exponents := by
  intro i j h
  have h0 := congrArg (fun v => v 0) h
  have h1 := congrArg (fun v => v 1) h
  have h2 := congrArg (fun v => v 2) h
  have h3 := congrArg (fun v => v 3) h
  fin_cases i <;> fin_cases j <;> simp [exponents] at h0 h1 h2 h3 ⊢

def values (l : Ambient F) : Fin 11 → F :=
  ![l 0,l 1,l 2,l 3,l 4,l 5,l 6,l 7,-l 5,-l 6,-l 7]
def polynomial (l : Ambient F) : MvPolynomial (Fin 4) F :=
  ∑ i, monomial (exponents i) (values l i)
lemma coefficient (l : Ambient F) (i : Fin 11) :
    coeff (exponents i) (polynomial l)=values l i := by
  simp [polynomial,coeff_sum,coeff_monomial,exponents_injective.eq_iff]
lemma polynomial_ne_zero {l : Ambient F} (hl : l ≠ 0) : polynomial l ≠ 0 := by
  intro h
  apply hl
  funext i
  have hi := congrArg (coeff (exponents (Fin.castLE (by decide : 8≤11) i))) h
  rw [coefficient,coeff_zero] at hi
  fin_cases i <;> simpa [values] using hi
lemma polynomial_degree (l : Ambient F) : (polynomial l).totalDegree ≤ 2 := by
  apply sum_degree_le
  intro i
  apply (totalDegree_monomial_le _ _).trans
  fin_cases i <;> simp [exponents,Finsupp.sum_fintype,Fin.sum_univ_four]

def encoding : Point F ↪ (Fin 4 → F) :=
  ⟨fun p => ![p.1.1,p.1.2,p.2.1,p.2.2],by
    intro p q h
    exact Prod.ext (Prod.ext (congrFun h 0) (congrFun h 1))
      (Prod.ext (congrFun h 2) (congrFun h 3))⟩
lemma polynomial_eval (l : Ambient F) (p : Point F) :
    eval (encoding p) (polynomial l)=dot l (chart p) := by
  simp [polynomial,values,Fin.sum_univ_succ,exponents,eval_monomial,
    Finsupp.prod_fintype,Fin.prod_univ_four,encoding,dot,chart]
  ring

/-- The four coefficients on the c,d fiber at fixed a,b. -/
def profile (l : Ambient F) (x : F × F) : Coeff F :=
  ![l 0+l 1*x.1+l 2*x.2+l 5*x.1^2+l 6*x.1*x.2+l 7*x.2^2,
    l 3-l 7*x.1,l 4-l 5*x.2,-l 6]
lemma dot_eq_form (l : Ambient F) (x y : F × F) :
    dot l (chart (x,y))=form (profile l x) y := by
  simp [dot,chart,profile,form,Fin.sum_univ_succ]
  ring

/-- Exponents for the six possible coefficients in the constant fiber term. -/
def baseExponents : Fin 6 → (Fin 2 →₀ ℕ) :=
  ![0,Finsupp.single 0 1,Finsupp.single 1 1,Finsupp.single 0 2,
    Finsupp.single 0 1+Finsupp.single 1 1,Finsupp.single 1 2]
lemma baseExponents_injective : Function.Injective baseExponents := by
  intro i j h
  have h0 := congrArg (fun v => v 0) h
  have h1 := congrArg (fun v => v 1) h
  fin_cases i <;> fin_cases j <;> simp [baseExponents] at h0 h1 ⊢
def baseValues (l : Ambient F) : Fin 6 → F := ![l 0,l 1,l 2,l 5,l 6,l 7]
def basePolynomial (l : Ambient F) : MvPolynomial (Fin 2) F :=
  ∑ i, monomial (baseExponents i) (baseValues l i)
lemma base_coefficient (l : Ambient F) (i : Fin 6) :
    coeff (baseExponents i) (basePolynomial l)=baseValues l i := by
  simp [basePolynomial,coeff_sum,coeff_monomial,baseExponents_injective.eq_iff]
lemma base_degree (l : Ambient F) : (basePolynomial l).totalDegree ≤ 2 := by
  apply sum_degree_le
  intro i
  apply (totalDegree_monomial_le _ _).trans
  fin_cases i <;> simp [baseExponents,Finsupp.sum_fintype,Fin.sum_univ_two]
lemma base_eval (l : Ambient F) (x : F × F) :
    eval (pairEncoding x) (basePolynomial l)=profile l x 0 := by
  simp [basePolynomial,baseValues,Fin.sum_univ_succ,baseExponents,eval_monomial,
    Finsupp.prod_fintype,Fin.prod_univ_two,pairEncoding,profile,mul_assoc]
  ring

lemma profile_ne_zero_of_base_zero {l : Ambient F} (hl : l ≠ 0)
    (hp : basePolynomial l=0) (x : F × F) : profile l x ≠ 0 := by
  have hc (i : Fin 6) : baseValues l i=0 := by
    have h := congrArg (coeff (baseExponents i)) hp
    simpa only [base_coefficient,coeff_zero] using h
  intro hzero
  have h1 := congrFun hzero 1
  have h2 := congrFun hzero 2
  have h0 := hc 0; have ha := hc 1; have hb := hc 2
  have h5 := hc 3; have h6 := hc 4; have h7 := hc 5
  simp only [baseValues,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.head_cons,Matrix.tail_cons] at h0 ha hb h5 h6 h7
  apply hl
  funext i
  fin_cases i <;> simp_all [profile]

variable [Fintype F]
def zeroProfiles (l : Ambient F) : Finset (F × F) := univ.filter (fun x => profile l x=0)
lemma zero_profile_bound {l : Ambient F} (hl : l ≠ 0) :
    (zeroProfiles l).card ≤ 2*Fintype.card F := by
  by_cases hp : basePolynomial l=0
  · have he : zeroProfiles l=∅ := by
      ext x
      simp [zeroProfiles,profile_ne_zero_of_base_zero hl hp x]
    simp [he]
  · have hs : zeroProfiles l ⊆ univ.filter (fun x : F × F =>
        eval (pairEncoding x) (basePolynomial l)=0) := by
      intro x hx
      apply mem_filter.mpr
      refine ⟨mem_univ _,?_⟩
      rw [base_eval]
      exact congrFun (mem_filter.mp hx).2 0
    have h := Erdos714PolynomialExceptionalDensity.encoded_zero_card
      2 (by decide) pairEncoding (basePolynomial l) hp
    norm_num only [Nat.reduceSub,pow_one] at h
    exact (card_le_card hs).trans (h.trans (Nat.mul_le_mul_right _ (base_degree l)))

omit [Fintype F] in
lemma zero_profile_forces_six {l : Ambient F} {x : F × F} (h : profile l x=0) : l 6=0 := by
  have hh := congrFun h 3
  simpa [profile] using hh

/-- A coordinate row of a linear equivalence is a nonzero linear functional. -/
def linearRow (L : Ambient F ≃ₗ[F] Ambient F) (j : Fin 8) : Ambient F :=
  fun i => L (Pi.single i 1) j
omit [Fintype F] in
lemma linearRow_apply (L : Ambient F ≃ₗ[F] Ambient F) (j : Fin 8) (v : Ambient F) :
    L v j=dot (linearRow L j) v := by
  have hv : (∑ i : Fin 8, v i • (Pi.single i 1 : Ambient F))=v := by
    ext k
    simp [Pi.single_apply]
  conv_lhs => rw [← hv]
  simp [dot,linearRow,map_sum,map_smul,Finset.sum_apply,Pi.smul_apply,mul_comm]
omit [Fintype F] in
lemma linearRow_ne_zero (L : Ambient F ≃ₗ[F] Ambient F) (j : Fin 8) : linearRow L j ≠ 0 := by
  intro h
  have he := linearRow_apply L j (L.symm (Pi.single j 1))
  rw [L.apply_symm_apply,h] at he
  simp [dot] at he

def coefficients (L : Ambient F ≃ₗ[F] Ambient F) (p : Point F) : Ambient F := L (chart p)
omit [Fintype F] in
lemma coefficients_ne_zero (L : Ambient F ≃ₗ[F] Ambient F) (p : Point F) :
    coefficients L p ≠ 0 := by
  intro h
  apply chart_ne_zero p
  apply L.injective
  simpa [coefficients] using h

lemma rare_column_bound (L : Ambient F ≃ₗ[F] Ambient F) :
    (univ.filter (fun p : Point F => coefficients L p 6=0)).card ≤ 2*Fintype.card F^3 := by
  have heval (p : Point F) :
      eval (encoding p) (polynomial (linearRow L 6))=coefficients L p 6 := by
    rw [polynomial_eval,← linearRow_apply]
    rfl
  have h := Erdos714PolynomialExceptionalDensity.encoded_zero_card
    4 (by decide) encoding (polynomial (linearRow L 6))
    (polynomial_ne_zero (linearRow_ne_zero L 6))
  simp only [heval,show 4-1=3 by decide] at h
  exact h.trans (Nat.mul_le_mul_right _ (polynomial_degree _))

/-- The original bilinear hyperplane-incidence host. -/
def neighbors (L : Ambient F ≃ₗ[F] Ambient F) (c : Point F) : Finset (Point F) :=
  univ.filter (fun p => dot (coefficients L c) (chart p)=0)
def graph (L : Ambient F ≃ₗ[F] Ambient F) : SimpleGraph (Point F ⊕ Point F) :=
  Erdos714Packing.incidence (neighbors L)

def goodGraph (L : Ambient F ≃ₗ[F] Ambient F) : SimpleGraph (Point F ⊕ Point F) :=
  Erdos714BilinearProfiles.goodGraph (fun x c => profile (coefficients L c) x)
def badNeighbors (L : Ambient F ≃ₗ[F] Ambient F) (c : Point F) : Finset (Point F) :=
  univ.filter (fun p => profile (coefficients L c) p.1=0)
def badGraph (L : Ambient F ≃ₗ[F] Ambient F) : SimpleGraph (Point F ⊕ Point F) :=
  Erdos714Packing.incidence (badNeighbors L)

lemma bad_degree (L : Ambient F ≃ₗ[F] Ambient F) (c : Point F) :
    (badNeighbors L c).card=(zeroProfiles (coefficients L c)).card*Fintype.card F^2 := by
  have he : badNeighbors L c=(zeroProfiles (coefficients L c)).product (univ : Finset (F × F)) := by
    ext p
    simp [badNeighbors,zeroProfiles]
  rw [he,Finset.product_eq_sprod,card_product,card_univ,Fintype.card_prod]
  ring

lemma bad_degree_bound (L : Ambient F ≃ₗ[F] Ambient F) (c : Point F) :
    (badNeighbors L c).card ≤ if coefficients L c 6=0 then 2*Fintype.card F^3 else 0 := by
  by_cases hc : coefficients L c 6=0
  · rw [if_pos hc,bad_degree]
    calc
      _ ≤ (2*Fintype.card F)*Fintype.card F^2 :=
        Nat.mul_le_mul_right _ (zero_profile_bound (coefficients_ne_zero L c))
      _ = _ := by ring
  · have hz : zeroProfiles (coefficients L c)=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact hc (zero_profile_forces_six (mem_filter.mp hx).2)
    simp [hc,bad_degree,hz]

/-- All identically zero fibers together contribute only O(q^6) edges. -/
theorem bad_edge_bound (L : Ambient F ≃ₗ[F] Ambient F) :
    (badGraph L).edgeFinset.card ≤ 4*Fintype.card F^6 := by
  rw [badGraph,Erdos714Packing.incidence_edges]
  calc
    _ ≤ ∑ c : Point F, if coefficients L c 6=0 then 2*Fintype.card F^3 else 0 :=
      sum_le_sum (fun c _ => bad_degree_bound L c)
    _ = (univ.filter (fun c : Point F => coefficients L c 6=0)).card*(2*Fintype.card F^3) := by
      rw [← sum_filter]
      simp
    _ ≤ (2*Fintype.card F^3)*(2*Fintype.card F^3) :=
      Nat.mul_le_mul_right _ (rare_column_bound L)
    _ = _ := by ring

lemma host_le_sup (L : Ambient F ≃ₗ[F] Ambient F) : graph L ≤ goodGraph L ⊔ badGraph L := by
  have he (c p : Point F) (h : dot (coefficients L c) (chart p)=0) :
      (goodGraph L).Adj (.inl c) (.inr p) ∨ (badGraph L).Adj (.inl c) (.inr p) := by
    by_cases hp : profile (coefficients L c) p.1=0
    · right
      exact mem_filter.mpr ⟨mem_univ _,hp⟩
    · left
      have hh := dot_eq_form (coefficients L c) p.1 p.2
      exact mem_filter.mpr ⟨mem_univ _,hp,hh.symm.trans h⟩
  intro u v huv
  cases u with
  | inl c =>
    cases v with
    | inl d => exact False.elim huv
    | inr p => exact he c p ((mem_filter.mp huv).2)
  | inr p =>
    cases v with
    | inr q => exact False.elim huv
    | inl c => exact he c p ((mem_filter.mp huv).2)

omit [Field F] in
lemma card_point : Fintype.card (Point F)=Fintype.card F^4 := by
  simp only [Point,Fintype.card_prod]
  ring

/-- Arbitrary K44-free edge thinnings of the entire chart are subcritical.
No exceptional zero polynomial or coefficient row is discarded. -/
theorem thinning_bound (L : Ambient F ≃ₗ[F] Ambient F)
    (H : SimpleGraph (Point F ⊕ Point F)) (hH : H ≤ graph L)
    (hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H) :
    H.edgeFinset.card^4 ≤ 6635522048*Fintype.card F^27 := by
  let G := H ⊓ goodGraph L
  let B := H ⊓ badGraph L
  have hgf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free G := by
    intro h
    exact hf (h.mono_right inf_le_left)
  have hg : G.edgeFinset.card^4 ≤ 829440000*Fintype.card F^27 := by
    have ht := Erdos714BilinearProfiles.good_thinning_bound
      (fun x c => profile (coefficients L c) x) G inf_le_right hgf
      (by simp [pow_two]) card_point.le
    simpa only [edgeFinset_card,Fintype.card_eq_nat_card] using ht
  have hb : B.edgeFinset.card ≤ 4*Fintype.card F^6 :=
    (card_le_card (edgeFinset_mono (show B ≤ badGraph L from inf_le_right))).trans (bad_edge_bound L)
  have hs : H ≤ G ⊔ B := by
    dsimp [G,B]
    rw [← inf_sup_left]
    exact le_inf le_rfl (hH.trans (host_le_sup L))
  have he : H.edgeFinset.card ≤ G.edgeFinset.card+B.edgeFinset.card := by
    have h := card_le_card (edgeFinset_mono hs)
    rw [edgeFinset_sup] at h
    exact h.trans (card_union_le _ _)
  have hp := add_pow_le (Nat.zero_le G.edgeFinset.card) (Nat.zero_le B.edgeFinset.card) 4
  norm_num only at hp
  have hq : 1 ≤ Fintype.card F := Fintype.card_pos
  have h24 : Fintype.card F^24 ≤ Fintype.card F^27 := pow_le_pow_right' hq (by decide)
  calc
    _ ≤ (G.edgeFinset.card+B.edgeFinset.card)^4 := Nat.pow_le_pow_left he 4
    _ ≤ 8*(G.edgeFinset.card^4+B.edgeFinset.card^4) := hp
    _ ≤ 8*(829440000*Fintype.card F^27+(4*Fintype.card F^6)^4) := by gcongr
    _ = 6635520000*Fintype.card F^27+2048*Fintype.card F^24 := by ring
    _ ≤ 6635520000*Fintype.card F^27+2048*Fintype.card F^27 := by gcongr
    _ = _ := by ring

/-- The constant loss of any proposed critical construction bounds its
field size. Thus no unbounded fixed-loss family lies in this chart model. -/
theorem size_budget (L : Ambient F ≃ₗ[F] Ambient F)
    (H : SimpleGraph (Point F ⊕ Point F)) (hH : H ≤ graph L)
    (hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H)
    (C : ℕ) (he : Fintype.card F^7 ≤ C*H.edgeFinset.card) :
    Fintype.card F ≤ 6635522048*C^4 := by
  have hp : Fintype.card F^27*Fintype.card F ≤ Fintype.card F^27*(6635522048*C^4) := by
    calc
      _ = (Fintype.card F^7)^4 := by ring
      _ ≤ (C*H.edgeFinset.card)^4 := Nat.pow_le_pow_left he 4
      _ = C^4*H.edgeFinset.card^4 := by ring
      _ ≤ C^4*(6635522048*Fintype.card F^27) := Nat.mul_le_mul_left _ (thinning_bound L H hH hf)
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_left hp (pow_pos Fintype.card_pos 27)

#print axioms plucker_minors
#print axioms rows_independent
#print axioms linear_sections
#print axioms plucker_quadrics
#print axioms chart_injective
#print axioms polynomial_ne_zero
#print axioms zero_profile_bound
#print axioms rare_column_bound
#print axioms bad_edge_bound
#print axioms thinning_bound
#print axioms size_budget
end Erdos714GrassmannFourChart
