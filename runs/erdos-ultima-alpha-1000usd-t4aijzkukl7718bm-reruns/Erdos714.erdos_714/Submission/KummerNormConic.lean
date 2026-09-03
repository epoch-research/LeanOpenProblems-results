import FormalConjecturesUtil

/-!
Exact conic/quartic reduction for three equal-weight rows of a cubic norm graph.
This supplies a conditional certificate, not a K44-free construction or a
settlement of the conjecture in Spec.lean.
-/
noncomputable section
open Polynomial SimpleGraph Classical
set_option maxHeartbeats 3000000
namespace Erdos714KummerConic
variable {F E : Type*} [Field F] [Field E] [Algebra F E]

def element (z : E) (a b c : F) : E :=
  algebraMap F E a+algebraMap F E b*z+algebraMap F E c*z^2

def form (d a b c : F) : F := a^3+d*b^3+d^2*c^3-3*d*a*b*c

def multiplicationMatrix (d a b c : F) : Matrix (Fin 3) (Fin 3) F :=
  !![a,d*c,d*b;b,a,d*c;c,b,a]

lemma leftMulMatrix_element (d : F) (z : E) (hz : z^3=algebraMap F E d)
    (B : Module.Basis (Fin 3) F E) (hB : ∀ i, B i=z^(i:ℕ)) (a b c : F) :
    Algebra.leftMulMatrix B (element z a b c)=multiplicationMatrix d a b c := by
  have hz4 : z^4=algebraMap F E d*z := by rw [show (4:ℕ)=3+1 from rfl,pow_succ,hz]
  have hcol (j : Fin 3) : ∑ i, multiplicationMatrix d a b c i j • B i =
      element z a b c*B j := by
    simp only [Fin.sum_univ_three,hB,Algebra.smul_def]
    fin_cases j
    · change algebraMap F E a*z^0+algebraMap F E b*z^1+algebraMap F E c*z^2 = _
      simp only [element]; ring
    · change algebraMap F E (d*c)*z^0+algebraMap F E a*z^1+algebraMap F E b*z^2 = _
      simp only [element,map_mul]
      ring_nf
      rw [hz]
      ring
    · change algebraMap F E (d*b)*z^0+algebraMap F E (d*c)*z^1+algebraMap F E a*z^2 = _
      simp only [element,map_mul]
      ring_nf
      rw [hz4,hz]
      ring
  ext i j
  rw [Algebra.leftMulMatrix_eq_repr_mul,← hcol j]
  simp [Finsupp.single_apply]

/-- Identification with the actual algebra norm, in any supplied Kummer basis. -/
theorem norm_element (d : F) (z : E) (hz : z^3=algebraMap F E d)
    (B : Module.Basis (Fin 3) F E) (hB : ∀ i, B i=z^(i:ℕ)) (a b c : F) :
    Algebra.norm F (element z a b c)=form d a b c := by
  rw [Algebra.norm_eq_matrix_det B,leftMulMatrix_element d z hz B hB,
    Matrix.det_fin_three]
  simp [multiplicationMatrix,form]
  ring

lemma element_injective (z : E) (B : Module.Basis (Fin 3) F E)
    (hB : ∀ i, B i=z^(i:ℕ)) :
    Function.Injective (fun v : Fin 3 → F => element z (v 0) (v 1) (v 2)) := by
  have he (v : Fin 3 → F) : element z (v 0) (v 1) (v 2)=∑ i, v i • B i := by
    simp [element,Fin.sum_univ_three,hB,Algebra.smul_def]
  intro v w h
  dsimp only at h
  rw [he,he,← B.equivFun_symm_apply,← B.equivFun_symm_apply] at h
  exact B.equivFun.symm.injective h

/-- Norms on the common-neighbor conic of scalar rows 0, 1, -1. -/
def weight (d s : F) : F := d*s^3+1/(27*d*s^3)

lemma conic_form (d s t : F) (h3 : (3:F)≠0) (hd : d≠0) (hs : s≠0) :
    form d t s (1/(3*d*s))=t^3-t+weight d s := by
  dsimp [form,weight]
  have h27 : (27:F)≠0 := by convert pow_ne_zero 3 h3 using 1; norm_num
  field_simp
  ring

/-- The fourth-row condition after clearing exactly 3*s^2, not a zero denominator. -/
def quartic (d a u v : F) : F[X] :=
  C (9*d*u)*X^4+C (9*d*(u^2-a*v))*X^3+C (3*(form d a u v-a))*X^2+
    C (3*(d*v^2-a*u))*X+C v

lemma fourth_equation (d a u v s : F) (h3 : (3:F)≠0) (hd : d≠0) (hs : s≠0) :
    3*s^2*(form d a (u+s) (v+1/(3*d*s))-weight d s)=(quartic d a u v).eval s := by
  simp only [quartic,eval_add,eval_mul,eval_pow,eval_X,eval_C,form,weight]
  have h27 : (27:F)≠0 := by convert pow_ne_zero 3 h3 using 1; norm_num
  field_simp
  ring

lemma fourth_root_iff (d a u v s : F) (h3 : (3:F)≠0) (hd : d≠0) (hs : s≠0) :
    (quartic d a u v).eval s=0 ↔ form d a (u+s) (v+1/(3*d*s))=weight d s := by
  rw [← fourth_equation d a u v s h3 hd hs,mul_eq_zero]
  simp only [mul_ne_zero h3 (pow_ne_zero 2 hs),false_or,sub_eq_zero]

/-- Four distinct nonzero roots give all sixteen norm identities. -/
theorem norm_rectangle (d : F) (z : E) (hz : z^3=algebraMap F E d)
    (B : Module.Basis (Fin 3) F E) (hB : ∀ i, B i=z^(i:ℕ))
    (h3 : (3:F)≠0) (hd : d≠0) (a u v : F) (s : Fin 4 → F)
    (hs : ∀ j, s j≠0) (hr : ∀ j, (quartic d a u v).eval (s j)=0) :
    ∀ i j : Fin 4,
      Algebra.norm F ((![0,1,-1,element z a u v] : Fin 4 → E) i+
        element z 0 (s j) (1/(3*d*s j)))=weight d (s j) := by
  intro i j
  have hscalar (t : F) (ht : t^3=t) :
      Algebra.norm F (algebraMap F E t+element z 0 (s j) (1/(3*d*s j)))=
        weight d (s j) := by
    have he : algebraMap F E t+element z 0 (s j) (1/(3*d*s j))=
        element z t (s j) (1/(3*d*s j)) := by simp [element]; ring
    rw [he,norm_element d z hz B hB,conic_form d (s j) t h3 hd (hs j),ht]
    ring
  fin_cases i
  · simpa using hscalar 0 (by simp)
  · simpa using hscalar 1 (by simp)
  · simpa using hscalar (-1) (by norm_num)
  · have he : element z a u v+element z 0 (s j) (1/(3*d*s j))=
        element z a (u+s j) (v+1/(3*d*s j)) := by
      simp only [element,map_zero,map_add]; ring
    change Algebra.norm F (element z a u v+element z 0 (s j) (1/(3*d*s j)))=_
    rw [he,norm_element d z hz B hB]
    exact (fourth_root_iff d a u v (s j) h3 hd (hs j)).mp (hr j)

/-- The actual field-norm graph with nonzero square weights. -/
def squareGraph : SimpleGraph ((E × F) ⊕ (E × F)) where
  Adj x y := match x,y with
    | .inl p,.inr q => p.2≠0 ∧ q.2≠0 ∧ IsSquare p.2 ∧ IsSquare q.2 ∧
        Algebra.norm F (p.1+q.1)=p.2*q.2
    | .inr q,.inl p => p.2≠0 ∧ q.2≠0 ∧ IsSquare p.2 ∧ IsSquare q.2 ∧
        Algebra.norm F (p.1+q.1)=p.2*q.2
    | _,_ => False
  symm := by intro x y; cases x <;> cases y <;> exact id
  loopless := by intro x; cases x <;> exact not_false

/-- A genuine copy, including injections and all weight restrictions. Root
existence and the square tests remain explicit hypotheses. -/
def squareCopy (d : F) (z : E) (hz : z^3=algebraMap F E d)
    (B : Module.Basis (Fin 3) F E) (hB : ∀ i, B i=z^(i:ℕ))
    (h2 : (2:F)≠0) (h3 : (3:F)≠0) (hd : d≠0) (a u v : F) (hu : u≠0)
    (s : Fin 4 → F) (hs : ∀ j, s j≠0) (hinj : Function.Injective s)
    (hr : ∀ j, (quartic d a u v).eval (s j)=0)
    (hw : ∀ j, weight d (s j)≠0 ∧ IsSquare (weight d (s j))) :
    (completeBipartiteGraph (Fin 4) (Fin 4)).Copy (squareGraph (F := F) (E := E)) := by
  let rc : Fin 4 → Fin 3 → F := ![![0,0,0],![1,0,0],![-1,0,0],![a,u,v]]
  let cc : Fin 4 → Fin 3 → F := fun j => ![0,s j,1/(3*d*s j)]
  let point : (Fin 3 → F) → E := fun w => element z (w 0) (w 1) (w 2)
  have hp : Function.Injective point := element_injective z B hB
  have hpm : (1:F)≠ -1 := by intro h; apply h2; linear_combination h
  have hri : Function.Injective rc := by
    intro i j hij
    have h0 := congrFun hij 0
    have h1 := congrFun hij 1
    fin_cases i <;> fin_cases j <;> simp_all [rc,Ne.symm hu,Ne.symm hpm]
  have hci : Function.Injective cc := by
    intro i j hij
    exact hinj (congrFun hij 1)
  let L : Fin 4 ↪ E × F := ⟨fun i => (point (rc i),1),by
    intro i j h
    exact hri (hp (congrArg Prod.fst h))⟩
  let R : Fin 4 ↪ E × F := ⟨fun j => (point (cc j),weight d (s j)),by
    intro i j h
    exact hci (hp (congrArg Prod.fst h))⟩
  have he (i j : Fin 4) : Algebra.norm F ((L i).1+(R j).1)=weight d (s j) := by
    have hrc : point (rc i)=(![0,1,-1,element z a u v] : Fin 4 → E) i := by
      fin_cases i <;> simp [point,rc,element]
    change Algebra.norm F (point (rc i)+point (cc j))=_
    rw [hrc]
    exact norm_rectangle d z hz B hB h3 hd a u v s hs hr i j
  refine ⟨⟨L.sumMap R,?_⟩,(L.sumMap R).injective⟩
  intro x y hxy
  cases x with
  | inl i =>
    cases y with
    | inl j => simp at hxy
    | inr j =>
      exact ⟨one_ne_zero,(hw j).1,⟨1,by simp [L]⟩,(hw j).2,by simpa [L,R] using he i j⟩
  | inr j =>
    cases y with
    | inl i =>
      exact ⟨one_ne_zero,(hw j).1,⟨1,by simp [L]⟩,(hw j).2,by simpa [L,R] using he i j⟩
    | inr i => simp at hxy

#print axioms norm_element
#print axioms element_injective
#print axioms conic_form
#print axioms fourth_equation
#print axioms fourth_root_iff
#print axioms norm_rectangle
#print axioms squareCopy
end Erdos714KummerConic
