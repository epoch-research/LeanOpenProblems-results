import Submission.UnbalancedParabolas

/-! A noncommutative quartic model: a positive one-direction recovery result
and exact finite failures. No global freeness or result on Erdős 714 is claimed. -/
noncomputable section
open SimpleGraph Classical
namespace Erdos714NoncommutativeQuartic
variable {F : Type*} [Field F]

def realPart (D e₀ e₁ b c : F) : F := e₀*(b^2+D*c^2)+2*e₁*D*b*c

def normForm (D e₀ e₁ a b c : F) : F :=
  (D*a^2-realPart D e₀ e₁ b c)^2 -
    D*(e₁*(b^2+D*c^2)+2*e₀*b*c)^2

/-- Multiplication by `a*u+b*v+c*u*v` in the basis `1,u,v,u*v`, where
`u²=D` and `v²=e₀+e₁*u`. -/
def multiplicationMatrix (D e₀ e₁ a b c : F) : Matrix (Fin 4) (Fin 4) F :=
  !![0,a*D,b*e₀+c*e₁*D,b*e₁*D+c*D*e₀;
     a,0,b*e₁+c*e₀,b*e₀+c*D*e₁;
     b,c*D,0,a*D;
     c,b,a,0]

set_option maxHeartbeats 2000000 in
lemma normForm_eq_det (D e₀ e₁ a b c : F) :
    normForm D e₀ e₁ a b c = (multiplicationMatrix D e₀ e₁ a b c).det := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_four]
  simp [Matrix.det_fin_three,multiplicationMatrix,Matrix.submatrix,Fin.succAbove,normForm,realPart]
  ring

section NormSemantics
variable {E : Type*} [CommRing E] [Algebra F E]

def coordinate (u v : E) (a b c : F) : E :=
  algebraMap F E a*u+algebraMap F E b*v+algebraMap F E c*u*v

lemma leftMulMatrix_coordinate (D e₀ e₁ : F) (u v : E)
    (hu : u^2=algebraMap F E D)
    (hv : v^2=algebraMap F E e₀+algebraMap F E e₁*u)
    (B : Module.Basis (Fin 4) F E) (hB : ∀ i, B i=![1,u,v,u*v] i)
    (a b c : F) :
    Algebra.leftMulMatrix B (coordinate u v a b c) = multiplicationMatrix D e₀ e₁ a b c := by
  have hcol (j : Fin 4) :
      ∑ i, (multiplicationMatrix D e₀ e₁ a b c i j) • B i =
        coordinate u v a b c * B j := by
    simp only [Fin.sum_univ_four,hB,Algebra.smul_def]
    fin_cases j <;> simp [multiplicationMatrix,coordinate,map_add,map_mul]
    all_goals ring_nf
    all_goals simp only [hu,hv]
    all_goals ring_nf
    all_goals simp only [hu]
    all_goals ring
  ext i j
  rw [Algebra.leftMulMatrix_eq_repr_mul, ← hcol j]
  simp [Finsupp.single_apply]

theorem coordinate_norm (D e₀ e₁ : F) (u v : E)
    (hu : u^2=algebraMap F E D)
    (hv : v^2=algebraMap F E e₀+algebraMap F E e₁*u)
    (B : Module.Basis (Fin 4) F E) (hB : ∀ i, B i=![1,u,v,u*v] i)
    (a b c : F) : Algebra.norm F (coordinate u v a b c)=normForm D e₀ e₁ a b c := by
  rw [Algebra.norm_eq_matrix_det B,leftMulMatrix_coordinate D e₀ e₁ u v hu hv B hB,
    ← normForm_eq_det]

theorem coordinate_trace (D e₀ e₁ : F) (u v : E)
    (hu : u^2=algebraMap F E D)
    (hv : v^2=algebraMap F E e₀+algebraMap F E e₁*u)
    (B : Module.Basis (Fin 4) F E) (hB : ∀ i, B i=![1,u,v,u*v] i)
    (a b c : F) : Algebra.trace F E (coordinate u v a b c)=0 := by
  rw [Algebra.trace_eq_matrix_trace B,leftMulMatrix_coordinate D e₀ e₁ u v hu hv B hB]
  simp [Matrix.trace,multiplicationMatrix,Fin.sum_univ_four]

end NormSemantics

def graph (D e₀ e₁ : F) : SimpleGraph ((Fin 4 → F) ⊕ (Fin 4 → F)) where
  Adj x y := match x,y with
    | .inl x, .inr y => normForm D e₀ e₁ (x 0+y 0) (x 1+y 1) (x 2+y 2) =
        x 3+y 3+x 0*y 1-x 1*y 0
    | .inr y, .inl x => normForm D e₀ e₁ (x 0+y 0) (x 1+y 1) (x 2+y 2) =
        x 3+y 3+x 0*y 1-x 1*y 0
    | _, _ => False
  symm := by intro x y; cases x <;> cases y <;> simp_all
  loopless := by intro x; cases x <;> simp

/-- Four distinct scalar rows determine the first two column coordinates and
leave only a quadratic ambiguity in the third. The noncommutative correction
`-t*b` is essential to recovering `b`. -/
theorem scalar_profile (D e₀ e₁ : F) (hD : D ≠ 0) (h₂ : (2 : F) ≠ 0)
    (t : Fin 4 ↪ F) (a b c v a' b' c' v' : F)
    (h : ∀ i, normForm D e₀ e₁ (a+t i) b c-t i*b-v =
      normForm D e₀ e₁ (a'+t i) b' c'-t i*b'-v') :
    a = a' ∧ b = b' ∧ (c = c' ∨ e₀*(c+c')+2*e₁*b = 0) := by
  let A := realPart D e₀ e₁ b c
  let A' := realPart D e₀ e₁ b' c'
  have hz (i : Fin 4) :
      (4*D^2*a-4*D^2*a')*t i^3 +
      (6*D^2*a^2-2*D*A-(6*D^2*a'^2-2*D*A'))*t i^2 +
      (4*D^2*a^3-4*D*A*a-b-(4*D^2*a'^3-4*D*A'*a'-b'))*t i +
      (normForm D e₀ e₁ a b c-v-(normForm D e₀ e₁ a' b' c'-v')) = 0 := by
    have hh := h i
    dsimp [normForm, A, A'] at hh ⊢
    linear_combination hh
  obtain ⟨h₃,hq,hl,_⟩ := Erdos714Parabolas.cubic_coefficients t _ _ _ _ hz
  have h₄ : (4 : F) ≠ 0 := by
    convert mul_ne_zero h₂ h₂ using 1; norm_num
  have ha0 : (4*D^2)*(a-a') = 0 := by linear_combination h₃
  have ha : a = a' := sub_eq_zero.mp
    ((mul_eq_zero.mp ha0).resolve_left (mul_ne_zero h₄ (pow_ne_zero _ hD)))
  subst a'
  have hA0 : (2*D)*(A-A') = 0 := by linear_combination -hq
  have hA : A = A' := sub_eq_zero.mp
    ((mul_eq_zero.mp hA0).resolve_left (mul_ne_zero h₂ hD))
  have hb : b = b' := by rw [hA] at hl; linear_combination -hl
  subst b'
  have hfactor : D*((c-c')*(e₀*(c+c')+2*e₁*b)) = 0 := by
    dsimp [A,A',realPart] at hA
    linear_combination hA
  exact ⟨rfl,rfl, (mul_eq_zero.mp ((mul_eq_zero.mp hfactor).resolve_left hD)).imp
    sub_eq_zero.mp id⟩

/-- In particular, four distinct rows in this scalar direction have at most
two common columns. This is a local statement, not freeness of the whole graph. -/
theorem scalar_no_three (D e₀ e₁ : F) (hD : D ≠ 0) (h₂ : (2 : F) ≠ 0)
    (he₀ : e₀ ≠ 0) (t : Fin 4 ↪ F) (w : Fin 4 → F)
    (R : Fin 3 ↪ (Fin 4 → F)) :
    ¬ ∀ i j, normForm D e₀ e₁ (t i+R j 0) (R j 1) (R j 2) =
      w i+R j 3+t i*R j 1 := by
  intro h
  have hp (j k : Fin 3) : R j 0 = R k 0 ∧ R j 1 = R k 1 ∧
      (R j 2 = R k 2 ∨ e₀*(R j 2+R k 2)+2*e₁*R j 1=0) := by
    apply scalar_profile D e₀ e₁ hD h₂ t
      (R j 0) (R j 1) (R j 2) (R j 3) (R k 0) (R k 1) (R k 2) (R k 3)
    intro i
    have hj := h i j
    have hk := h i k
    rw [add_comm (t i)] at hj hk
    linear_combination hj-hk
  have hc (j k : Fin 3) (hne : j ≠ k) : R j 2 ≠ R k 2 := by
    intro he
    apply hne
    apply R.injective
    obtain ⟨ha,hb,_⟩ := hp j k
    have hw : R j 3=R k 3 := by
      have hj := h 0 j
      have hk := h 0 k
      rw [ha,hb,he] at hj
      linear_combination hk-hj
    funext i
    fin_cases i <;> assumption
  have h₁ := (hp 0 1).2.2.resolve_left (hc 0 1 (by decide))
  have h₂' := (hp 0 2).2.2.resolve_left (hc 0 2 (by decide))
  have he : e₀*(R 1 2-R 2 2)=0 := by linear_combination h₁-h₂'
  exact hc 1 2 (by decide) (sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left he₀))

lemma row_card [Fintype F] (D e₀ e₁ : F) (x : Fin 4 → F) :
    (Finset.univ.filter (fun y : Fin 4 → F =>
      normForm D e₀ e₁ (x 0+y 0) (x 1+y 1) (x 2+y 2) =
        x 3+y 3+x 0*y 1-x 1*y 0)).card = Fintype.card F^3 := by
  classical
  have hcard : Fintype.card F^3 = (Finset.univ : Finset (Fin 3 → F)).card := by simp
  rw [hcard]
  apply Finset.card_bij (fun y _ => ![y 0,y 1,y 2])
  · intro y _; exact Finset.mem_univ _
  · intro y hy z hz he
    have h₀ : y 0=z 0 := congrFun he 0
    have h₁ : y 1=z 1 := congrFun he 1
    have h₂ : y 2=z 2 := congrFun he 2
    have h₃ : y 3=z 3 := by
      have hy' := (Finset.mem_filter.mp hy).2
      have hz' := (Finset.mem_filter.mp hz).2
      rw [h₀,h₁,h₂] at hy'
      linear_combination hz'-hy'
    funext i; fin_cases i <;> assumption
  · intro y _
    refine ⟨![y 0,y 1,y 2,
      normForm D e₀ e₁ (x 0+y 0) (x 1+y 1) (x 2+y 2)-x 3-x 0*y 1+x 1*y 0], ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      constructor
      · exact Finset.mem_univ _
      · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
        ring
    · funext i; fin_cases i <;> rfl

omit [Field F] in
theorem vertex_count [Fintype F] :
    Fintype.card ((Fin 4 → F) ⊕ (Fin 4 → F)) = 2*Fintype.card F^4 := by
  simp only [Fintype.card_sum,Fintype.card_fun,Fintype.card_fin]
  ring

theorem edge_count [Fintype F] (D e₀ e₁ : F) :
    (graph D e₀ e₁).edgeFinset.card = Fintype.card F^7 := by
  have he : graph D e₀ e₁ = Erdos714Packing.incidence (fun x : Fin 4 → F =>
      Finset.univ.filter (fun y : Fin 4 → F =>
        normForm D e₀ e₁ (x 0+y 0) (x 1+y 1) (x 2+y 2) =
          x 3+y 3+x 0*y 1-x 1*y 0)) := by
    ext x y
    cases x <;> cases y <;> simp [graph,Erdos714Packing.incidence]
  rw [he,Erdos714Packing.incidence_edges]
  simp_rw [row_card]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fun,Fintype.card_fin,
    nsmul_eq_mul,Nat.cast_id]
  ring

/-- Use a finite table without enumerating the whole ambient graph. -/
def tableCopy (D e₀ e₁ : F) (L R : Fin 4 → Fin 4 → F)
    (hL : Function.Injective L) (hR : Function.Injective R)
    (he : ∀ i j, normForm D e₀ e₁ (L i 0+R j 0) (L i 1+R j 1) (L i 2+R j 2) =
      L i 3+R j 3+L i 0*R j 1-L i 1*R j 0) :
    Copy (completeBipartiteGraph (Fin 4) (Fin 4)) (graph D e₀ e₁) := by
  let l : Fin 4 ↪ (Fin 4 → F) := ⟨L,hL⟩
  let r : Fin 4 ↪ (Fin 4 → F) := ⟨R,hR⟩
  refine ⟨⟨l.sumMap r, ?_⟩, (l.sumMap r).injective⟩
  intro x y h
  cases x with
  | inl i =>
    cases y with
    | inl j => simp at h
    | inr j => exact he i j
  | inr j =>
    cases y with
    | inl i => exact he i j
    | inr k => simp at h

def L3 : Fin 4 → Fin 4 → ZMod 3 :=
  ![![0,0,0,0],![1,0,0,0],![0,0,1,0],![0,0,2,0]]

def R3 : Fin 4 → Fin 4 → ZMod 3 :=
  ![![0,2,1,2],![1,0,0,1],![1,0,1,1],![1,0,2,1]]

theorem not_free_3 :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (graph (F := ZMod 3) 2 1 1) := by
  intro hf
  exact hf ⟨tableCopy 2 1 1 L3 R3 (by decide) (by decide) (by decide)⟩

instance : Fact (Nat.Prime 5) := ⟨by decide⟩
instance : Fact (Nat.Prime 7) := ⟨by decide⟩

def L5 : Fin 4 → Fin 4 → ZMod 5 :=
  ![![0,0,0,0],![1,0,0,0],![0,0,1,4],![0,0,3,0]]

def R5 : Fin 4 → Fin 4 → ZMod 5 :=
  ![![0,3,0,3],![0,4,1,3],![1,0,0,4],![2,0,1,4]]

theorem not_free_5 :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (graph (F := ZMod 5) 2 1 2) := by
  intro hf
  exact hf ⟨tableCopy 2 1 2 L5 R5 (by decide) (by decide) (by decide)⟩

def L7 : Fin 4 → Fin 4 → ZMod 7 :=
  ![![0,0,0,0],![1,0,0,0],![0,0,4,5],![0,0,6,5]]

def R7 : Fin 4 → Fin 4 → ZMod 7 :=
  ![![0,3,6,5],![0,4,6,5],![5,3,4,5],![6,3,0,3]]

theorem not_free_7 :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (graph (F := ZMod 7) 3 1 1) := by
  intro hf
  exact hf ⟨tableCopy 3 1 1 L7 R7 (by decide) (by decide) (by decide)⟩

end Erdos714NoncommutativeQuartic

#print axioms Erdos714NoncommutativeQuartic.scalar_profile
#print axioms Erdos714NoncommutativeQuartic.not_free_3
#print axioms Erdos714NoncommutativeQuartic.not_free_5
#print axioms Erdos714NoncommutativeQuartic.not_free_7

#print axioms Erdos714NoncommutativeQuartic.scalar_no_three
#print axioms Erdos714NoncommutativeQuartic.edge_count

#print axioms Erdos714NoncommutativeQuartic.coordinate_norm
#print axioms Erdos714NoncommutativeQuartic.coordinate_trace

#print axioms Erdos714NoncommutativeQuartic.vertex_count
