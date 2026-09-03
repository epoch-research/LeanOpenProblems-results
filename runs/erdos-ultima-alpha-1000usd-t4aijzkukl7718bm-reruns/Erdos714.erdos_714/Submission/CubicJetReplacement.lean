import FormalConjecturesUtil

/-! A characteristic-three obstruction to replacing cubic evaluation fibers
by quadratic-norm graphs. This does not settle Erdős 714. -/

set_option maxHeartbeats 3000000
noncomputable section
open Classical SimpleGraph
namespace Erdos714CubicJet
variable {F : Type*} [Field F] [CharP F 3]

abbrev Vertex (F : Type*) := F × F × F × F

def eval (f : Vertex F) (t : F) : F := f.1*t^3+f.2.1*t^2+f.2.2.1*t+f.2.2.2

/-- The sum of the quadratic coefficients is explicitly required to be nonzero.
The norm variable is also required to be nonzero. -/
def graph (δ : F) : SimpleGraph (Vertex F ⊕ Vertex F) where
  Adj f g := match f,g with
    | .inl f,.inr g | .inr g,.inl f =>
      f.1 ≠ 0 ∧ IsSquare f.1 ∧ g.1 ≠ 0 ∧ IsSquare g.1 ∧ f.2.1+g.2.1 ≠ 0 ∧
      ∃ t : F, eval f t+eval g t=0 ∧
        f.2.2.1+g.2.2.1-(f.2.1+g.2.1)*t ≠ 0 ∧
        (f.2.2.1+g.2.2.1-(f.2.1+g.2.1)*t)^2-δ*(f.2.1+g.2.1)^2=f.1*g.1
    | _,_ => False
  symm := by intro f g; cases f <;> cases g <;> simp_all
  loopless := by intro f; cases f <;> simp

private def sign (b : Bool) : F := if b then 1 else -1
omit [CharP F 3] in
private lemma sign_sq (b : Bool) : (sign b : F)^2=1 := by cases b <;> norm_num [sign]
omit [CharP F 3] in
private lemma sign_cube (b : Bool) : (sign b : F)^3=sign b := by cases b <;> norm_num [sign]
omit [CharP F 3] in
private lemma sign_ne_zero (b : Bool) : (sign b : F) ≠ 0 := by cases b <;> simp [sign]
private lemma two_ne_zero : (2 : F) ≠ 0 := by
  exact (CharP.cast_eq_zero_iff F 3 2).not.mpr (by decide)

private lemma sign_mul_injective {x : F} (hx : x ≠ 0) :
    Function.Injective (fun b : Bool => sign b*x) := by
  intro b c he
  have hh := mul_right_cancel₀ hx he
  cases b <;> cases c <;> try rfl
  all_goals
    exfalso
    have hz : (2 : F)=0 := by
      simp only [sign,Bool.false_eq_true,if_false,if_true] at hh
      first | linear_combination hh | linear_combination -hh
    exact two_ne_zero hz

def center (A B v : F) : F := -(A+1)*v^2/B^2
def constant (δ A B v : F) : F :=
  -(A+1)*(center A B v)^3/B^3+(center A B v)^2/B-δ*B-A/B+v^2/B

lemma edge_formula (δ : F) {A B H v w c d : F} (hB : B ≠ 0) (hH : H ≠ 0)
    (hA : A ≠ 0) (hsA : IsSquare A) (hN : H^2-δ*B^2=A)
    (hw : (A+1)*H^3=w*B^3) (hc : c^2=v^2) (hd : d^3=d) (hd0 : d ≠ 0)
    (hd2 : d^2=1) :
    (graph δ).Adj (.inl (1,0,c,d*w)) (.inr (A,B,center A B v,constant δ A B v)) := by
  let C := center A B v
  let D := constant δ A B v
  let t := (c+C-d*H)/B
  have ht : c+C-B*t=d*H := by dsimp [t]; field_simp; ring
  refine ⟨one_ne_zero,IsSquare.one,hA,hsA,by simpa using hB,t,?_,?_,?_⟩
  · change eval (1,0,c,d*w) t+eval (A,B,C,D) t=0
    dsimp [eval,t,C,D,constant,center]
    field_simp
    -- All cancellations are polynomial identities in characteristic three.
    linear_combination (norm := (ring_nf; reduce_mod_char!))
      B^6*(A+1)*c*(hc) - B^8*hc - B^6*d*(hw) + B^8*(hN) + B^8*H^2*(hd2)
      - B^6*(A+1)*H^3*(hd)
  · change c+C-(0+B)*t ≠ 0
    rw [zero_add,ht]
    exact mul_ne_zero hd0 hH
  · change (c+C-(0+B)*t)^2-δ*(0+B)^2=1*A
    rw [zero_add,ht,mul_pow,hd2,one_mul,one_mul]
    exact hN

private def row (v w : F) (i : Bool × Bool) : Vertex F := (1,0,sign i.1*v,sign i.2*w)
private def column (δ : F) (A B : Fin 2 → F) (v : F) (j : Fin 2 × Bool) : Vertex F :=
  (A j.1,sign j.2*B j.1,center (A j.1) (sign j.2*B j.1) v,
    constant δ (A j.1) (sign j.2*B j.1) v)

/-- Two profile columns and both signs of their quadratic coefficients give
four actual columns against the paired cubic rows. -/
def profileCopy (δ : F) (A B H : Fin 2 → F) (v w : F)
    (hv : v ≠ 0) (hw0 : w ≠ 0) (hAi : Function.Injective A)
    (hA : ∀ i, A i ≠ 0) (hsA : ∀ i, IsSquare (A i))
    (hB : ∀ i, B i ≠ 0) (hH : ∀ i, H i ≠ 0)
    (hN : ∀ i, (H i)^2-δ*(B i)^2=A i)
    (hw : ∀ i, (A i+1)*(H i)^3=w*(B i)^3) :
    Copy (completeBipartiteGraph (Fin 4) (Fin 4)) (graph (F := F) δ) := by
  have hr : Function.Injective (row v w) := by
    rintro ⟨i,j⟩ ⟨k,l⟩ he
    have hi : i=k := sign_mul_injective hv (congrArg (fun p : Vertex F => p.2.2.1) he)
    have hj : j=l := sign_mul_injective hw0 (congrArg (fun p : Vertex F => p.2.2.2) he)
    exact Prod.ext hi hj
  have hc : Function.Injective (column δ A B v) := by
    rintro ⟨i,b⟩ ⟨j,c⟩ he
    have hij : i=j := hAi (congrArg Prod.fst he)
    subst j
    have hbc : b=c := sign_mul_injective (hB i) (congrArg (fun p : Vertex F => p.2.1) he)
    cases hbc
    rfl
  have hedge (i : Bool × Bool) (j : Fin 2 × Bool) :
      (graph δ).Adj (.inl (row v w i)) (.inr (column δ A B v j)) := by
    apply edge_formula δ (B := sign j.2*B j.1) (H := sign j.2*H j.1)
      (mul_ne_zero (sign_ne_zero _) (hB _)) (mul_ne_zero (sign_ne_zero _) (hH _))
      (hA _) (hsA _)
    · rw [mul_pow,mul_pow,sign_sq,one_mul,one_mul]; exact hN _
    · rw [mul_pow,mul_pow,sign_cube]
      linear_combination sign j.2 * hw j.1
    · rw [mul_pow,sign_sq,one_mul]
    · exact sign_cube _
    · exact sign_ne_zero _
    · exact sign_sq _
  let eL : Fin 4 ≃ Bool × Bool :=
    (finCongr (by simp : 4=Fintype.card (Bool × Bool))).trans (Fintype.equivFin _).symm
  let eR : Fin 4 ≃ Fin 2 × Bool :=
    (finCongr (by simp : 4=Fintype.card (Fin 2 × Bool))).trans (Fintype.equivFin _).symm
  let L := eL.toEmbedding.trans ⟨row v w,hr⟩
  let R := eR.toEmbedding.trans ⟨column δ A B v,hc⟩
  refine ⟨⟨L.sumMap R,?_⟩,(L.sumMap R).injective⟩
  intro p q hpq
  cases p with
  | inl i =>
    cases q with
    | inl j => simp at hpq
    | inr j => exact hedge (eL i) (eR j)
  | inr j =>
    cases q with
    | inr i => simp at hpq
    | inl i => exact hedge (eL i) (eR j)

/-- A rational profile family; all four column weights are squares. -/
def parameterCopy {z ρ : F} (hz : z ≠ 0) (hρ0 : ρ ≠ 0)
    (hρ : ρ^2=1+z^2) (hz2 : z^2 ≠ 1) :
    Copy (completeBipartiteGraph (Fin 4) (Fin 4)) (graph (F := F) (-1)) := by
  let d := 1+z^2
  have hd : d ≠ 0 := by rw [show d=ρ^2 from hρ.symm]; exact pow_ne_zero 2 hρ0
  have hd' : 1+z^2 ≠ 0 := hd
  let A : Fin 2 → F := ![z^2/d,1/d]
  let B : Fin 2 → F := ![z/d,1/d]
  let H : Fin 2 → F := ![z^2/d,-z/d]
  let w := (1-z^2)*z^3/d
  have hw0 : w ≠ 0 := div_ne_zero
    (mul_ne_zero (sub_ne_zero.mpr hz2.symm) (pow_ne_zero 3 hz)) hd
  have hAi : Function.Injective A := by
    intro i j he
    fin_cases i <;> fin_cases j <;> try rfl
    all_goals
      exfalso
      apply hz2
      apply (div_left_inj' hd).mp
      first | exact he | exact he.symm
  have hA (i) : A i ≠ 0 := by
    fin_cases i
    · exact div_ne_zero (pow_ne_zero 2 hz) hd
    · exact div_ne_zero one_ne_zero hd
  have hsA (i) : IsSquare (A i) := by
    fin_cases i
    · refine ⟨z/ρ,?_⟩
      change z^2/d=(z/ρ)*(z/ρ)
      rw [show d=ρ^2 from hρ.symm]
      ring
    · refine ⟨1/ρ,?_⟩
      change 1/d=(1/ρ)*(1/ρ)
      rw [show d=ρ^2 from hρ.symm]
      ring
  have hB (i) : B i ≠ 0 := by
    fin_cases i
    · exact div_ne_zero hz hd
    · exact div_ne_zero one_ne_zero hd
  have hH (i) : H i ≠ 0 := by
    fin_cases i
    · exact div_ne_zero (pow_ne_zero 2 hz) hd
    · exact div_ne_zero (neg_ne_zero.mpr hz) hd
  have hN (i) : (H i)^2-(-1)*(B i)^2=A i := by
    fin_cases i <;> dsimp [A,B,H,d] <;> field_simp [hd'] <;> ring
  have hw (i) : (A i+1)*(H i)^3=w*(B i)^3 := by
    fin_cases i <;> dsimp [A,B,H,w,d] <;> field_simp [hd'] <;> ring_nf <;> reduce_mod_char!
    ring
  exact profileCopy (-1) A B H 1 w one_ne_zero hw0 hAi hA hsA hB hH hN hw

/-- The conic parameter exists over every finite field in the relevant odd
characteristic-three family, except the smallest field. -/
lemma exists_parameter [Fintype F] (hsize : 3 < Fintype.card F)
    (hns : ¬ IsSquare (-1 : F)) :
    ∃ z ρ : F, z ≠ 0 ∧ ρ ≠ 0 ∧ ρ^2=1+z^2 ∧ z^2 ≠ 1 := by
  have hbad : ({0,1,-1} : Finset F).card < (Finset.univ : Finset F).card := by
    exact lt_of_le_of_lt Finset.card_le_three (by simpa using hsize)
  obtain ⟨t,_,ht⟩ := Finset.exists_mem_notMem_of_card_lt_card hbad
  have ht' : t ≠ 0 ∧ t ≠ 1 ∧ t ≠ -1 := by simpa using ht
  let z := t-t⁻¹
  let ρ := t+t⁻¹
  have hz : z ≠ 0 := by
    intro hh
    have he : t^2=1 := by
      have he' := congrArg (fun x : F => x*t) hh
      dsimp [z] at he'
      field_simp [ht'.1] at he'
      linear_combination he'
    exact (sq_eq_one_iff.mp he).elim ht'.2.1 ht'.2.2
  have hρ0 : ρ ≠ 0 := by
    intro hh
    apply hns
    refine ⟨t,?_⟩
    have he := congrArg (fun x : F => x*t) hh
    dsimp [ρ] at he
    field_simp [ht'.1] at he
    linear_combination -he
  have hρ : ρ^2=1+z^2 := by
    dsimp [ρ,z]
    field_simp [ht'.1]
    ring_nf
    reduce_mod_char!
    ring
  refine ⟨z,ρ,hz,hρ0,hρ,?_⟩
  intro he
  apply hns
  refine ⟨ρ,?_⟩
  linear_combination (norm := (ring_nf; reduce_mod_char!)) -hρ-he

/-- The local quadratic-norm replacements do not combine to a K44-free graph,
even after requiring square weights and deleting the zero coefficient-sum and
zero norm-variable edges. This is a construction obstruction, not Erdős 714. -/
theorem finite_field_not_free [Fintype F] (hsize : 3 < Fintype.card F)
    (hns : ¬ IsSquare (-1 : F)) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph (F := F) (-1)) := by
  obtain ⟨z,ρ,hz,hρ0,hρ,hz2⟩ := exists_parameter hsize hns
  intro hf
  exact hf ⟨parameterCopy hz hρ0 hρ hz2⟩

/-- The same paired profiles work for arbitrary quadratic-norm parameters. -/
def generalParameterCopy (δ : F) {s t z ρ : F}
    (hs : s ≠ 0) (ht : t ≠ 0) (hz : z ≠ 0) (hρ0 : ρ ≠ 0)
    (hst : s^2+t^2=1) (hne : s^2 ≠ t^2) (hα : s^2+1 ≠ 0)
    (hρ : ρ^2=z^2-δ) :
    Copy (completeBipartiteGraph (Fin 4) (Fin 4)) (graph δ) := by
  let A : Fin 2 → F := ![s^2,t^2]
  let B : Fin 2 → F := ![s/ρ,t/ρ]
  let H : Fin 2 → F := ![s*z/ρ,-t*z/ρ]
  let w := (s^2+1)*z^3
  have hw0 : w ≠ 0 := mul_ne_zero hα (pow_ne_zero 3 hz)
  have hAi : Function.Injective A := by
    intro i j he
    fin_cases i <;> fin_cases j <;> try rfl
    · exact (hne he).elim
    · exact (hne he.symm).elim
  have hA (i) : A i ≠ 0 := by fin_cases i <;> first | exact pow_ne_zero 2 hs | exact pow_ne_zero 2 ht
  have hsA (i) : IsSquare (A i) := by fin_cases i <;> exact IsSquare.sq _
  have hB (i) : B i ≠ 0 := by
    fin_cases i
    · exact div_ne_zero hs hρ0
    · exact div_ne_zero ht hρ0
  have hH (i) : H i ≠ 0 := by
    fin_cases i
    · exact div_ne_zero (mul_ne_zero hs hz) hρ0
    · exact div_ne_zero (mul_ne_zero (neg_ne_zero.mpr ht) hz) hρ0
  have hN (i) : (H i)^2-δ*(B i)^2=A i := by
    fin_cases i <;> dsimp [H,B,A] <;> field_simp
    · linear_combination -hρ
    · linear_combination -hρ
  have hw (i) : (A i+1)*(H i)^3=w*(B i)^3 := by
    fin_cases i <;> dsimp [A,H,w,B] <;> field_simp
    linear_combination (norm := (ring_nf; reduce_mod_char!)) -hst
  exact profileCopy δ A B H 1 w one_ne_zero hw0 hAi hA hsA hB hH hN hw

/-- Every nonsquare choice of the norm parameter fails, not just δ=-1. -/
theorem all_nonsquare_parameters [Fintype F] (hsize : 3 < Fintype.card F)
    (hns : ¬ IsSquare (-1 : F)) (δ : F) (hδ : ¬ IsSquare δ) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph δ) := by
  obtain ⟨z₀,ρ₀,hz₀,hρ₀,hrel,hz2⟩ := exists_parameter hsize hns
  let s := z₀/ρ₀
  let t := 1/ρ₀
  have hs : s ≠ 0 := div_ne_zero hz₀ hρ₀
  have ht : t ≠ 0 := div_ne_zero one_ne_zero hρ₀
  have hst : s^2+t^2=1 := by
    dsimp [s,t]
    field_simp
    linear_combination -hrel
  have hne : s^2 ≠ t^2 := by
    intro he
    apply hz2
    dsimp [s,t] at he
    field_simp at he
    exact he
  have hα : s^2+1 ≠ 0 := by
    intro he
    exact hns ⟨s,by linear_combination -he⟩
  obtain ⟨z,ρ,hz,hρ0,hρ⟩ : ∃ z ρ : F, z ≠ 0 ∧ ρ ≠ 0 ∧ ρ^2=z^2-δ := by
    by_cases hd : δ = -1
    · refine ⟨z₀,ρ₀,hz₀,hρ₀,?_⟩
      rw [hd]
      linear_combination hrel
    · refine ⟨1+δ,1-δ,?_,?_,?_⟩
      · intro he
        apply hd
        linear_combination he
      · intro he
        apply hδ
        refine ⟨1,?_⟩
        linear_combination -he
      · linear_combination (norm := (ring_nf; reduce_mod_char!))
  intro hf
  exact hf ⟨generalParameterCopy δ hs ht hz hρ0 hst hne hα hρ⟩

/-- An explicit unbounded field-size family satisfying all arithmetic hypotheses. -/
theorem odd_degree_not_free [Fintype F] (k : ℕ)
    (hcard : Fintype.card F=3^(2*k+3)) (δ : F) (hδ : ¬ IsSquare δ) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph δ) := by
  have hsize : 3 < Fintype.card F := by
    have hh : (3 : ℕ)^3 ≤ 3^(2*k+3) := pow_le_pow_right' (by decide) (by omega)
    rw [hcard]
    norm_num at hh ⊢
    omega
  have hmod : Fintype.card F%4=3 := by
    rw [hcard,pow_add,pow_mul,Nat.mul_mod,Nat.pow_mod]
    norm_num
  have hns : ¬ IsSquare (-1 : F) := by
    rw [FiniteField.isSquare_neg_one_iff,hmod]
    simp
  exact all_nonsquare_parameters hsize hns δ hδ

end Erdos714CubicJet
#print axioms Erdos714CubicJet.edge_formula
#print axioms Erdos714CubicJet.profileCopy
#print axioms Erdos714CubicJet.parameterCopy
#print axioms Erdos714CubicJet.finite_field_not_free

#print axioms Erdos714CubicJet.all_nonsquare_parameters

#print axioms Erdos714CubicJet.odd_degree_not_free
