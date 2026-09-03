import Submission.TernaryASParameter
import Submission.QuinticNormProduct

/-!
A uniform K44 in cubic characteristic-three norm graphs with ALL FOUR ROW
WEIGHTS EQUAL. The actual norm equations follow from an Artin--Schreier
power basis, and the parameter exists in every base field of order >9.
Consequently any weight law with one full nonzero row fails in this family.
This is a construction obstruction, not a disproof of Erdős 714.
-/
noncomputable section
open Classical Polynomial SimpleGraph
set_option maxHeartbeats 4000000
namespace Erdos714EqualRowCubicNorm
variable {F : Type*} [Field F] [CharP F 3]
abbrev V (F : Type*) := Fin 3 → F

def form (d : F) (x : V F) : F :=
  x 0^3-x 0^2*x 2+x 0*x 2^2-x 0*x 1^2+
    d*x 1^3-d*x 1*x 2^2+d^2*x 2^3

def rows (d : F) : Fin 4 → V F := ![![0,0,0],![1,0,0],![-1,0,0],![0,0,-d]]
def cols (d v : F) : Fin 4 → V F :=
  ![![d+d^2,-1,0],![d-d^2,-1,0],![d+d*v,1,0],![d-d*v,1,0]]

lemma neg_one_ne_one : (-1:F) ≠ 1 := by
  intro h
  have h3 : (3:F)=0 := CharP.cast_eq_zero F 3
  have hh : (1:F)=0 := by linear_combination h3+h
  exact one_ne_zero hh

lemma add_ne_sub (a b : F) (hb : b ≠ 0) : a+b ≠ a-b := by
  intro h
  have h3 : (3:F)=0 := CharP.cast_eq_zero F 3
  apply hb
  linear_combination b*h3-h

lemma rows_injective {d : F} (hd : d ≠ 0) : Function.Injective (rows d) := by
  intro i j h
  have h0 := congrFun h 0
  have h2 := congrFun h 2
  fin_cases i <;> fin_cases j <;>
    simp [rows,hd,neg_one_ne_one,Ne.symm neg_one_ne_one] at h0 h2 ⊢

lemma cols_injective {d v : F} (hd : d ≠ 0) (hv : v ≠ 0) :
    Function.Injective (cols d v) := by
  have hsq := add_ne_sub d (d^2) (pow_ne_zero 2 hd)
  have hprod := add_ne_sub d (d*v) (mul_ne_zero hd hv)
  intro i j h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  fin_cases i <;> fin_cases j <;>
    simp [cols,hsq,Ne.symm hsq,hprod,Ne.symm hprod,neg_one_ne_one,
      Ne.symm neg_one_ne_one] at h0 h1 ⊢

omit [CharP F 3] in
lemma cols_ne_zero (d v : F) (j : Fin 4) : cols d v j ≠ 0 := by
  intro h
  have hh := congrFun h 1
  fin_cases j <;> simp [cols] at hh

/-- Every row sees the same norm at each column. No weight operation occurs
in this identity, and all four columns are explicitly exhibited. -/
lemma coordinate_edges (d v : F) (hv : v^2=d^2-1) (i j : Fin 4) :
    form d (rows d i+cols d v j)=form d (cols d v j) := by
  fin_cases i <;> fin_cases j <;>
    simp [form,rows,cols] <;> ring_nf <;> reduce_mod_char! <;> ring_nf
  all_goals
    try rw [hv]
    try ring_nf
    reduce_mod_char!

section Semantics
variable {E : Type*} [Field E] [Algebra F E]

def element (z : E) (x : V F) : E :=
  Erdos714QuinticNormProduct.element z (x 0) (x 1) (x 2)

omit [CharP F 3] in
lemma element_add (z : E) (x y : V F) : element z (x+y)=element z x+element z y := by
  simp only [element,Erdos714QuinticNormProduct.element,Pi.add_apply,map_add]
  ring

omit [CharP F 3] in
lemma element_zero (z : E) : element z (0 : V F)=0 := by
  simp [element,Erdos714QuinticNormProduct.element]

omit [CharP F 3] in
lemma element_sum (z : E) (B : Module.Basis (Fin 3) F E)
    (hB : ∀ i, B i=z^(i:ℕ)) (x : V F) : element z x=∑ i, x i • B i := by
  simp [element,Erdos714QuinticNormProduct.element,Fin.sum_univ_three,hB,Algebra.smul_def]

omit [CharP F 3] in
lemma element_injective (z : E) (B : Module.Basis (Fin 3) F E)
    (hB : ∀ i, B i=z^(i:ℕ)) : Function.Injective (element (F := F) z) := by
  intro x y h
  rw [element_sum z B hB,element_sum z B hB,
    ← B.equivFun_symm_apply,← B.equivFun_symm_apply] at h
  exact B.equivFun.symm.injective h

/-- The formula used above is the actual algebra norm, not just a surrogate. -/
lemma norm_element (d : F) (z : E) (hz : z^3=z+algebraMap F E d)
    (B : Module.Basis (Fin 3) F E) (hB : ∀ i, B i=z^(i:ℕ)) (x : V F) :
    Algebra.norm F (element z x)=form d x := by
  rw [Algebra.norm_eq_matrix_det B,element,
    Erdos714QuinticNormProduct.leftMulMatrix_element d z hz B hB,Matrix.det_fin_three]
  simp [Erdos714QuinticNormProduct.multiplicationMatrix,form]
  ring_nf
  reduce_mod_char!
  ring

omit [CharP F 3] in
lemma column_norm_ne_zero (d v : F) (z : E) (B : Module.Basis (Fin 3) F E)
    (hB : ∀ i, B i=z^(i:ℕ)) (j : Fin 4) :
    Algebra.norm F (element z (cols d v j)) ≠ 0 := by
  letI : FiniteDimensional F E := Module.Finite.of_basis B
  apply Algebra.norm_ne_zero_iff.mpr
  intro h
  exact cols_ne_zero d v j (element_injective z B hB (h.trans (element_zero z).symm))

/-- A geometric rectangle with all four row radii equal at each column. -/
theorem power_basis_rectangle (d v : F) (hd : d ≠ 0) (hv : v ≠ 0)
    (hv2 : v^2=d^2-1) (z : E) (hz : z^3=z+algebraMap F E d)
    (B : Module.Basis (Fin 3) F E) (hB : ∀ i, B i=z^(i:ℕ)) :
    ∃ l r : Fin 4 ↪ E, (∀ j, Algebra.norm F (r j) ≠ 0) ∧
      ∀ i j, Algebra.norm F (l i+r j)=Algebra.norm F (r j) := by
  let l : Fin 4 ↪ E := ⟨fun i => element z (rows d i),
    (element_injective z B hB).comp (rows_injective hd)⟩
  let r : Fin 4 ↪ E := ⟨fun j => element z (cols d v j),
    (element_injective z B hB).comp (cols_injective hd hv)⟩
  refine ⟨l,r,column_norm_ne_zero d v z B hB,?_⟩
  intro i j
  change Algebra.norm F (element z (rows d i)+element z (cols d v j))=
    Algebra.norm F (element z (cols d v j))
  rw [← element_add,norm_element d z hz B hB,coordinate_edges d v hv2,
    norm_element d z hz B hB]

/-- The parameter and its actual power basis exist in every finite base
field of characteristic three and order >9, in every cubic extension. -/
theorem exists_equal_row_rectangle [Fintype F] (hq : 9 < Fintype.card F)
    (hdim : Module.finrank F E=3) :
    ∃ l r : Fin 4 ↪ E, (∀ j, Algebra.norm F (r j) ≠ 0) ∧
      ∀ i j, Algebra.norm F (l i+r j)=Algebra.norm F (r j) := by
  obtain ⟨d,v,hd,hv,hv2,hirr⟩ := Erdos714TernaryASParameter.exists_parameter hq
  obtain ⟨z,hz,B,hB⟩ := Erdos714QuinticNormProduct.exists_cubic_power_basis hdim d hirr
  exact power_basis_rectangle d v hd hv hv2 z hz B hB

end Semantics

section WeightLaws
variable {E A D : Type*} [Field E] [Algebra F E]

/-- The weight law is arbitrary; every displayed norm value is nonzero. -/
def graph (H : A → D → F) : SimpleGraph ((E × A) ⊕ (E × D)) where
  Adj u v := match u,v with
    | .inl x,.inr y => Algebra.norm F (x.1+y.1)=H x.2 y.2 ∧ H x.2 y.2 ≠ 0
    | .inr y,.inl x => Algebra.norm F (x.1+y.1)=H x.2 y.2 ∧ H x.2 y.2 ≠ 0
    | _,_ => False
  symm := by intro u v; cases u <;> cases v <;> exact id
  loopless := by intro u; cases u <;> exact not_false

/-- One full nonzero row of H is enough. It need not be a group operation,
commutative, associative, or independent of the field size. -/
theorem not_free_of_full_row [Fintype F] (hq : 9 < Fintype.card F)
    (hdim : Module.finrank F E=3) (H : A → D → F) (a : A)
    (hrow : ∀ w : F, w ≠ 0 → ∃ b : D, H a b=w) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph (E := E) H) := by
  obtain ⟨l,r,hn,he⟩ := exists_equal_row_rectangle hq hdim
  choose b hb using fun j : Fin 4 => hrow (Algebra.norm F (r j)) (hn j)
  let L : Fin 4 ↪ E × A := ⟨fun i => (l i,a),by
    intro i j h; exact l.injective (congrArg Prod.fst h)⟩
  let R : Fin 4 ↪ E × D := ⟨fun j => (r j,b j),by
    intro i j h; exact r.injective (congrArg Prod.fst h)⟩
  have hedge (i j : Fin 4) : (graph (E := E) H).Adj (.inl (L i)) (.inr (R j)) := by
    change Algebra.norm F (l i+r j)=H a (b j) ∧ H a (b j) ≠ 0
    rw [hb]
    exact ⟨he i j,hn j⟩
  intro hfree
  apply hfree
  refine ⟨⟨⟨L.sumMap R,?_⟩,(L.sumMap R).injective⟩⟩
  intro u v h
  cases u with
  | inl i =>
    cases v with
    | inl j => simp at h
    | inr j => exact hedge i j
  | inr i =>
    cases v with
    | inl j => exact hedge j i
    | inr j => simp at h

end WeightLaws
end Erdos714EqualRowCubicNorm

#print axioms Erdos714EqualRowCubicNorm.coordinate_edges
#print axioms Erdos714EqualRowCubicNorm.norm_element
#print axioms Erdos714EqualRowCubicNorm.power_basis_rectangle
#print axioms Erdos714EqualRowCubicNorm.exists_equal_row_rectangle
#print axioms Erdos714EqualRowCubicNorm.not_free_of_full_row
