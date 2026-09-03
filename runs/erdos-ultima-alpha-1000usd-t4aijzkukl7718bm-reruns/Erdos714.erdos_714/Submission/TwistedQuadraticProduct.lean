import Submission.QuinticNormProduct
import Submission.Coding

/-! An actual trace-based code obstruction. This does not settle Erdős714. -/
noncomputable section
open Classical Finset SimpleGraph Polynomial
set_option maxHeartbeats 4000000
namespace Erdos714TwistedQuadraticProduct
open Erdos714QuinticNormProduct
variable {F E : Type*} [Field F] [Field E] [CharP F 3] [Algebra F E]

abbrev Vec (F : Type*) := Fin 3 → F

def el (z : E) (v : Vec F) : E := element z (v 0) (v 1) (v 2)

def vmul (v w : Vec F) : Vec F :=
  ![v 0*w 0-v 1*w 2-v 2*w 1,
    v 0*w 1+v 1*w 0+v 1*w 2+v 2*w 1-v 2*w 2,
    v 0*w 2+v 1*w 1+v 2*w 0+v 2*w 2]

omit [CharP F 3] in
lemma el_mul (z : E) (hz : z^3=z-1) (v w : Vec F) :
    el z v * el z w = el z (vmul v w) := by
  have hz4 : z^4=z^2-z := by calc
    _ = z^3*z := by ring
    _ = _ := by rw [hz]; ring
  dsimp [el,element,vmul]
  simp only [map_add,map_sub,map_mul]
  ring_nf
  rw [hz4,hz]
  ring

omit [CharP F 3] in
lemma el_injective (z : E) (B : Module.Basis (Fin 3) F E)
    (hB : ∀ i, B i = z^(i : ℕ)) : Function.Injective (el (F := F) z) := by
  have he (v : Vec F) : el z v = ∑ i, v i • B i := by
    simp only [el,element,Fin.sum_univ_three,hB,Algebra.smul_def]
    norm_num
  intro v w h
  funext i
  have hh := congrArg (fun x => B.repr x i) h
  fin_cases i <;> simpa [he,Fin.sum_univ_three] using hh

def kernel (z x : E) : F :=
  Algebra.trace F E (x^2)+Algebra.trace F E x+(Algebra.trace F E (z*x))^3

def coordinateKernel (v : Vec F) : F := v 0*v 2-(v 1)^2-(v 2)^2-v 2-(v 1)^3

lemma kernel_el (z : E) (hz : z^3=z-1)
    (B : Module.Basis (Fin 3) F E) (hB : ∀ i, B i=z^(i : ℕ)) (v : Vec F) :
    kernel z (el z v) = coordinateKernel v := by
  have ht (w : Vec F) : Algebra.trace F E (el z w) = -w 2 := by
    exact trace_element (-1) z (by simpa [sub_eq_add_neg] using hz) B hB _ _ _
  have hez : z = el (F := F) z ![0,1,0] := by simp [el,element]
  have hzx : z*el z v = el z (vmul ![0,1,0] v) := by
    calc
      _ = el z ![0,1,0]*el z v := by rw [← hez]
      _ = _ := el_mul z hz _ _
  unfold kernel
  rw [pow_two,el_mul z hz,hzx]
  simp only [ht]
  dsimp [coordinateKernel,vmul]
  apply sub_eq_zero.mp
  ring_nf
  reduce_mod_char!

def leftVec : Fin 4 → Vec F := ![![1,0,0],![-1,0,0],![0,1,0],![-1,1,1]]
def rightVec : Fin 4 → Vec F := ![![0,1,0],![0,0,1],![-1,1,0],![1,-1,-1]]
def leftTag : Fin 4 → F := ![0,1,0,1]
def rightTag : Fin 4 → F := ![1,1,1,-1]

lemma neg_one_ne_one : (-1 : F) ≠ 1 := by
  intro h
  have h3 : (3 : F)=0 := CharP.cast_eq_zero F 3
  have h0 : (1 : F)=0 := by linear_combination h3+h
  exact one_ne_zero h0

lemma left_injective : Function.Injective (leftVec (F := F)) := by
  intro i j h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  fin_cases i <;> fin_cases j <;>
    simp [leftVec,neg_one_ne_one,Ne.symm neg_one_ne_one] at h0 h1 h2 ⊢

lemma right_injective : Function.Injective (rightVec (F := F)) := by
  intro i j h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  fin_cases i <;> fin_cases j <;>
    simp [rightVec,neg_one_ne_one,Ne.symm neg_one_ne_one] at h0 h1 h2 ⊢

omit [CharP F 3] in
lemma left_ne_zero (i : Fin 4) : leftVec (F := F) i ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  fin_cases i <;> simp [leftVec] at h0 h1

omit [CharP F 3] in
lemma right_ne_zero (i : Fin 4) : rightVec (F := F) i ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  fin_cases i <;> simp [rightVec] at h0 h1 h2

lemma coordinate_edges (i j : Fin 4) :
    coordinateKernel (vmul (leftVec i) (rightVec j))+leftTag i = rightTag (F := F) j := by
  fin_cases i <;> fin_cases j <;>
    dsimp [coordinateKernel,vmul,leftVec,rightVec,leftTag,rightTag]
  all_goals apply sub_eq_zero.mp
  all_goals ring_nf
  all_goals reduce_mod_char!

variable [Fintype E]

def code (z : E) (r : Eˣ × F) (x : Eˣ) : F := kernel z ((r.1 : E)*(x : E))+r.2

def graph (z : E) : SimpleGraph ((Eˣ × F) ⊕ (Eˣ × F)) := Erdos714Coding.graph (code z)

/-- Every coordinate and symbol is retained; point coordinates must be NONZERO. -/
def copy (z : E) (hz : z^3=z-1) (B : Module.Basis (Fin 3) F E)
    (hB : ∀ i, B i=z^(i : ℕ)) :
    Copy (completeBipartiteGraph (Fin 4) (Fin 4)) (graph (F := F) z) := by
  have hz0 : el z (0 : Vec F)=0 := by simp [el,element]
  have hL0 (i : Fin 4) : el z (leftVec (F := F) i) ≠ 0 := by
    intro h
    exact left_ne_zero i (el_injective z B hB (h.trans hz0.symm))
  have hR0 (i : Fin 4) : el z (rightVec (F := F) i) ≠ 0 := by
    intro h
    exact right_ne_zero i (el_injective z B hB (h.trans hz0.symm))
  let L : Fin 4 → Eˣ × F := fun i => (Units.mk0 (el z (leftVec i)) (hL0 i),leftTag i)
  let R : Fin 4 → Eˣ × F := fun i => (Units.mk0 (el z (rightVec i)) (hR0 i),rightTag i)
  have hL : Function.Injective L := by
    intro i j h
    apply left_injective (F := F)
    apply el_injective z B hB
    exact congrArg (fun p : Eˣ × F => (p.1 : E)) h
  have hR : Function.Injective R := by
    intro i j h
    apply right_injective (F := F)
    apply el_injective z B hB
    exact congrArg (fun p : Eˣ × F => (p.1 : E)) h
  have he (i j : Fin 4) : code z (L i) (R j).1=(R j).2 := by
    change kernel z (el z (leftVec i)*el z (rightVec j))+leftTag i=rightTag j
    rw [el_mul z hz,kernel_el z hz B hB]
    exact coordinate_edges i j
  let le : Fin 4 ↪ Eˣ × F := ⟨L,hL⟩
  let re : Fin 4 ↪ Eˣ × F := ⟨R,hR⟩
  refine ⟨⟨le.sumMap re,?_⟩,(le.sumMap re).injective⟩
  intro u v huv
  cases u with
  | inl i =>
    cases v with
    | inl j => simp at huv
    | inr j => exact (Erdos714Coding.mem_symbols (code z) (L i) (R j).1 (R j).2).mpr (he i j)
  | inr j =>
    cases v with
    | inl i => exact (Erdos714Coding.mem_symbols (code z) (L i) (R j).1 (R j).2).mpr (he i j)
    | inr i => simp at huv

theorem not_free (z : E) (hz : z^3=z-1) (B : Module.Basis (Fin 3) F E)
    (hB : ∀ i, B i=z^(i : ℕ)) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph (F := F) z) :=
  fun h => h ⟨copy z hz B hB⟩

variable [Fintype F]

omit [CharP F 3] in
lemma edge_count (z : E) : (graph (F := F) z).edgeFinset.card =
    Fintype.card F*(Fintype.card E-1)^2 := by
  rw [graph,Erdos714Coding.edge_count]
  simp only [Fintype.card_prod,Fintype.card_units]
  ring

omit [Field F] [CharP F 3] [Algebra F E] in
lemma vertex_count : Fintype.card ((Eˣ × F) ⊕ (Eˣ × F)) =
    2*Fintype.card F*(Fintype.card E-1) := by
  simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_units]
  ring

/-- The power-basis condition is realized in every actual cubic extension
whenever X^3-X+1 is irreducible over the base field. -/
theorem exists_bad_parameter (hdim : Module.finrank F E=3)
    (hirr : Irreducible (X^3-X-C (-1) : F[X])) :
    ∃ z : E, ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph (F := F) z) := by
  obtain ⟨z,hz,B,hB⟩ := exists_cubic_power_basis hdim (-1) hirr
  exact ⟨z,not_free z (by simpa [sub_eq_add_neg] using hz) B hB⟩

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

/-- The explicit cubic is irreducible on every base field of order 3^m
with m not divisible by3. The proof uses Frobenius iteration, not a
probabilistic or asymptotic irreducibility assertion. -/
theorem cubic_irreducible_of_card (m : ℕ) (hcard : Fintype.card F=3^m)
    (hm : ¬ 3 ∣ m) : Irreducible (X^3-X-C (-1) : F[X]) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · have hd : (X^3-X-C (-1) : F[X]).natDegree=3 := by compute_degree!
    rw [hd]
    decide
  · intro x hx
    have hx3 : x^3=x-1 := by
      have h : x^3-x+1=0 := by simpa [Polynomial.IsRoot] using hx
      linear_combination h
    have hcast (k : ℕ) : (k : F)^3=(k : F) := by
      change frobenius F 3 (k : F)=(k : F)
      exact map_natCast _ _
    have hi (k : ℕ) : x^(3^k)=x-(k : F) := by
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ,pow_mul,ih,sub_pow_char,hx3,hcast]
        push_cast
        ring
    have hf := FiniteField.pow_card x
    rw [hcard,hi] at hf
    have hm0 : (m : F)=0 := by linear_combination -hf
    exact hm ((CharP.cast_eq_zero_iff F 3 m).mp hm0)

theorem exists_bad_parameter_of_card (m : ℕ) (hcard : Fintype.card F=3^m)
    (hm : ¬ 3 ∣ m) (hdim : Module.finrank F E=3) :
    ∃ z : E, ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph (F := F) z) :=
  exists_bad_parameter hdim (cubic_irreducible_of_card m hcard hm)

/-- The displayed bad-parameter subfamily exists at unbounded exponents. -/
theorem exists_bad_parameter_six_k_one (k : ℕ)
    (hcard : Fintype.card F=3^(6*k+1)) (hdim : Module.finrank F E=3) :
    ∃ z : E, ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph (F := F) z) := by
  apply exists_bad_parameter_of_card (6*k+1) hcard _ hdim
  omega

omit [CharP F 3] in
lemma cubic_counts (z : E) (hdim : Module.finrank F E=3) :
    Fintype.card ((Eˣ × F) ⊕ (Eˣ × F)) =
      2*Fintype.card F*(Fintype.card F^3-1) ∧
    (graph (F := F) z).edgeFinset.card =
      Fintype.card F*(Fintype.card F^3-1)^2 := by
  have hcard : Fintype.card E=Fintype.card F^3 := by
    rw [Module.card_eq_pow_finrank (K := F),hdim]
  constructor
  · rw [vertex_count,hcard]
  · rw [edge_count,hcard]

#print axioms kernel_el
#print axioms copy
#print axioms not_free
#print axioms edge_count
#print axioms exists_bad_parameter
#print axioms cubic_irreducible_of_card
#print axioms exists_bad_parameter_six_k_one
#print axioms cubic_counts
end Erdos714TwistedQuadraticProduct
