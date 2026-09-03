import Submission.TwistedQuadraticProduct

/-!
Square POINT restrictions of the even-plus-additive trace code. The nonzero
square coordinates on BOTH sides are retained, with the full additive alphabet.
These are construction obstructions, not a solution to Erdős 714.
-/
noncomputable section
open Classical Finset SimpleGraph
set_option maxHeartbeats 4000000
namespace Erdos714SquareTwistedQuadraticProduct
open Erdos714TwistedQuadraticProduct (Vec el vmul el_mul el_injective kernel)
open Erdos714QuinticNormProduct (element trace_element exists_cubic_power_basis)
variable {F E : Type*} [Field F] [Field E] [Algebra F E]

abbrev Sq (K : Type*) [Field K] := Subgroup.square Kˣ

def val {K : Type*} [Field K] (x : Sq K) : K := x.val.val

lemma val_injective {K : Type*} [Field K] : Function.Injective (@val K _) := by
  intro x y h
  exact Subtype.ext (Units.ext h)

lemma unit_square_iff {K : Type*} [Field K] (u : Kˣ) : IsSquare u ↔ IsSquare (u : K) := by
  constructor
  · rintro ⟨v,hv⟩
    exact ⟨v,congrArg Units.val hv⟩
  · rintro ⟨v,hv⟩
    have hn : v ≠ 0 := by intro h; rw [h,mul_zero] at hv; exact u.ne_zero hv
    exact ⟨Units.mk0 v hn,Units.ext hv⟩

def mkSq (x : E) (hx : x ≠ 0) (hs : IsSquare x) : Sq E :=
  ⟨Units.mk0 x hx,(unit_square_iff _).mpr hs⟩

lemma square_card {K : Type*} [Field K] [Fintype K] (hodd : Odd (Fintype.card K)) :
    Fintype.card (Sq K)=(Fintype.card K-1)/2 := by
  have he : Subgroup.square Kˣ = (powMonoidHom 2 : Kˣ →* Kˣ).range := by
    ext x
    simp only [Subgroup.mem_square,MonoidHom.mem_range,powMonoidHom_apply,pow_two,IsSquare]
    constructor <;> rintro ⟨r,hr⟩ <;> exact ⟨r,hr.symm⟩
  change Fintype.card (Subgroup.square Kˣ) = _
  rw [← Nat.card_eq_fintype_card,he,IsCyclic.card_powMonoidHom_range]
  simp only [Nat.card_eq_fintype_card,Fintype.card_units]
  have hd : 2 ∣ Fintype.card K-1 := by
    obtain ⟨k,hk⟩ := hodd
    exact ⟨k,by omega⟩
  rw [Nat.gcd_eq_right hd]

def code (γ : E) (r : Sq E × F) (x : Sq E) : F := kernel γ (val r.1*val x)+r.2

variable [Fintype E]

def graph (γ : E) : SimpleGraph ((Sq E × F) ⊕ (Sq E × F)) := Erdos714Coding.graph (code γ)

/-- A copy criterion that includes every square/nonzero guard explicitly. -/
def copy_of_points (γ : E) (a x : Fin 4 → E) (b y : Fin 4 → F)
    (ha : Function.Injective a) (hx : Function.Injective x)
    (ha0 : ∀ i, a i ≠ 0) (hx0 : ∀ i, x i ≠ 0)
    (haS : ∀ i, IsSquare (a i)) (hxS : ∀ i, IsSquare (x i))
    (he : ∀ i j, kernel γ (a i*x j)+b i=y j) :
    Copy (completeBipartiteGraph (Fin 4) (Fin 4)) (graph (F := F) γ) := by
  let L : Fin 4 → Sq E × F := fun i => (mkSq (a i) (ha0 i) (haS i),b i)
  let R : Fin 4 → Sq E × F := fun j => (mkSq (x j) (hx0 j) (hxS j),y j)
  have hL : Function.Injective L := by
    intro i j h
    exact ha (congrArg (fun p : Sq E × F => val p.1) h)
  have hR : Function.Injective R := by
    intro i j h
    exact hx (congrArg (fun p : Sq E × F => val p.1) h)
  have hE (i j : Fin 4) : code γ (L i) (R j).1=(R j).2 := he i j
  let le : Fin 4 ↪ Sq E × F := ⟨L,hL⟩
  let re : Fin 4 ↪ Sq E × F := ⟨R,hR⟩
  refine ⟨⟨le.sumMap re,?_⟩,(le.sumMap re).injective⟩
  intro u v huv
  cases u with
  | inl i =>
    cases v with
    | inl j => simp at huv
    | inr j => exact (Erdos714Coding.mem_symbols (code γ) (L i) (R j).1 (R j).2).mpr (hE i j)
  | inr j =>
    cases v with
    | inl i => exact (Erdos714Coding.mem_symbols (code γ) (L i) (R j).1 (R j).2).mpr (hE i j)
    | inr i => simp at huv

variable [CharP F 3]

omit [Fintype E] in
lemma kernel_square_parameter (z : E) (hz : z^3=z-1)
    (B : Module.Basis (Fin 3) F E) (hB : ∀ i, B i=z^(i : ℕ)) (v : Vec F) :
    kernel (z^2) (el z v) = v 0*v 2-(v 1)^2-(v 2)^2-v 2-(v 0)^3-(v 2)^3 := by
  have ht (w : Vec F) : Algebra.trace F E (el z w) = -w 2 := by
    exact trace_element (-1) z (by simpa [sub_eq_add_neg] using hz) B hB _ _ _
  have hez : z^2 = el (F := F) z ![0,0,1] := by simp [el,element]
  have hzx : z^2*el z v = el z (vmul ![0,0,1] v) := by
    calc
      _ = el z ![0,0,1]*el z v := by rw [← hez]
      _ = _ := el_mul z hz _ _
  unfold kernel
  rw [pow_two,el_mul z hz,hzx]
  simp only [ht]
  dsimp [vmul]
  apply sub_eq_zero.mp
  ring_nf
  reduce_mod_char!

-- All displayed coefficients lie in the prime field, but the identities hold
-- over every characteristic-three base field with the stated cubic basis.
def leftVec : Fin 4 → Vec F := ![![1,0,0],![0,0,1],![0,1,1],![0,-1,0]]
def rightVec : Fin 4 → Vec F := ![![0,1,1],![1,1,1],![1,-1,-1],![-1,-1,0]]
def leftRoot : Fin 4 → Vec F := ![![1,0,0],![0,1,0],![1,-1,1],![1,1,-1]]
def rightRoot : Fin 4 → Vec F := ![![1,-1,1],![1,-1,0],![1,0,-1],![1,-1,-1]]
def leftTag : Fin 4 → F := ![0,-1,1,1]
def rightTag : Fin 4 → F := ![-1,-1,1,0]

omit [Fintype E] in
lemma left_injective : Function.Injective (leftVec (F := F)) := by
  intro i j h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  fin_cases i <;> fin_cases j <;>
    simp [leftVec,Erdos714TwistedQuadraticProduct.neg_one_ne_one,
      Ne.symm Erdos714TwistedQuadraticProduct.neg_one_ne_one] at h0 h1 h2 ⊢

omit [Fintype E] in
lemma right_injective : Function.Injective (rightVec (F := F)) := by
  intro i j h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  fin_cases i <;> fin_cases j <;>
    simp [rightVec,Erdos714TwistedQuadraticProduct.neg_one_ne_one,
      Ne.symm Erdos714TwistedQuadraticProduct.neg_one_ne_one] at h0 h1 h2 ⊢

omit [Fintype E] [CharP F 3] in
lemma left_nonzero (i : Fin 4) : leftVec (F := F) i ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  fin_cases i <;> simp [leftVec] at h0 h1 h2

omit [Fintype E] [CharP F 3] in
lemma right_nonzero (i : Fin 4) : rightVec (F := F) i ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  fin_cases i <;> simp [rightVec] at h0 h1

omit [Fintype E] in
lemma left_square (z : E) (hz : z^3=z-1) (i : Fin 4) :
    IsSquare (el z (leftVec (F := F) i)) := by
  refine ⟨el z (leftRoot (F := F) i),?_⟩
  rw [el_mul z hz]
  apply congrArg (el z)
  funext j
  fin_cases i <;> fin_cases j <;> simp only [leftVec,leftRoot,vmul,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_zero',Matrix.cons_val_succ',Matrix.head_cons,Matrix.tail_cons]
  all_goals apply sub_eq_zero.mp
  all_goals ring_nf
  all_goals reduce_mod_char!

omit [Fintype E] in
lemma right_square (z : E) (hz : z^3=z-1) (i : Fin 4) :
    IsSquare (el z (rightVec (F := F) i)) := by
  refine ⟨el z (rightRoot (F := F) i),?_⟩
  rw [el_mul z hz]
  apply congrArg (el z)
  funext j
  fin_cases i <;> fin_cases j <;> simp only [rightVec,rightRoot,vmul,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_zero',Matrix.cons_val_succ',Matrix.head_cons,Matrix.tail_cons]
  all_goals apply sub_eq_zero.mp
  all_goals ring_nf
  all_goals reduce_mod_char!

omit [Fintype E] in
lemma explicit_edges (z : E) (hz : z^3=z-1)
    (B : Module.Basis (Fin 3) F E) (hB : ∀ i, B i=z^(i : ℕ)) (i j : Fin 4) :
    kernel (z^2) (el z (leftVec (F := F) i)*el z (rightVec (F := F) j))+leftTag i=rightTag (F := F) j := by
  rw [el_mul z hz,kernel_square_parameter z hz B hB]
  fin_cases i <;> fin_cases j <;> simp only [leftVec,rightVec,leftTag,rightTag,vmul,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_zero',Matrix.cons_val_succ',Matrix.head_cons,Matrix.tail_cons]
  all_goals apply sub_eq_zero.mp
  all_goals ring_nf
  all_goals reduce_mod_char!

/-- All eight points are nonzero squares. No antipodal pair is used. -/
def explicit_copy (z : E) (hz : z^3=z-1)
    (B : Module.Basis (Fin 3) F E) (hB : ∀ i, B i=z^(i : ℕ)) :
    Copy (completeBipartiteGraph (Fin 4) (Fin 4)) (graph (F := F) (z^2)) := by
  have he0 : el z (0 : Vec F)=0 := by simp [el,element]
  refine copy_of_points (z^2) (fun i => el z (leftVec (F := F) i)) (fun j => el z (rightVec (F := F) j))
    leftTag rightTag ((el_injective z B hB).comp left_injective)
    ((el_injective z B hB).comp right_injective) ?_ ?_
    (left_square z hz) (right_square z hz) (explicit_edges z hz B hB)
  · intro i h
    exact left_nonzero i (el_injective z B hB (h.trans he0.symm))
  · intro i h
    exact right_nonzero i (el_injective z B hB (h.trans he0.symm))

theorem explicit_not_free (z : E) (hz : z^3=z-1)
    (B : Module.Basis (Fin 3) F E) (hB : ∀ i, B i=z^(i : ℕ)) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph (F := F) (z^2)) :=
  fun h => h ⟨explicit_copy z hz B hB⟩

omit [Fintype E] in
lemma explicit_parameter_trace (z : E) (hz : z^3=z-1)
    (B : Module.Basis (Fin 3) F E) (hB : ∀ i, B i=z^(i : ℕ)) :
    Algebra.trace F E (z^2)=-1 := by
  have h := trace_element (-1) z (by simpa [sub_eq_add_neg] using hz) B hB 0 0 1
  simpa [element] using h

variable [Fintype F]

theorem exists_nonzero_trace_bad_parameter (m : ℕ) (hcard : Fintype.card F=3^m)
    (hm : ¬ 3 ∣ m) (hdim : Module.finrank F E=3) :
    ∃ γ : E, Algebra.trace F E γ=-1 ∧
      ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph (F := F) γ) := by
  obtain ⟨z,hz,B,hB⟩ := exists_cubic_power_basis hdim (-1)
    (Erdos714TwistedQuadraticProduct.cubic_irreducible_of_card m hcard hm)
  have hz' : z^3=z-1 := by simpa [sub_eq_add_neg] using hz
  exact ⟨z^2,explicit_parameter_trace z hz' B hB,explicit_not_free z hz' B hB⟩

theorem exists_bad_parameter_six_k_one (k : ℕ)
    (hcard : Fintype.card F=3^(6*k+1)) (hdim : Module.finrank F E=3) :
    ∃ γ : E, Algebra.trace F E γ=-1 ∧
      ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph (F := F) γ) := by
  apply exists_nonzero_trace_bad_parameter (6*k+1) hcard _ hdim
  omega

omit [Fintype E] [Fintype F] in
/-- A trace-zero parameter leaves every base-field product at kernel value zero. -/
lemma kernel_base_zero (hdim : Module.finrank F E=3) (γ : E)
    (hγ : Algebra.trace F E γ=0) (a : F) :
    kernel (F := F) γ (algebraMap F E a)=0 := by
  have h3 : (3 : F)=0 := CharP.cast_eq_zero F 3
  have ht (b : F) : Algebra.trace F E (algebraMap F E b)=0 := by
    simp [Algebra.trace_algebraMap,hdim,h3]
  have hg : Algebra.trace F E (γ*algebraMap F E a)=0 := by
    rw [mul_comm,← Algebra.smul_def,LinearMap.map_smul]
    simp [hγ]
  simp only [kernel,← map_pow,ht,hg,zero_pow (by decide : 3 ≠ 0),add_zero]

/-- Uniform obstruction for every trace-zero parameter, even after the
square-point restriction: the base-field squares give a complete block. -/
theorem trace_zero_not_free (hdim : Module.finrank F E=3)
    (hq : 9 ≤ Fintype.card F) (γ : E) (hγ : Algebra.trace F E γ=0) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph (F := F) γ) := by
  have ho : Odd (Fintype.card F) :=
    Nat.odd_iff.mpr (FiniteField.odd_card_of_char_ne_two (by rw [ringChar.eq F 3]; decide))
  have hc : 4 ≤ Fintype.card (Sq F) := by rw [square_card ho]; omega
  obtain ⟨t⟩ := Function.Embedding.nonempty_of_card_le (α := Fin 4) (β := Sq F)
    (by simpa using hc)
  let p : Fin 4 → E := fun i => algebraMap F E (val (t i))
  have hp : Function.Injective p :=
    (algebraMap F E).injective.comp (val_injective.comp t.injective)
  have hp0 (i : Fin 4) : p i ≠ 0 := by
    exact (map_ne_zero (algebraMap F E)).mpr (t i).val.ne_zero
  have hpS (i : Fin 4) : IsSquare (p i) := by
    obtain ⟨v,hv⟩ := (unit_square_iff (t i).val).mp (t i).property
    refine ⟨algebraMap F E v,?_⟩
    change algebraMap F E (val (t i))=algebraMap F E v*algebraMap F E v
    rw [← map_mul]
    exact congrArg (algebraMap F E) hv
  have he (i j : Fin 4) : kernel γ (p i*p j)+(0 : F)=0 := by
    change kernel γ (algebraMap F E (val (t i))*algebraMap F E (val (t j)))+0=0
    rw [← map_mul,kernel_base_zero hdim γ hγ,add_zero]
  exact fun hf => hf ⟨copy_of_points γ p p (fun _ => 0) (fun _ => 0)
    hp hp hp0 hp0 hpS hpS he⟩

omit [CharP F 3] in
lemma edge_count (γ : E) (hodd : Odd (Fintype.card E)) :
    (graph (F := F) γ).edgeFinset.card =
      Fintype.card F*((Fintype.card E-1)/2)^2 := by
  rw [graph,Erdos714Coding.edge_count]
  simp only [Fintype.card_prod,square_card hodd]
  ring

omit [CharP F 3] [Field F] [Algebra F E] in
lemma vertex_count (hodd : Odd (Fintype.card E)) :
    Fintype.card ((Sq E × F) ⊕ (Sq E × F)) =
      2*Fintype.card F*((Fintype.card E-1)/2) := by
  simp only [Fintype.card_sum,Fintype.card_prod,square_card hodd]
  ring

lemma cubic_counts (γ : E) (hdim : Module.finrank F E=3) :
    Fintype.card ((Sq E × F) ⊕ (Sq E × F)) =
      2*Fintype.card F*((Fintype.card F^3-1)/2) ∧
    (graph (F := F) γ).edgeFinset.card =
      Fintype.card F*((Fintype.card F^3-1)/2)^2 := by
  letI : CharP E 3 := charP_of_injective_algebraMap (algebraMap F E).injective 3
  have ho : Odd (Fintype.card E) :=
    Nat.odd_iff.mpr (FiniteField.odd_card_of_char_ne_two (by rw [ringChar.eq E 3]; decide))
  have hc : Fintype.card E=Fintype.card F^3 := by
    rw [Module.card_eq_pow_finrank (K := F),hdim]
  constructor
  · rw [vertex_count ho,hc]
  · rw [edge_count γ ho,hc]

#print axioms kernel_base_zero
#print axioms trace_zero_not_free
#print axioms cubic_counts
#print axioms explicit_copy
#print axioms exists_bad_parameter_six_k_one
end Erdos714SquareTwistedQuadraticProduct
