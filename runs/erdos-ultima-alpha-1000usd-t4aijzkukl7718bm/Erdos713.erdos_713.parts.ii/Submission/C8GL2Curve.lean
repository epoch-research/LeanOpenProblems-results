import FormalConjecturesUtil
import Submission.C8InvolutiveBlock

/-! Characteristic-two matrix-curve calculations. Auxiliary to Erdős 713;
these lemmas do not prove rationality of an extremal exponent. -/
open SimpleGraph
open scoped MatrixGroups
namespace Erdos713C8GL2Curve
variable {K : Type*} [Field K] [CharP K 2]
set_option maxHeartbeats 2000000

def delta (a : K) : K := 1+a^3

def raw (a : K) : Matrix (Fin 2) (Fin 2) K := !![1,a;a^2,1]

lemma raw_det (a : K) : (raw a).det = delta a := by
  simp only [raw,Matrix.det_fin_two_of,delta,CharTwo.sub_eq_add]
  ring

lemma raw_square (a : K) : raw a*raw a = delta a • (1 : Matrix (Fin 2) (Fin 2) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [raw,delta,Matrix.mul_apply,Fin.sum_univ_two,Matrix.smul_apply,
      CharTwo.add_self_eq_zero] <;> ring

abbrev Param (K : Type*) [Field K] := {a : K // delta a ≠ 0}

def curve (a : Param K) : GL (Fin 2) K where
  val := raw a.val
  inv := (delta a.val)⁻¹ • raw a.val
  val_inv := by
    rw [Matrix.mul_smul,raw_square,smul_smul,inv_mul_cancel₀ a.property,one_smul]
  inv_val := by
    rw [Matrix.smul_mul,raw_square,smul_smul,inv_mul_cancel₀ a.property,one_smul]

@[simp] lemma curve_val (a : Param K) : (curve a).val = raw a.val := rfl
@[simp] lemma curve_inv_val (a : Param K) : ((curve a)⁻¹).val =
    (delta a.val)⁻¹ • raw a.val := rfl

lemma curve_injective : Function.Injective (curve (K := K)) := by
  intro a b h
  apply Subtype.ext
  have hh := congrArg (fun A : GL (Fin 2) K => A.val 0 1) h
  simpa [raw,curve] using hh

lemma difference_01 (a b : Param K) :
    ((curve a)*(curve b)⁻¹).val 0 1 = (a.val+b.val)/delta b.val := by
  simp [curve,raw,Matrix.mul_apply,Fin.sum_univ_two,div_eq_mul_inv]
  ring

lemma difference_10 (a b : Param K) :
    ((curve a)*(curve b)⁻¹).val 1 0 =
      (a.val+b.val)*(((curve a)*(curve b)⁻¹).val 0 1) := by
  rw [difference_01]
  simp [curve,raw,Matrix.mul_apply,Fin.sum_univ_two,div_eq_mul_inv]
  ring_nf
  reduce_mod_char!

lemma difference_sidon (hcube : Function.Injective (fun x : K => x^3))
    (a b c d : Param K) (hab : a ≠ b)
    (h : curve a*(curve b)⁻¹ = curve c*(curve d)⁻¹) : a=c ∧ b=d := by
  have habv : a.val ≠ b.val := fun he => hab (Subtype.ext he)
  have habs : a.val+b.val ≠ 0 := by
    simpa only [← CharTwo.sub_eq_add,sub_ne_zero] using habv
  have h01 := congrArg (fun A : GL (Fin 2) K => A.val 0 1) h
  have h10 := congrArg (fun A : GL (Fin 2) K => A.val 1 0) h
  dsimp only at h01 h10
  rw [difference_10,difference_10,h01] at h10
  have hsum : a.val+b.val = c.val+d.val :=
    mul_right_cancel₀ (by rw [← h01,difference_01]; exact div_ne_zero habs b.property) h10
  rw [difference_01,difference_01,← hsum] at h01
  have hden : delta b.val = delta d.val := by
    have hh := (div_eq_div_iff b.property d.property).mp h01
    exact (mul_left_cancel₀ habs hh).symm
  have hbd : b=d := Subtype.ext (hcube (add_left_cancel hden))
  refine ⟨?_,hbd⟩
  subst d
  exact Subtype.ext (add_right_cancel hsum)

lemma difference_not_involution (a b : Param K) (ha : a.val ≠ 0)
    (hb : b.val ≠ 0) (hab : a ≠ b) : (curve a*(curve b)⁻¹)^2 ≠ 1 := by
  intro h
  have hh := congrArg (fun A : GL (Fin 2) K => A.val 0 1) h
  have habs : a.val+b.val ≠ 0 := by
    rw [← CharTwo.sub_eq_add,sub_ne_zero]
    exact fun he => hab (Subtype.ext he)
  have he : a.val*b.val*(a.val+b.val)^2 = 0 := by
    simp [pow_two,curve,raw,Matrix.mul_apply,Fin.sum_univ_two] at hh
    field_simp [b.property] at hh
    ring_nf at hh ⊢
    reduce_mod_char! at hh ⊢
    exact hh
  exact (mul_ne_zero (mul_ne_zero ha hb) (pow_ne_zero _ habs)) he

lemma delta_pair (a c : K) :
    delta a*delta c = 1+(a+c)^3+(a*c)*(a+c)+(a*c)^3 := by
  simp only [delta]
  ring_nf
  reduce_mod_char!

lemma swapped_delta {a b c d : K} (h1 : a+c=b*d) (h2 : b+d=a*c) :
    delta a*delta c = delta b*delta d := by
  rw [delta_pair,delta_pair,h1,h2]
  ring

lemma raw_four_trace (a b c d : K) :
    (raw a*raw b*raw c*raw d) 0 0 + (raw a*raw b*raw c*raw d) 1 1 =
    (a+c)*(a*c)+(b+d)*(b*d)+(a+c)*(b+d)*((a+c)+(b+d))+
      (a*c)*(b*d)*((a*c)+(b*d)) := by
  simp [raw,Matrix.mul_apply,Fin.sum_univ_two]
  ring_nf
  reduce_mod_char!

lemma swapped_trace {a b c d : K} (h1 : a+c=b*d) (h2 : b+d=a*c) :
    (raw a*raw b*raw c*raw d) 0 0 = (raw a*raw b*raw c*raw d) 1 1 := by
  apply sub_eq_zero.mp
  rw [CharTwo.sub_eq_add,raw_four_trace,h1,h2]
  ring_nf
  reduce_mod_char!

lemma matrix_involution (A : Matrix (Fin 2) (Fin 2) K)
    (hdet : A.det = 1) (hdiag : A 0 0 = A 1 1) : A*A=1 := by
  rw [Matrix.det_fin_two] at hdet
  rw [CharTwo.sub_eq_add,hdiag] at hdet
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply,Fin.sum_univ_two,hdiag]
  · simpa only [mul_comm (A 1 0) (A 0 1)] using hdet
  · ring_nf; reduce_mod_char!
  · ring_nf; reduce_mod_char!
  · simpa only [mul_comm (A 1 0) (A 0 1),add_comm] using hdet

lemma block_val (a b c d : Param K) :
    ((curve a*(curve b)⁻¹)*(curve c*(curve d)⁻¹)).val =
      (delta b.val*delta d.val)⁻¹ • (raw a.val*raw b.val*raw c.val*raw d.val) := by
  simp only [Units.val_mul,curve_val,curve_inv_val,Matrix.mul_smul,Matrix.smul_mul,
    smul_smul,mul_inv_rev,Matrix.mul_assoc]


lemma swapped_involution (a b c d : Param K)
    (h1 : a.val+c.val=b.val*d.val) (h2 : b.val+d.val=a.val*c.val) :
    ((curve a*(curve b)⁻¹)*(curve c*(curve d)⁻¹))^2 = 1 := by
  apply Units.ext
  simp only [pow_two,Units.val_mul,Units.val_one]
  change ((curve a*(curve b)⁻¹)*(curve c*(curve d)⁻¹)).val *
    ((curve a*(curve b)⁻¹)*(curve c*(curve d)⁻¹)).val = 1
  apply matrix_involution
  · rw [block_val,Matrix.det_smul]
    simp only [Matrix.det_mul,raw_det,Fintype.card_fin]
    have he := swapped_delta h1 h2
    calc
      _ = (delta b.val*delta d.val)⁻¹^2 *
          ((delta a.val*delta c.val)*(delta b.val*delta d.val)) := by ring
      _ = 1 := by rw [he]; field_simp [b.property,d.property]
  · rw [block_val]
    simpa only [Matrix.smul_apply,smul_eq_mul] using
      congrArg (fun x : K => (delta b.val*delta d.val)⁻¹*x) (swapped_trace h1 h2)

/-- Four admissible distinct parameters satisfying the swapped sum-product
relations give an injective eight-cycle, not just a closed walk. -/
theorem contains_at (hcube : Function.Injective (fun x : K => x^3))
    (a b c d : Param K) (ha : a.val ≠ 0) (hb : b.val ≠ 0)
    (hab : a ≠ b) (hcb : c ≠ b) (hda : d ≠ a)
    (h1 : a.val+c.val=b.val*d.val) (h2 : b.val+d.val=a.val*c.val) :
    cycleGraph 8 ⊑ Erdos713C8CommutingDifferences.graph (curve (K := K)) := by
  apply Erdos713C8InvolutiveBlock.contains curve a b c d
    (difference_not_involution a b ha hb hab) ?_ (swapped_involution a b c d h1 h2)
    (fun h => hcb (curve_injective h)) (fun h => hda (curve_injective h))
  intro h
  have he : curve a*(curve b)⁻¹ = curve d*(curve c)⁻¹ := by
    calc
      _ = ((curve a*(curve b)⁻¹)*(curve c*(curve d)⁻¹))*curve d*(curve c)⁻¹ := by
        simp [mul_assoc]
      _ = _ := by rw [h,one_mul]
  exact hda (difference_sidon hcube a b d c hab he).1.symm

end Erdos713C8GL2Curve
