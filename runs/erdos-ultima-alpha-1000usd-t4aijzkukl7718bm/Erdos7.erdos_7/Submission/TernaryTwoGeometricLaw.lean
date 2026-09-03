import Submission.TernaryTwoSharedComparison
import Submission.FiniteGeometricBudget

/-! Exact finite geometric reference laws, with their terminal atom retained. -/
namespace Erdos7TernaryTwoGeometricLaw
open scoped BigOperators
open Erdos7TernaryTwoSharedComparison Erdos7FiniteGeometricBudget
set_option maxHeartbeats 2000000

noncomputable def geometricSum (E : ℕ) (f : ℝ → ℝ) (n : ℝ) : ℝ :=
  ∑ j : Fin (E+1), geometricWeight E j * f ((geometricLength E j : ℝ)*n)

lemma geometricSum_expansion (E : ℕ) (f : ℝ → ℝ) (n : ℝ) :
    geometricSum E f n = (∑ j∈Finset.range E,4/(5:ℝ)^(j+2)*f (((j:ℝ)+2)*n)) +
      1/(5:ℝ)^(E+1)*f (((E:ℝ)+2)*n) := by
  unfold geometricSum
  rw [Fin.sum_univ_castSucc]
  have hf : (∑ j : Fin E,geometricWeight E j.castSucc *
      f ((geometricLength E j.castSucc : ℝ)*n)) =
      ∑ j∈Finset.range E,4/(5:ℝ)^(j+2)*f (((j:ℝ)+2)*n) := by
    simp only [geometricWeight,geometricLength,Fin.val_castSucc,Fin.isLt,if_true,Nat.cast_add,Nat.cast_ofNat]
    exact Fin.sum_univ_eq_sum_range (fun j : ℕ => 4/(5:ℝ)^(j+2)*f (((j:ℝ)+2)*n)) E
  rw [hf]
  simp [geometricWeight,geometricLength]

lemma geometricSum_succ (E : ℕ) (f : ℝ → ℝ) (n : ℝ) :
    geometricSum (E+1) f n = geometricSum E f n +
      1/(5:ℝ)^(E+2)*(f (((E:ℝ)+3)*n)-f (((E:ℝ)+2)*n)) := by
  rw [geometricSum_expansion,geometricSum_expansion,Finset.sum_range_succ]
  norm_num only [Nat.cast_add,Nat.cast_one,add_assoc]
  congr 1
  rw [show (5:ℝ)^(E+2)=5^(E+1)*5 by rw [show E+2=(E+1)+1 by omega,pow_succ]]
  field_simp
  <;> ring

lemma q_five (j : ℕ) : q 5 1 (1/5) j = 1/(5:ℝ)^(j+1) := by
  apply min_eq_right
  apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
  simpa using (pow_le_pow_right₀ (show (1:ℝ)≤5 by norm_num) (show 1≤j+1 by omega))

/-- The finite reference is precisely a finite capped geometric operator;
no infinite series or dropped positive tail is involved. -/
theorem geometricSum_eq_op (E : ℕ) (f : ℝ → ℝ) (n : ℝ) :
    geometricSum E f n = op 5 1 (1/5) f (E+1) n := by
  have hop (e : ℕ) : op 5 1 (1/5) f (e+1) n = op 5 1 (1/5) f e n +
      1/(5:ℝ)^(e+1)*(f (((e:ℝ)+2)*n)-f (((e:ℝ)+1)*n)) := by
    unfold op
    rw [Finset.sum_range_succ,q_five]
    ring
  induction E with
  | zero =>
    rw [geometricSum_expansion,hop]
    norm_num [op]
    ring
  | succ E ih =>
    rw [geometricSum_succ,ih,hop (E+1)]
    try simp only [Nat.cast_add,Nat.cast_one]
    congr 2 <;> congr 1 <;> ring

/-- Every finite exponent cap is bounded by an exact finite affine-tail
budget, uniformly over all such caps. Signed monotone functions are allowed. -/
theorem geometricSum_le_budget (E R : ℕ) (f : ℝ → ℝ) (hf : Monotone f)
    (T S n : ℝ) (hS : 0≤S) (htail : ∀ x,T≤x → f x=f T+S*(x-T))
    (hn : 0≤n) (hR : T≤((R:ℝ)+1)*n) :
    geometricSum E f n ≤ budget 5 1 (1/5) f S R n := by
  rw [geometricSum_eq_op]
  exact op_le_budget 5 1 (1/5) (by norm_num) (by norm_num) (by norm_num)
    f hf T S hS htail R (E+1) n hn hR

lemma reference_eval (E : ℕ) (c : Fin 10) (f : ℝ → ℝ) :
    (∑ z,refWeight c (geometricWeight E) z*f (refCount (geometricLength E) z)) =
      (∑ n : Fin 3,(Erdos7TernaryTwoSharedPrefix.lowNum c n : ℝ)/100*f (n.val+1)) +
      ∑ n : Fin 3,(starWeight n : ℝ)/5*geometricSum E f (n.val+1) := by
  simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,refWeight,refCount,Sum.elim_inl,Sum.elim_inr,Nat.cast_add,Nat.cast_one,Nat.cast_mul]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _
  unfold geometricSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma reference_mass (E : ℕ) (c : Fin 10) :
    (∑ z,refWeight c (geometricWeight E) z) = if c.val<5 then (3:ℝ)/5 else 11/20 := by
  simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,refWeight,Sum.elim_inl,Sum.elim_inr]
  have hg : (∑ j : Fin (E+1),∑ n : Fin 3,
      geometricWeight E j*(starWeight n : ℝ)/5)=1/5 := by
    have he : ∀ j : Fin (E+1),(∑ n : Fin 3,
        geometricWeight E j*(starWeight n : ℝ)/5)=geometricWeight E j := by
      intro j
      norm_num [starWeight,Fin.sum_univ_succ]
      ring
    simp only [he,geometric_mass]
  rw [hg]
  unfold Erdos7TernaryTwoSharedPrefix.lowNum
  split_ifs <;> norm_num [Fin.sum_univ_succ]

lemma reference_count_bounds (E : ℕ) (z : Fin 3 ⊕ (Fin (E+1) × Fin 3)) :
    1≤refCount (geometricLength E) z ∧ refCount (geometricLength E) z≤3*(E+2) := by
  cases z with
  | inl n => simp only [refCount,Sum.elim_inl]; omega
  | inr z =>
    simp only [refCount,Sum.elim_inr,geometricLength]
    have hj := z.1.isLt
    have hn := z.2.isLt
    constructor
    · have := Nat.mul_le_mul (show 1≤z.1.val+2 by omega) (show 1≤z.2.val+1 by omega)
      simpa using this
    · calc
        _ ≤ (E+2)*3 := Nat.mul_le_mul (by omega) (by omega)
        _ = _ := Nat.mul_comm _ _

#print axioms reference_eval
#print axioms reference_mass

#print axioms geometricSum_eq_op
#print axioms geometricSum_le_budget
end Erdos7TernaryTwoGeometricLaw
