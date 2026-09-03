import Submission.Capped19Real
import Submission.KernelFamilyCompression

/-! A complete finite-exponent scalar certificate through prime19. This is
still not the arithmetic covering theorem: the family model must be connected. -/
namespace Erdos7Capped19Scalar
open scoped BigOperators
open Erdos7Capped19Rows Erdos7Capped19Metadata Erdos7Capped19Real
open Erdos7CappedRetentionRows Erdos7KernelFamilyCompression
set_option maxHeartbeats 2500000

noncomputable def truncatedTail (p c : ℝ) (E j : ℕ) : ℝ :=
  if j<E then c/p^(j+1) else 0

lemma truncatedTail_nonneg (p c : ℝ) (hp : 1<p) (hc : 0 ≤ c) (E j : ℕ) :
    0 ≤ truncatedTail p c E j := by
  dsimp only [truncatedTail]
  split_ifs
  · exact div_nonneg hc (pow_nonneg (by linarith) _)
  · exact le_rfl

lemma truncatedTail_decreasing (p c : ℝ) (hp : 1<p) (hc : 0 ≤ c) (E j : ℕ) :
    truncatedTail p c E (j+1) ≤ truncatedTail p c E j := by
  by_cases hj : j+1<E
  · simp only [truncatedTail, if_pos hj, if_pos (show j<E by omega)]
    apply div_le_div_of_nonneg_left hc (pow_pos (by linarith) _)
    exact pow_le_pow_right₀ hp.le (by omega)
  · simp only [truncatedTail, if_neg hj]
    split_ifs
    · exact div_nonneg hc (pow_nonneg (by linarith) _)
    · exact le_rfl

lemma coefficient_increment {E : ℕ} (h : ℝ) (hh : 0 ≤ h) (q f : ℕ → ℝ) (hq : q E=0) :
    (∑ d : Option (Fin E), coefficient h q E d *
      (match d with | none => f 0 | some j => f (j.val+1))) =
      h*f 0+∑ j ∈ Finset.range E, min h (q j)*(f (j+1)-f j) := by
  rw [Fintype.sum_option]
  simp only [coefficient]
  rw [Fin.sum_univ_eq_sum_range (fun j => (min h (q j)-min h (q (j+1)))*f (j+1)) E]
  have hh' := Erdos7FiniteRetainedMixture.mixture_positive_form h (fun j => min h (q j)) f E
  simp only [Erdos7FiniteRetainedMixture.mixture, hq, min_eq_right hh, zero_mul, add_zero] at hh'
  exact hh'.symm

lemma finite_coefficient_op (p c h : ℝ) (hh : 0 ≤ h) (E : ℕ) (f : ℝ → ℝ) (n : ℝ) :
    (∑ d : Option (Fin E), coefficient h (truncatedTail p c E) E d *f (multiplier d*n)) =
      Erdos7FiniteGeometricBudget.op p c h f E n := by
  have hc := coefficient_increment (E := E) h hh (truncatedTail p c E) (fun j => f ((j+1)*n))
    (by simp [truncatedTail])
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_add, one_mul,
    add_assoc, one_add_one_eq_two] at hc
  have hleft : (∑ d : Option (Fin E), coefficient h (truncatedTail p c E) E d *f (multiplier d*n)) =
      ∑ d : Option (Fin E), coefficient h (truncatedTail p c E) E d *
        (match d with | none => f n | some j => f (((j.val:ℝ)+2)*n)) := by
    apply Finset.sum_congr rfl
    intro d _
    cases d <;> simp only [multiplier, one_mul]
  rw [hleft, hc]
  dsimp only [Erdos7FiniteGeometricBudget.op]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  simp only [truncatedTail, if_pos (Finset.mem_range.mp hj), Erdos7FiniteGeometricBudget.q,
    Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two]

lemma coefficient_zero (q : ℕ → ℝ) (hq : ∀ j, 0 ≤ q j) (E : ℕ) (d : Option (Fin E)) :
    coefficient 0 q E d=0 := by
  cases d with
  | none => simp [coefficient, min_eq_left (hq 0)]
  | some j => simp [coefficient, min_eq_left (hq j.val), min_eq_left (hq (j.val+1))]

lemma evalR_sum (s : Stage) (future : List ℚ) (hm : Metadata s future) (x : ℝ) :
    evalR s.F x=evalR s.U x+evalR s.V x := by
  have hAdd := hm.2.2.2.2.2.2.2.2.1
  have he (j : ℕ) (hj : j<10) : (coeff s.F j:ℝ)=(coeff s.U j:ℝ)+(coeff s.V j:ℝ) := by
    exact_mod_cast hAdd j (List.mem_range.mpr hj)
  have hsum : (∑ j ∈ Finset.range 8, (coeff s.F (j+2):ℝ)*Erdos7FiniteHingeFunctions.hinge (j+2) x) =
      ∑ j ∈ Finset.range 8, ((coeff s.U (j+2):ℝ)+(coeff s.V (j+2):ℝ))*
        Erdos7FiniteHingeFunctions.hinge (j+2) x := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [he (j+2) (by have := Finset.mem_range.mp hj; omega)]
  dsimp only [evalR, Erdos7FiniteHingeFunctions.eval]
  rw [he 0 (by omega), he 1 (by omega), hsum]
  simp only [add_mul, Finset.sum_add_distrib]
  ring

/-- Uniformly in the finite current exponent cap E. -/
theorem scalar_dual (s : Stage) (future : List ℚ) (hv : Valid s future)
    (hm : Metadata s future) (E : ℕ) (k n : ℝ) (hk : 1 ≤ k) (hn : 1 ≤ n) :
    let h := retained ((s.p:ℝ)-1) s.cap s.cut k
    1-h+(∑ d : Option (Fin E), coefficient h (truncatedTail s.p s.cap E) E d *
      evalR future (multiplier d*n)) ≤ evalR s.U k+evalR s.V n := by
  dsimp only
  have hp : (1:ℝ)<s.p := by exact_mod_cast hm.1
  have hc : (0:ℝ)≤s.cap := by exact_mod_cast hm.2.1
  have hU := hm.2.2.1
  have hV := hm.2.2.2.1
  have hG := hm.2.2.2.2.2.1
  by_cases hkc : k ≤ (s.cut:ℝ)
  · have he : retained ((s.p:ℝ)-1) s.cap s.cut k=ret s k := by simp only [retained, if_pos hkc, ret]
    rw [he, finite_coefficient_op (s.p:ℝ) s.cap (ret s k) (show 0 ≤ ret s k from le_max_left _ _) E]
    have hf := Erdos7FiniteGeometricBudget.op_le_budget (s.p:ℝ) s.cap (ret s k) hp hc
      (le_max_left _ _) (evalR future) (evalR_monotone future hG) 9
      (Erdos7Capped19Rows.slope future) (slope_nonneg future hG) (evalR_tail future hG)
      9 E n (by linarith) (by norm_num; linarith)
    have hd := live_dual s future hv hm k n hk hkc hn
    dsimp only [cost] at hd
    linarith
  · have he : retained ((s.p:ℝ)-1) s.cap s.cut k=0 := by simp only [retained, if_neg hkc]
    rw [he]
    simp only [coefficient_zero _ (truncatedTail_nonneg s.p s.cap hp hc E), zero_mul,
      Finset.sum_const_zero, sub_zero, add_zero]
    have hkill : (1:ℝ) ≤ evalR s.U s.cut+evalR s.V 1 := by
      have hh := hv.2.2.2.2.1
      have hr : (1:ℝ) ≤ (Rat.cast (evaluate s.U s.cut+evaluate s.V 1):ℝ) := by exact_mod_cast hh
      rw [Rat.cast_add, ← evalR_cast, ← evalR_cast] at hr
      simpa only [Rat.cast_one] using hr
    have hu := evalR_monotone s.U hU (le_of_lt (lt_of_not_ge hkc))
    have hv' := evalR_monotone s.V hV hn
    linarith

lemma root_mixture_exact : mixture 3 2 1 stage5.F 1=rootValue := by decide +kernel

theorem root_finite_bound (E : ℕ) :
    Erdos7FiniteGeometricBudget.op 3 2 1 (evalR stage5.F) E 1 ≤ (rootValue:ℝ) := by
  have hg : Good stage5.F := stage5_metadata.2.2.2.2.1
  have hh := Erdos7FiniteGeometricBudget.op_le_budget 3 2 1 (by norm_num) (by norm_num) (by norm_num)
    (evalR stage5.F) (evalR_monotone stage5.F hg) 9 (Erdos7Capped19Rows.slope stage5.F)
    (slope_nonneg stage5.F hg) (evalR_tail stage5.F hg) 9 E 1 (by norm_num) (by norm_num)
  have he : Erdos7FiniteGeometricBudget.budget 3 2 1 (evalR stage5.F)
      (Erdos7Capped19Rows.slope stage5.F) 9 1=(rootValue:ℝ) := by
    rw [show (3:ℝ)=(3:ℚ) by norm_num, show (2:ℝ)=(2:ℚ) by norm_num,
      show (1:ℝ)=(1:ℚ) by norm_num, mixture_cast, root_mixture_exact]
  rw [he] at hh
  exact hh

theorem root_finite_strict (E : ℕ) :
    Erdos7FiniteGeometricBudget.op 3 2 1 (evalR stage5.F) E 1 < 1 :=
  (root_finite_bound E).trans_lt (by exact_mod_cast rootValue_lt_one)

#print axioms scalar_dual
#print axioms root_finite_strict
end Erdos7Capped19Scalar
