import Submission.RectangleBudgetTower
import Submission.Capped19Scalar

/-! The certified prime-19 scalar rows instantiated as an actual finite
rectangle budget schedule. This is a bounded-prime result only. -/
namespace Erdos7Capped19Schedule
open scoped BigOperators
open Erdos7CompleteFamilyModel Erdos7Capped19Rows Erdos7Capped19Metadata
open Erdos7Capped19Real Erdos7Capped19Scalar
open Erdos7CappedRetentionRows Erdos7KernelFamilyCompression
set_option maxHeartbeats 3000000
set_option autoImplicit false
set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable

def primes : Fin 7 → ℕ := ![3,5,7,11,13,17,19]
def later : Fin 6 → Stage := ![stage5,stage7,stage11,stage13,stage17,stage19]
def forms : ℕ → List ℚ
  | 1 => stage5.F
  | 2 => stage7.F
  | 3 => stage11.F
  | 4 => stage13.F
  | 5 => stage17.F
  | 6 => stage19.F
  | _ => terminal

def future (j : Fin 6) : List ℚ := forms (j.val+2)
noncomputable def potential (t : ℕ) : ℝ → ℝ :=
  if t = 0 then fun _ => rootValue else evalR (forms t)
noncomputable def cap : Fin 7 → ℝ := Fin.cases 2 (fun j => (later j).cap)
noncomputable def cut : Fin 7 → ℝ := Fin.cases 1 (fun j => (later j).cut)
noncomputable def U : Fin 7 → ℝ → ℝ := Fin.cases (fun _ => 0) (fun j => evalR (later j).U)
noncomputable def V : Fin 7 → ℝ → ℝ := Fin.cases (fun _ => rootValue) (fun j => evalR (later j).V)

lemma later_valid (j : Fin 6) : Valid (later j) (future j) := by
  fin_cases j
  · exact stage5_valid
  · exact stage7_valid
  · exact stage11_valid
  · exact stage13_valid
  · exact stage17_valid
  · exact stage19_valid

lemma later_metadata (j : Fin 6) : Metadata (later j) (future j) := by
  fin_cases j
  · exact stage5_metadata
  · exact stage7_metadata
  · exact stage11_metadata
  · exact stage13_metadata
  · exact stage17_metadata
  · exact stage19_metadata

lemma primes_gt_one (i : Fin 7) : 1 < primes i := by fin_cases i <;> norm_num [primes]
lemma primes_later (j : Fin 6) : (primes j.succ:ℚ) = (later j).p := by fin_cases j <;> rfl
lemma forms_later (j : Fin 6) : forms (j.val+1) = (later j).F := by fin_cases j <;> rfl
lemma potential_later (j : Fin 6) : potential j.succ.val = evalR (later j).F := by
  simp only [potential,Fin.val_succ,show j.val+1 ≠ 0 by omega,if_false,forms_later]
lemma potential_future (j : Fin 6) : potential (j.succ.val+1) = evalR (future j) := by
  simp only [potential,Fin.val_succ,show j.val+1+1 ≠ 0 by omega,if_false,future,Nat.add_assoc]

lemma evalR_terminal : evalR terminal = fun _ => 0 := by
  funext x
  have hc (j : ℕ) : coeff terminal j = 0 := by
    dsimp only [coeff,terminal]
    rw [List.getElem?_replicate]
    split_ifs <;> rfl
  simp only [evalR,Erdos7FiniteHingeFunctions.eval,hc,Rat.cast_zero,zero_mul,
    zero_add,Finset.sum_const_zero]

lemma geometric_mass (p : ℝ) (hp : 1 < p) (E : ℕ) :
    (∑ a : Fin E,(p-1)*truncatedTail p 1 E a.val) ≤ 1 := by
  have hp1 : p-1 ≠ 0 := by linarith
  have hh := Erdos7FiniteGeometricBudget.finite_tail_bound
    (fun j => (p-1)/p^(j+1)) (Erdos7FiniteGeometricBudget.tail p (p-1)) 0
    (fun j => div_nonneg (by linarith) (pow_nonneg (by linarith) _))
    (Erdos7FiniteGeometricBudget.tail_nonneg p (p-1) hp (by linarith))
    (fun j _ => (Erdos7FiniteGeometricBudget.tail_step p (p-1) hp j).le) E
  simp only [Finset.range_zero,Finset.sum_empty,Erdos7FiniteGeometricBudget.tail,pow_zero,one_mul,
    div_self hp1,zero_add] at hh
  have he : (∑ a : Fin E,(p-1)*truncatedTail p 1 E a.val) =
      ∑ a ∈ Finset.range E,(p-1)/p^(a+1) := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro a _
    simp only [truncatedTail,if_pos a.isLt,mul_one_div]
  rwa [he]

lemma cap_tail (p c : ℝ) (E j : ℕ) :
    c*truncatedTail p 1 E j = truncatedTail p c E j := by
  dsimp only [truncatedTail]
  split_ifs <;> simp [div_eq_mul_inv]

variable (A : Fin 7 → Type) [∀ i,Fintype (A i)] [∀ i,Nonempty (A i)] [∀ i,DecidableEq (A i)]
variable (E : Fin 7 → ℕ) (X : Pattern E → ∀ i,Finset (A i))

/-- Only the actual coordinate-density bound is supplied by the application. -/
noncomputable def schedule (ρ : ∀ i,A i → ℝ)
    (hρ : ∀ i y,0 ≤ ρ i y) (hρmass : ∀ i,(∑ y,ρ i y) = 1)
    (hd : ∀ i k,exponent E k i ≠ 0 →
      (∑ y,if y ∈ X k i then ρ i y else 0) ≤ 1/(primes i:ℝ)^(exponent E k i)) :
    BudgetSchedule A E X where
  density := ρ
  q := fun i => (primes i:ℝ)-1
  cap := cap
  cut := cut
  tail := fun i => truncatedTail (primes i) 1 (E i)
  potential := potential
  U := U
  V := V
  density_nonneg := hρ
  density_mass := hρmass
  q_pos := fun i => by exact_mod_cast (show 0 < (primes i:ℤ)-1 by have := primes_gt_one i; omega)
  cap_nonneg := by
    intro i
    refine Fin.cases (by norm_num [cap]) (fun j => ?_) i
    change (0:ℝ) ≤ ((later j).cap:ℝ)
    exact_mod_cast (later_metadata j).2.1
  tail_nonneg := fun i j _ => truncatedTail_nonneg _ _ (by exact_mod_cast primes_gt_one i) (by norm_num) _ _
  tail_decreasing := fun i => truncatedTail_decreasing _ _ (by exact_mod_cast primes_gt_one i) (by norm_num) _
  tail_zero := fun i => by simp [truncatedTail]
  current_mass := fun i => geometric_mass _ (by exact_mod_cast primes_gt_one i) (E i)
  box_density := by
    intro i k hk
    have hb := exponent_bound E k i
    have hl : exponent E k i-1 < E i := by omega
    simpa only [truncatedTail,if_pos hl,show exponent E k i-1+1 = exponent E k i by omega] using hd i k hk
  convex_U := by
    intro i
    refine Fin.cases (convexOn_const 0 convex_univ) (fun j => ?_) i
    exact evalR_convex (later j).U (later_metadata j).2.2.1
  monotone_U := by
    intro i
    refine Fin.cases (monotone_const) (fun j => ?_) i
    exact evalR_monotone (later j).U (later_metadata j).2.2.1
  nonneg_V := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · intro u hu
      change (0:ℝ) ≤ rootValue
      rw [rootValue_exact]
      norm_num
    · intro u hu
      exact evalR_nonneg (later j).V (later_metadata j).2.2.2.1 u hu.1
  sum_le_potential := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · intro u hu
      simp [U,V,potential]
    · intro u hu
      rw [potential_later]
      exact (evalR_sum (later j) (future j) (later_metadata j) u).symm.le
  dual := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · intro k hk u hu
      have hk1 : k = 1 := le_antisymm (by simpa only [Fin.val_zero,capacity,Nat.cast_one] using hk.2) hk.1
      have hu1 : u = 1 := le_antisymm (by simpa only [Fin.val_zero,capacity,Nat.cast_one] using hu.2) hu.1
      subst k; subst u
      have hr : retained 2 2 1 1 = 1 := by norm_num [retained]
      have hp0 : (primes 0:ℝ) = 3 := by norm_num [primes]
      simp only [hp0,show (3:ℝ)-1 = 2 by norm_num]
      change 1-retained 2 2 1 1 +
        (∑ d : Option (Fin (E 0)),coefficient (retained 2 2 1 1)
          (fun j => 2*truncatedTail 3 1 (E 0) j) (E 0) d * evalR stage5.F (multiplier d*1)) ≤
          0+(rootValue:ℝ)
      simp only [hr,sub_self,zero_add,cap_tail]
      rw [finite_coefficient_op 3 2 1 (by norm_num)]
      exact root_finite_bound (E 0)
    · intro k hk u hu
      have hp : (primes j.succ:ℝ) = (later j).p := by exact_mod_cast primes_later j
      simp only [cap,cut,U,V,Fin.cases_succ,potential_future,hp,cap_tail]
      exact scalar_dual (later j) (future j) (later_valid j) (later_metadata j) (E j.succ) k u hk.1 hu.1

#print axioms schedule
end Erdos7Capped19Schedule
