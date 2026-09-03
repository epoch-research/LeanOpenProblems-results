import Submission.RectangleBudgetTower
import Submission.Shared47Scalar

/-! A suffix schedule beginning after the ternary/quinary block. The first
two rows are harmless zero-cap dummy rows; their densities are unrestricted. -/
namespace Erdos7Shared47Schedule
open scoped BigOperators
open Erdos7CompleteFamilyModel Erdos7Shared47Rows Erdos7Shared47Metadata
open Erdos7Shared47Real Erdos7Shared47Scalar
open Erdos7CappedRetentionRows Erdos7KernelFamilyCompression
set_option maxHeartbeats 3000000
set_option autoImplicit false
set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable

def later : Fin 12 → Stage := ![stage7,stage11,stage13,stage17,stage19,stage23,stage29,stage31,stage37,stage41,stage43,stage47]
def forms : ℕ → List ℚ
  | 2 => stage7.F
  | 3 => stage11.F
  | 4 => stage13.F
  | 5 => stage17.F
  | 6 => stage19.F
  | 7 => stage23.F
  | 8 => stage29.F
  | 9 => stage31.F
  | 10 => stage37.F
  | 11 => stage41.F
  | 12 => stage43.F
  | 13 => stage47.F
  | _ => terminal

def future (j : Fin 12) : List ℚ := forms (3+j.val)
noncomputable def potential (t : ℕ) : ℝ → ℝ :=
  if t<2 then fun _ => 1 else evalR (forms t)
noncomputable def cap : Fin 14 → ℝ := Fin.addCases (motive := fun _ : Fin 14 => ℝ) (fun _ : Fin 2 => 0) (fun j => (later j).cap)
noncomputable def cut : Fin 14 → ℝ := Fin.addCases (motive := fun _ : Fin 14 => ℝ) (fun _ : Fin 2 => 0) (fun j => (later j).cut)
noncomputable def U : Fin 14 → ℝ → ℝ := Fin.addCases (motive := fun _ : Fin 14 => ℝ → ℝ) (fun _ : Fin 2 => fun _ => 0) (fun j => evalR (later j).U)
noncomputable def V : Fin 14 → ℝ → ℝ := Fin.addCases (motive := fun _ : Fin 14 => ℝ → ℝ) (fun _ : Fin 2 => fun _ => 1) (fun j => evalR (later j).V)

lemma later_metadata (j : Fin 12) : Metadata (later j) (future j) := by
  fin_cases j
  · exact stage7_metadata
  · exact stage11_metadata
  · exact stage13_metadata
  · exact stage17_metadata
  · exact stage19_metadata
  · exact stage23_metadata
  · exact stage29_metadata
  · exact stage31_metadata
  · exact stage37_metadata
  · exact stage41_metadata
  · exact stage43_metadata
  · exact stage47_metadata

lemma forms_later (j : Fin 12) : forms (2+j.val)=(later j).F := by fin_cases j <;> rfl
lemma potential_later (j : Fin 12) : potential (j.natAdd 2).val=evalR (later j).F := by
  simp only [potential,Fin.val_natAdd,show ¬2+j.val<2 by omega,if_false,forms_later]
lemma potential_future (j : Fin 12) : potential ((j.natAdd 2).val+1)=evalR (future j) := by
  simp only [potential,Fin.val_natAdd,show ¬2+j.val+1<2 by omega,if_false,future]
  congr 2
  omega
lemma potential_early (i : Fin 2) : potential (i.castAdd 12).val=fun _ => 1 := by
  simp only [potential,Fin.val_castAdd,if_pos i.isLt]

lemma evalR_terminal : evalR terminal = fun _ => 0 := by
  funext x
  have hc (j : ℕ) : coeff terminal j = 0 := by
    dsimp only [coeff,terminal]
    rw [List.getElem?_replicate]
    split_ifs <;> rfl
  simp only [evalR,Erdos7FiniteHingeFunctions.eval,hc,Rat.cast_zero,zero_mul,
    zero_add,Finset.sum_const_zero]
lemma potential_terminal : potential 14=fun _ => 0 := by
  simpa only [potential,show ¬(14:ℕ)<2 by omega,if_false,forms] using evalR_terminal
lemma potential_two : potential 2=evalR stage7.F := by rfl

noncomputable def flatTail (D j : ℕ) : ℝ := if j<D then 1 else 0
lemma flatTail_nonneg (D j : ℕ) : 0≤flatTail D j := by unfold flatTail; split_ifs <;> norm_num
lemma flatTail_decreasing (D j : ℕ) : flatTail D (j+1)≤flatTail D j := by
  unfold flatTail
  split_ifs <;> try norm_num
  omega
lemma flatTail_mass (D : ℕ) : (∑ a : Fin D,(1/((D:ℝ)+1))*flatTail D a.val)≤1 := by
  simp only [flatTail,if_pos (Fin.isLt _),mul_one,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  have hD : (0:ℝ)<D+1 := by positivity
  rw [mul_one_div]
  apply (div_le_one hD).mpr
  linarith

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
lemma zero_cap (q k : ℝ) : retained q 0 0 k=0 := by
  unfold retained
  split_ifs <;> norm_num

variable (A : Fin 14 → Type) [∀ i,Fintype (A i)] [∀ i,Nonempty (A i)] [∀ i,DecidableEq (A i)]
variable (E : Fin 14 → ℕ) (X : Pattern E → ∀ i,Finset (A i))
noncomputable def q : Fin 14 → ℝ := Fin.addCases (motive := fun _ : Fin 14 => ℝ)
  (fun i : Fin 2 => 1/((E (i.castAdd 12):ℝ)+1)) (fun j => (later j).p-1)
noncomputable def tail : Fin 14 → ℕ → ℝ := Fin.addCases (motive := fun _ : Fin 14 => ℕ → ℝ)
  (fun i : Fin 2 => flatTail (E (i.castAdd 12)))
  (fun j => truncatedTail (later j).p 1 (E (j.natAdd 2)))

/-- Numerical validity is supplied separately by the exact stage checks.
No density restriction is needed at either already-processed coordinate. -/
noncomputable def schedule
    (hvalid : ∀ j,Valid (later j) (future j))
    (ρ : ∀ i,A i → ℝ) (hρ : ∀ i y,0≤ρ i y) (hρmass : ∀ i,(∑ y,ρ i y)=1)
    (hd : ∀ j : Fin 12,∀ k,exponent E k (j.natAdd 2)≠0 →
      (∑ y,if y∈X k (j.natAdd 2) then ρ (j.natAdd 2) y else 0)≤
        1/((later j).p:ℝ)^(exponent E k (j.natAdd 2))) : BudgetSchedule A E X where
  density := ρ
  q := q E
  cap := cap
  cut := cut
  tail := tail E
  potential := potential
  U := U
  V := V
  density_nonneg := hρ
  density_mass := hρmass
  q_pos := by
    intro i
    cases i using Fin.addCases (m := 2) (n := 12) with
    | left j =>
      simp only [q,Fin.addCases_left]
      positivity
    | right j =>
      simp only [q,Fin.addCases_right]
      have hh : (1:ℝ)<(later j).p := by exact_mod_cast (later_metadata j).1
      linarith
  cap_nonneg := by
    intro i
    cases i using Fin.addCases (m := 2) (n := 12) with
    | left j =>
      simp [cap]
    | right j =>
      simpa only [cap,Fin.addCases_right] using (Rat.cast_nonneg.mpr (later_metadata j).2.1 : (0:ℝ)≤(later j).cap)
  tail_nonneg := by
    intro i
    cases i using Fin.addCases (m := 2) (n := 12) with
    | left j =>
      intro d _
      simp only [tail,Fin.addCases_left]
      exact flatTail_nonneg _ _
    | right j =>
      intro d _
      simp only [tail,Fin.addCases_right]
      exact truncatedTail_nonneg _ _ (by exact_mod_cast (later_metadata j).1) (by norm_num) _ _
  tail_decreasing := by
    intro i
    cases i using Fin.addCases (m := 2) (n := 12) with
    | left j =>
      simp only [tail,Fin.addCases_left]
      exact flatTail_decreasing _
    | right j =>
      simp only [tail,Fin.addCases_right]
      exact truncatedTail_decreasing _ _ (by exact_mod_cast (later_metadata j).1) (by norm_num) _
  tail_zero := by
    intro i
    cases i using Fin.addCases (m := 2) (n := 12) with
    | left j =>
      simp [tail,flatTail]
    | right j =>
      simp [tail,truncatedTail]
  current_mass := by
    intro i
    cases i using Fin.addCases (m := 2) (n := 12) with
    | left j =>
      simpa only [q,tail,Fin.addCases_left] using flatTail_mass (E (j.castAdd 12))
    | right j =>
      simpa only [q,tail,Fin.addCases_right] using geometric_mass (later j).p
        (by exact_mod_cast (later_metadata j).1) (E (j.natAdd 2))
  box_density := by
    intro i
    cases i using Fin.addCases (m := 2) (n := 12) with
    | left j =>
      intro k hk
      have hl : exponent E k (j.castAdd 12)-1<E (j.castAdd 12) := by have := exponent_bound E k (j.castAdd 12); omega
      simp only [tail,Fin.addCases_left,flatTail,if_pos hl]
      rw [← hρmass (j.castAdd 12)]
      apply Finset.sum_le_sum
      intro y _
      split_ifs
      · rfl
      · exact hρ _ _
    | right j =>
      intro k hk
      have hl : exponent E k (j.natAdd 2)-1<E (j.natAdd 2) := by have := exponent_bound E k (j.natAdd 2); omega
      simpa only [tail,Fin.addCases_right,truncatedTail,if_pos hl,
        show exponent E k (j.natAdd 2)-1+1=exponent E k (j.natAdd 2) by omega] using hd j k hk
  convex_U := by
    intro i
    cases i using Fin.addCases (m := 2) (n := 12) with
    | left j =>
      simp only [U,Fin.addCases_left]
      exact convexOn_const _ convex_univ
    | right j =>
      simp only [U,Fin.addCases_right]
      exact evalR_convex (later j).U (later_metadata j).2.2.1
  monotone_U := by
    intro i
    cases i using Fin.addCases (m := 2) (n := 12) with
    | left j =>
      simp only [U,Fin.addCases_left]
      exact monotone_const
    | right j =>
      simp only [U,Fin.addCases_right]
      exact evalR_monotone (later j).U (later_metadata j).2.2.1
  nonneg_V := by
    intro i
    cases i using Fin.addCases (m := 2) (n := 12) with
    | left j =>
      intro u hu
      norm_num [V]
    | right j =>
      intro u hu
      simp only [V,Fin.addCases_right]
      exact evalR_nonneg (later j).V (later_metadata j).2.2.2.1 u hu.1
  sum_le_potential := by
    intro i
    cases i using Fin.addCases (m := 2) (n := 12) with
    | left j =>
      intro u hu
      simp only [U,V,Fin.addCases_left,potential_early,zero_add,le_refl]
    | right j =>
      intro u hu
      rw [potential_later]
      simp only [U,V,Fin.addCases_right]
      exact (evalR_sum (later j) (future j) (later_metadata j) u).symm.le
  dual := by
    intro i
    cases i using Fin.addCases (m := 2) (n := 12) with
    | left j =>
      intro k hk u hu
      simp only [cap,cut,U,V,Fin.addCases_left,zero_cap,zero_mul]
      simp [Erdos7CappedRetentionRows.coefficient]
    | right j =>
      intro k hk u hu
      simp only [q,cap,cut,tail,U,V,Fin.addCases_right,potential_future,cap_tail]
      exact scalar_dual (later j) (future j) (hvalid j) (later_metadata j)
        (E (j.natAdd 2)) k u hk.1 hu.1

#print axioms schedule
end Erdos7Shared47Schedule
