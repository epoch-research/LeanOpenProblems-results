import Submission.CoordinatePushBounds

/-! A cardinal-density lower bound for uncovered points from family budgets. -/
namespace Erdos7DeficitFamilyBudget
open scoped BigOperators
open Erdos7CappedRetentionRows Erdos7FiniteRetentionKernel Erdos7KernelFamilyCompression
open Erdos7CompleteFamilyModel
set_option maxHeartbeats 2500000
set_option autoImplicit false
set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable

variable {n : ℕ}

def prefixCap (c : Fin n → ℝ) : ℕ → ℝ
  | 0 => 1
  | t+1 => if h:t < n then c ⟨t,h⟩*prefixCap c t else prefixCap c t

variable {A : Fin n → Type} [∀ i,Fintype (A i)] [∀ i,Nonempty (A i)]
  [∀ i,DecidableEq (A i)]
variable {E : Fin n → ℕ} {X : Pattern E → ∀ i,Finset (A i)}

theorem exists_bounded_stage (S : BudgetSchedule A E X)
    (huniform : ∀ i y,S.density i y = 1/(Fintype.card (A i):ℝ))
    (μ₀ : (∀ i,A i) → ℝ) (hμ₀ : ∀ x,0 ≤ μ₀ x) (D₀ : ℝ) (hD₀ : ∀ x,μ₀ x ≤ D₀)
    (t : ℕ) (ht : t ≤ n) :
    ∃ μ : (∀ i,A i) → ℝ,(∀ x,0 ≤ μ x) ∧ AvoidsBefore A E X t μ ∧
      (∀ x,μ x ≤ prefixCap S.cap t*D₀) ∧
      (∀ δ : ℝ, HasBudget δ μ (count A X : Family E (exponent E) t → _)
          (S.potential t) 1 (capacity E t) →
        HasBudget δ μ₀ (count A X : Family E (exponent E) 0 → _)
          (S.potential 0) 1 (capacity E 0)) := by
  induction t with
  | zero =>
    refine ⟨μ₀,hμ₀,?_,by simpa only [prefixCap,one_mul] using hD₀,fun _ => id⟩
    intro i hi
    omega
  | succ t ih =>
    have htn : t < n := by omega
    let i : Fin n := ⟨t,htn⟩
    obtain ⟨μ,hμ,havoid,hbound,hback⟩ := ih (by omega)
    obtain ⟨ν,hν,hcap,hzero,hmass,hstep⟩ := exists_rectangle_budget_step A E X t htn μ hμ
      (S.density i) (S.density_nonneg i) (S.density_mass i)
      (S.q i) (S.cap i) (S.cut i) (S.q_pos i) (S.cap_nonneg i)
      (S.tail i) (S.tail_nonneg i) (S.tail_decreasing i) (S.tail_zero i)
      (S.current_mass i) (S.box_density i) (S.U i) (S.V i)
      (S.potential t) (S.potential (t+1))
      (S.convex_U i) (S.monotone_U i) (S.nonneg_V i) (S.sum_le_potential i) (S.dual i)
    let f : ((∀ i,A i) × A i) → (∀ i,A i) := fun z => Function.update z.1 i z.2
    let μ' := push f (fun z => ν z.1 z.2)
    refine ⟨μ',push_nonneg f _ (fun z => hν z.1 z.2),?_,?_,?_⟩
    · exact push_avoidsBefore A E X t htn μ havoid ν hν (S.cap i) (S.density i) hcap hzero
    · intro x
      have hb := Erdos7CoordinatePushBounds.push_uniform_bound A i μ
        (prefixCap S.cap t*D₀) (S.cap i) (S.cap_nonneg i) hbound ν
        (fun x y => by simpa only [huniform i y] using hcap x y) x
      simpa only [prefixCap,dif_pos htn,mul_assoc] using hb
    · exact fun δ => hback δ ∘ hstep δ



noncomputable def uncovered (A : Fin n → Type) [∀ i,Fintype (A i)]
    [∀ i,Nonempty (A i)] [∀ i,DecidableEq (A i)]
    (E : Fin n → ℕ) (X : Pattern E → ∀ i,Finset (A i)) : Finset (∀ i,A i) :=
  Finset.univ.filter (fun x => ¬∃ k : Pattern E,(∃ i,exponent E k i ≠ 0) ∧
    indicator A n (exponent E k) (X k) x = 1)

/-- Quantitative form of the finite rectangle obstruction. -/
theorem uncovered_card_bound (S : BudgetSchedule A E X)
    (huniform : ∀ i y,S.density i y = 1/(Fintype.card (A i):ℝ))
    (hterminal : S.potential n = fun _ => 0) :
    (Fintype.card (∀ i,A i):ℝ)*(1-S.potential 0 1) ≤
      (uncovered A E X).card*prefixCap S.cap n := by
  let μ₀ : (∀ i,A i) → ℝ := fun _ => 1
  obtain ⟨μ,hμ,havoid,hbound,hback⟩ := exists_bounded_stage S huniform μ₀
    (fun _ => by norm_num [μ₀]) 1 (fun _ => le_rfl) n le_rfl
  have hb := terminal_budget μ (count A X : Family E (exponent E) n → _) 1 (capacity E n)
  rw [← hterminal] at hb
  have hstart := hback (∑ x,μ x) hb
  have hmass := constant_count_bound _ μ₀ (count A X : Family E (exponent E) 0 → _)
    (S.potential 0) 1 (capacity E 0) 1 (fun _ => by norm_num [μ₀])
    (by simp [capacity]) (count_initial A X) hstart
  simp only [μ₀,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] at hmass
  apply hmass.trans
  apply Erdos7CoordinatePushBounds.mass_le_card_mul (uncovered A E X) μ _
    (by simpa only [mul_one] using hbound)
  intro x hx
  have hcovered : ∃ k : Pattern E,(∃ i,exponent E k i ≠ 0) ∧
      indicator A n (exponent E k) (X k) x = 1 := by
    simpa only [uncovered,Finset.mem_filter,Finset.mem_univ,true_and,not_not] using hx
  obtain ⟨k,hk,hkx⟩ := hcovered
  obtain ⟨i,hi⟩ := full_box_has_layer A E X k hk x hkx
  exact havoid i i.isLt x hi

#print axioms uncovered_card_bound
end Erdos7DeficitFamilyBudget
