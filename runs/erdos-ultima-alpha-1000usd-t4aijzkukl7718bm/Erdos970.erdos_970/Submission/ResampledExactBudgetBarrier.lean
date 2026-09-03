import Submission.ResampledExposureCriterion

/-! Exact finite-budget comparison for the resampled Markov method. Averaged
partial-count floors are explicit hypotheses. This is a restriction on that
method, not a disproof of the quadratic Jacobsthal conjecture. -/
namespace Erdos970.SoftExposure
open Finset Real GapAverages
set_option maxHeartbeats 0

lemma density_le_one' (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) : density P ≤ 1 := by
  apply prod_le_one
  · intro p hp
    have hh : (1 : ℝ) ≤ p := by exact_mod_cast (hP p hp).one_le
    exact sub_nonneg.mpr ((one_div_le_one_div_of_le (by norm_num) hh).trans_eq (by norm_num))
  · intro p hp
    have hh : (0 : ℝ) ≤ 1/(p : ℝ) := by positivity
    linarith

lemma one_sub_density_le_reciprocal_sum (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) : 1-density P ≤ ∑ p ∈ P, (p : ℝ)⁻¹ := by
  classical
  induction P using Finset.induction_on with
  | empty => simp [density]
  | @insert p P hp ih =>
    have hPP : ∀ q ∈ P, q.Prime := fun q hq => hP q (mem_insert_of_mem hq)
    have hi := ih hPP
    have hd := density_le_one' P hPP
    have hx : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
    have hm := mul_le_mul_of_nonneg_left hd hx
    rw [show density (insert p P) = (1-(p : ℝ)⁻¹)*density P by
      simp only [density,prod_insert hp,one_div], sum_insert hp]
    nlinarith only [hi,hm]

/-- If every remainder after fewer than d removals has reciprocal mass at
least a, the exact ordered budget is at least a^d. -/
lemma budget_lower_of_remaining_sums (d : ℕ) (P : Finset ℕ) (a : ℝ) (ha : 0 ≤ a)
    (hrem : ∀ T ⊆ P, T.card < d → a ≤ ∑ p ∈ P \ T, (p : ℝ)⁻¹) :
    a^d ≤ budget d P := by
  classical
  induction d generalizing P with
  | zero => simp [budget]
  | succ d ih =>
    have hsum := hrem ∅ (empty_subset _) (by simp)
    simp only [sdiff_empty] at hsum
    have hchild (p : ℕ) (hp : p ∈ P) : a^d ≤ budget d (P.erase p) := by
      apply ih
      intro T hT hTd
      have hpT : p ∉ T := fun hh => (mem_erase.mp (hT hh)).1 rfl
      have hTP : insert p T ⊆ P := insert_subset hp (hT.trans (erase_subset _ _))
      have hh := hrem (insert p T) hTP (by rw [card_insert_of_notMem hpT]; omega)
      have he : P \ insert p T = (P.erase p) \ T := by
        ext q
        simp only [mem_sdiff,mem_insert,mem_erase]
        tauto
      rwa [he] at hh
    calc
      a^(d+1) = (∑ p ∈ P, (p : ℝ)⁻¹)*a^d -
          ((∑ p ∈ P, (p : ℝ)⁻¹)-a)*a^d := by ring
      _ ≤ (∑ p ∈ P, (p : ℝ)⁻¹)*a^d := by
        exact sub_le_self _ (mul_nonneg (sub_nonneg.mpr hsum) (pow_nonneg ha d))
      _ = ∑ p ∈ P, (p : ℝ)⁻¹*a^d := by rw [sum_mul]
      _ ≤ budget (d+1) P := sum_le_sum (fun p hp =>
        mul_le_mul_of_nonneg_left (hchild p hp) (by positivity))

/-- Fixing one particular ordered prefix gives this elementary lower bound
on the full budget. No factorial multiplicity is needed here. -/
lemma core_weight_mul_budget_le (P Q : Finset ℕ) (hQP : Q ⊆ P) (d : ℕ) :
    (∏ q ∈ Q, (q : ℝ)⁻¹)*budget d (P \ Q) ≤ budget (d+Q.card) P := by
  classical
  induction Q using Finset.induction_on generalizing P with
  | empty => simp
  | @insert q Q hqQ ih =>
    have hqP : q ∈ P := hQP (mem_insert_self _ _)
    have hQe : Q ⊆ P.erase q := by
      intro p hp
      exact mem_erase.mpr ⟨fun he => hqQ (he ▸ hp), hQP (mem_insert_of_mem hp)⟩
    have hh := ih (P.erase q) hQe
    have he : P \ insert q Q = (P.erase q) \ Q := by
      ext p
      simp only [mem_sdiff,mem_insert,mem_erase]
      tauto
    rw [prod_insert hqQ,card_insert_of_notMem hqQ,he,mul_assoc,
      show d+(Q.card+1) = (d+Q.card)+1 by omega]
    have hmul := mul_le_mul_of_nonneg_left hh (show 0 ≤ (q : ℝ)⁻¹ by positivity)
    have hsingle := single_le_sum (s := P)
      (f := fun p : ℕ => (p : ℝ)⁻¹ * budget (d+Q.card) (P.erase p))
      (fun p hp => mul_nonneg (by positivity) (budget_nonneg _ _)) hqP
    exact hmul.trans hsingle

/-- Averaged partial floors force the exact tail budget to dominate the
survival-fraction power whenever the fully resampled mean is below b. -/
lemma budget_lower_of_averaged_floors (R : Finset ℕ) (hR : ∀ p ∈ R, p.Prime)
    (d : ℕ) (A b D : ℝ) (hA : 0 < A) (hbA : b ≤ A)
    (hmean : D*density R ≤ b)
    (hfloor : ∀ T ⊆ R, T.card < d → A ≤ D*density T) :
    (1-b/A)^d ≤ budget d R := by
  apply budget_lower_of_remaining_sums d R (1-b/A)
    (sub_nonneg.mpr ((div_le_one hA).mpr hbA))
  intro T hTR hTd
  have hf := hfloor T hTR hTd
  have hrem : 0 ≤ density (R \ T) := (density_pos _
    (fun p hp => hR p (mem_sdiff.mp hp).1)).le
  have he : density T * density (R \ T) = density R := by
    simpa only [density,mul_comm] using
      (Finset.prod_sdiff hTR (f := fun p : ℕ => 1-1/(p : ℝ)))
  have hh := mul_le_mul_of_nonneg_right hf hrem
  rw [mul_assoc,he] at hh
  have hr : density (R \ T) ≤ b/A :=
    (le_div_iff₀ hA).mpr (by simpa only [mul_comm] using hh.trans hmean)
  exact (sub_le_sub_left hr 1).trans
    (one_sub_density_le_reciprocal_sum _ (fun p hp => hR p (mem_sdiff.mp hp).1))

/-- Even the exact factorial budget cannot contradict the Markov-cylinder
expression when the averaged partial-count floors are consistent with D.
If a proposed D violates such a floor, that deterministic contradiction is
already available without the low-tail estimate. -/
theorem markov_expression_le_exact_budget (P Q : Finset ℕ) (hQP : Q ⊆ P)
    (hP : ∀ p ∈ P, p.Prime) (j : ℕ) (hQj : Q.card ≤ j)
    (A b D : ℝ) (hA : 0 < A) (hb : 0 < b) (hbA : b ≤ A) (hD : 0 ≤ D)
    (hfloor : ∀ T ⊆ P \ Q, T.card < j-Q.card → A ≤ D*density T) :
    (1-b/A)^j * ((1-D*density (P \ Q)/b)*(∏ q ∈ Q, (q : ℝ)⁻¹)) ≤ budget j P := by
  have hbase : 0 ≤ 1-b/A := sub_nonneg.mpr ((div_le_one hA).mpr hbA)
  have hbase1 : 1-b/A ≤ 1 := by have := div_nonneg hb.le hA.le; linarith
  have hw : 0 ≤ ∏ q ∈ Q, (q : ℝ)⁻¹ := prod_nonneg (fun _ _ => by positivity)
  have hrho : 0 ≤ density (P \ Q) := (density_pos _
    (fun p hp => hP p (mem_sdiff.mp hp).1)).le
  have hc1 : 1-D*density (P \ Q)/b ≤ 1 := by
    have := div_nonneg (mul_nonneg hD hrho) hb.le
    linarith
  by_cases hc : 1-D*density (P \ Q)/b ≤ 0
  · exact (mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hbase j)
      (mul_nonpos_of_nonpos_of_nonneg hc hw)).trans (budget_nonneg j P)
  · have hmean : D*density (P \ Q) ≤ b := (div_le_one hb).mp (by linarith only [hc])
    have hl := budget_lower_of_averaged_floors (P \ Q)
      (fun p hp => hP p (mem_sdiff.mp hp).1) (j-Q.card) A b D hA hbA hmean hfloor
    have hp : (1-b/A)^j ≤ (1-b/A)^(j-Q.card) :=
      pow_le_pow_of_le_one hbase hbase1 (Nat.sub_le j Q.card)
    have hc := core_weight_mul_budget_le P Q hQP (j-Q.card)
    rw [Nat.sub_add_cancel hQj] at hc
    calc
      _ ≤ (1-b/A)^j * (∏ q ∈ Q, (q : ℝ)⁻¹) := by
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg hbase j)
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hc1 hw
      _ ≤ budget (j-Q.card) (P \ Q)*(∏ q ∈ Q, (q : ℝ)⁻¹) :=
        mul_le_mul_of_nonneg_right (hp.trans hl) hw
      _ ≤ budget j P := by simpa only [mul_comm] using hc

#print axioms budget_lower_of_remaining_sums
#print axioms core_weight_mul_budget_le
#print axioms budget_lower_of_averaged_floors
#print axioms markov_expression_le_exact_budget
end Erdos970.SoftExposure
