import Submission.SoftExposureAverage

/-! The soft tree has the same factorial elementary-symmetric budget as
hard ordered exposure. The lower-tail penalty stays explicit. -/
namespace Erdos970.SoftExposure
open Finset Real GapAverages

lemma weighted_insert_sum (P : Finset ℕ) (p : ℕ) (hp : p ∈ P)
    (j : ℕ) (w : ℕ → ℝ) :
    (∑ Q ∈ (P.erase p).powersetCard j, w p * ∏ q ∈ Q, w q) =
      ∑ T ∈ (P.powersetCard (j + 1)).filter (fun T => p ∈ T), ∏ q ∈ T, w q := by
  classical
  apply sum_bij (fun Q _ => insert p Q)
  · intro Q hQ
    obtain ⟨hQP, hQj⟩ := mem_powersetCard.mp hQ
    have hpQ : p ∉ Q := fun hh => (mem_erase.mp (hQP hh)).1 rfl
    exact mem_filter.mpr ⟨mem_powersetCard.mpr
      ⟨insert_subset hp (hQP.trans (erase_subset _ _)), by rw [card_insert_of_notMem hpQ, hQj]⟩,
      mem_insert_self _ _⟩
  · intro Q hQ R hR heq
    have hpQ : p ∉ Q := fun hh => (mem_erase.mp ((mem_powersetCard.mp hQ).1 hh)).1 rfl
    have hpR : p ∉ R := fun hh => (mem_erase.mp ((mem_powersetCard.mp hR).1 hh)).1 rfl
    have hh := congrArg (fun S : Finset ℕ => S.erase p) heq
    simpa only [erase_insert hpQ, erase_insert hpR] using hh
  · intro T hT
    obtain ⟨hTP, hpT⟩ := mem_filter.mp hT
    obtain ⟨hTP, hTj⟩ := mem_powersetCard.mp hTP
    refine ⟨T.erase p, mem_powersetCard.mpr ⟨erase_subset_erase p hTP, ?_⟩, insert_erase hpT⟩
    rw [card_erase_of_mem hpT, hTj]
    omega
  · intro Q hQ
    have hpQ : p ∉ Q := fun hh => (mem_erase.mp ((mem_powersetCard.mp hQ).1 hh)).1 rfl
    exact (prod_insert hpQ).symm

lemma symmetric_erase_sum (P : Finset ℕ) (j : ℕ) (w : ℕ → ℝ) :
    (∑ p ∈ P, w p * ∑ Q ∈ (P.erase p).powersetCard j, ∏ q ∈ Q, w q) =
      (j + 1 : ℕ) * ∑ T ∈ P.powersetCard (j + 1), ∏ q ∈ T, w q := by
  classical
  simp_rw [mul_sum]
  have he (p : ℕ) (hp : p ∈ P) := weighted_insert_sum P p hp j w
  rw [sum_congr rfl he]
  simp_rw [sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro T hT
  obtain ⟨hTP, hTj⟩ := mem_powersetCard.mp hT
  have hf : P.filter (fun p => p ∈ T) = T := by ext p; simp only [mem_filter]; exact and_iff_right_of_imp (fun h => hTP h)
  rw [← sum_filter, hf, sum_const, hTj, nsmul_eq_mul]

lemma budget_eq_factorial_symmetric (j : ℕ) (P : Finset ℕ) :
    budget j P = (j.factorial : ℝ) *
      ∑ Q ∈ P.powersetCard j, ∏ q ∈ Q, (q : ℝ)⁻¹ := by
  induction j generalizing P with
  | zero => simp [budget]
  | succ j ih =>
    simp only [budget, ih]
    calc
      _ = (j.factorial : ℝ) *
          ∑ p ∈ P, (p : ℝ)⁻¹ * ∑ Q ∈ (P.erase p).powersetCard j, ∏ q ∈ Q, (q : ℝ)⁻¹ := by
        rw [mul_sum]
        apply sum_congr rfl
        intro p hp
        ring
      _ = _ := by rw [symmetric_erase_sum, Nat.factorial_succ, Nat.cast_mul]; ring

/-- The deterministic lower-count hypothesis replaces the hard no-cover
hypothesis. It yields the same symmetric budget with a survival-fraction loss. -/
theorem lowCountFraction_factorial_symmetric (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (m j : ℕ) (A b : ℝ) (hA : 0 < A) (hb : 0 ≤ b) (hbA : b ≤ A)
    (hpartial : ∀ r : Phase P, PartialLower j (range m) P (phaseResidues P r) A) :
    (1 - b / A) ^ j * lowCountFraction P m b ≤
      (j.factorial : ℝ) * ∑ Q ∈ P.powersetCard j, ∏ q ∈ Q, (q : ℝ)⁻¹ := by
  rw [← budget_eq_factorial_symmetric]
  exact lowCountFraction_mul_le_budget P hP m j A b hA hb hbA hpartial

/-- The old core-tail generating-function estimate also bounds the soft budget. -/
theorem budget_le_core_exponential (P S : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hS : S ⊆ P) (n : ℕ) (hn : 0 < n)
    (hhalf : (∑ p ∈ P \ S, (p : ℝ)⁻¹) ≤ 1 / 2) :
    budget (2 * n) P ≤ exp ((S.card : ℝ) * log (1 + 4 * (n : ℝ)) - (n : ℝ) / 16) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hw (p : ℕ) (hp : p ∈ P) : 0 ≤ (p : ℝ)⁻¹ ∧ (p : ℝ)⁻¹ ≤ 1 := by
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (hP p hp).one_le
    exact ⟨by positivity, inv_le_one_of_one_le₀ hp1⟩
  have he := symmetric_generating_bound P (fun p => (p : ℝ)⁻¹)
    (fun p hp => (hw p hp).1) (2 * n) (4 * n) (by positivity)
  have hg := generating_core_tail_bound P S hS (fun p => (p : ℝ)⁻¹) hw (4 * n) (by positivity) hhalf
  have hfac := factorial_two_mul_exp_le n
  have hpos : 0 < (4 * (n : ℝ)) ^ (2 * n) := by positivity
  have hcore : 0 ≤ (1 + 4 * (n : ℝ)) ^ S.card := by positivity
  have hpow : (1 + 4 * (n : ℝ)) ^ S.card = exp ((S.card : ℝ) * log (1 + 4 * (n : ℝ))) := by
    rw [exp_nat_mul, exp_log (by positivity)]
  have hh : (4 * (n : ℝ)) ^ (2 * n) * budget (2 * n) P ≤
      (4 * (n : ℝ)) ^ (2 * n) * ((1 + 4 * (n : ℝ)) ^ S.card * exp (-(n : ℝ) / 16)) := by
    rw [budget_eq_factorial_symmetric]
    have hb := mul_le_mul_of_nonneg_left (he.trans hg) (Nat.cast_nonneg (2 * n).factorial)
    have hd := mul_le_mul_of_nonneg_left hfac hcore
    norm_num only [show 4 * (n : ℝ) / 2 = 2 * (n : ℝ) by ring] at hb
    nlinarith only [hb, hd]
  have hfinal := (mul_le_mul_iff_right₀ hpos).mp hh
  rw [hpow, ← exp_add] at hfinal
  simpa only [neg_div, sub_eq_add_neg] using hfinal

#print axioms budget_eq_factorial_symmetric
#print axioms lowCountFraction_factorial_symmetric
#print axioms budget_le_core_exponential
end Erdos970.SoftExposure
