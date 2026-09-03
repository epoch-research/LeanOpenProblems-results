import Submission.PatternPacking

/-! A finite survivor criterion using CRT-pattern packing constraints.
The required numerical positivity remains an explicit hypothesis. -/
namespace Erdos970.PatternPacking

open Erdos970.BlockSieve

/-- Nonnegative weighted packing indicators have a uniform total upper bound. -/
theorem weighted_pattern_union_sum_le {ι : Type*} [Fintype ι]
    (m : ℕ) (F : ι → Finset (Finset ℕ)) (w : ι → ℝ) (r : ℕ → ℕ)
    (hw : ∀ a, 0 ≤ w a)
    (hprime : ∀ a A, A ∈ F a → ∀ p ∈ A, p.Prime)
    (hcommon : ∀ a A, A ∈ F a → ∀ B ∈ F a, m ≤ ∏ p ∈ A ∩ B, p) :
    (∑ i ∈ Finset.range m, ∑ a,
      w a * if ∃ A ∈ F a, ∀ p ∈ A, i ≡ r p [MOD p] then (1 : ℝ) else 0) ≤
        ∑ a, w a := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro a ha
  rw [← Finset.mul_sum, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hc : (((Finset.range m).filter (fun i =>
      ∃ A ∈ F a, ∀ p ∈ A, i ≡ r p [MOD p])).card : ℝ) ≤ 1 := by
    exact_mod_cast pattern_union_card_le_one m (F a) r (hprime a) (hcommon a)
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hc (hw a)

/-- A rounded lower estimate exceeding a weighted packing budget forces a survivor. -/
theorem survivor_of_packing_certificate {ι : Type*} [Fintype ι]
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (m : ℕ) (r : ℕ → ℕ)
    (S : SievePolynomial) (hS : S.SupportedOn P)
    (F : ι → Finset (Finset ℕ)) (w : ι → ℝ)
    (hw : ∀ a, 0 ≤ w a)
    (hprime : ∀ a A, A ∈ F a → ∀ p ∈ A, p.Prime)
    (hcommon : ∀ a A, A ∈ F a → ∀ B ∈ F a, m ≤ ∏ p ∈ A ∩ B, p)
    (hpoint : ∀ i < m, (∃ p ∈ P, i ≡ r p [MOD p]) →
      S.value r i ≤ ∑ a, w a *
        if ∃ A ∈ F a, ∀ p ∈ A, i ≡ r p [MOD p] then (1 : ℝ) else 0)
    (hmain : (∑ a, w a) < S.roundedMain m) :
    ∃ i < m, ∀ p ∈ P, ¬i ≡ r p [MOD p] := by
  classical
  by_contra hbad
  push_neg at hbad
  have hlo := S.roundedMain_le_interval
    (fun a p hp => hP p (hS a hp)) r m
  have hmid : (∑ i ∈ Finset.range m, S.value r i) ≤
      ∑ i ∈ Finset.range m, ∑ a, w a *
        if ∃ A ∈ F a, ∀ p ∈ A, i ≡ r p [MOD p] then (1 : ℝ) else 0 := by
    apply Finset.sum_le_sum
    intro i hi
    exact hpoint i (Finset.mem_range.mp hi) (hbad i (Finset.mem_range.mp hi))
  exact hmain.not_ge (hlo.trans (hmid.trans
    (weighted_pattern_union_sum_le m F w r hw hprime hcommon)))

#print axioms survivor_of_packing_certificate

end Erdos970.PatternPacking
