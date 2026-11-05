import Submission.ResidueBlockNodes

/-!
# Finite nonself-level counts

Counting prime-power divisibility levels is just counting a natural interval.
For sum entries, this interval count is exactly the excess over the baseline.
The cutoff need only bound the sum valuation; it need not bound the individual
vertex heights.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos126Aux.ResidueBlocks

noncomputable def levelCount (p z w M : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (M + 1), if p ^ k ∣ z ∧ ¬p ^ k ∣ w then 1 else 0

private theorem interval_count_eq (u v M : ℕ) (hv : v ≤ M) :
    (∑ k ∈ Finset.range (M + 1), if k ≤ v ∧ ¬k ≤ u then (1 : ℝ) else 0) =
      ((v - u : ℕ) : ℝ) := by
  have hf : (Finset.range (M + 1)).filter (fun k => k ≤ v ∧ ¬k ≤ u) =
      Finset.Ioc u v := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc]
    omega
  rw [Finset.sum_boole, hf, Nat.card_Ioc]

private theorem interval_count_le (u v M : ℕ) :
    (∑ k ∈ Finset.range (M + 1), if k ≤ v ∧ ¬k ≤ u then (1 : ℝ) else 0) ≤
      ((v - u : ℕ) : ℝ) := by
  have hf : (Finset.range (M + 1)).filter (fun k => k ≤ v ∧ ¬k ≤ u) ⊆
      Finset.Ioc u v := by
    intro k hk
    obtain ⟨_, hkv, hku⟩ := Finset.mem_filter.1 hk
    exact Finset.mem_Ioc.2 ⟨by omega, hkv⟩
  rw [Finset.sum_boole]
  exact_mod_cast (Finset.card_le_card hf).trans_eq (Nat.card_Ioc u v)

/-- Exact interval count for two nonzero natural numbers. -/
theorem levelCount_eq (p z w M : ℕ) (hp : p.Prime) (hz : z ≠ 0) (hw : w ≠ 0)
    (hM : z.factorization p ≤ M) :
    levelCount p z w M = ((z.factorization p - w.factorization p : ℕ) : ℝ) := by
  unfold levelCount
  simp_rw [hp.pow_dvd_iff_le_factorization hz, hp.pow_dvd_iff_le_factorization hw]
  exact interval_count_eq _ _ _ hM

/-- Truncating the levels can only decrease their count. -/
theorem levelCount_le (p z w M : ℕ) (hp : p.Prime) (hz : z ≠ 0) (hw : w ≠ 0) :
    levelCount p z w M ≤ ((z.factorization p - w.factorization p : ℕ) : ℝ) := by
  unfold levelCount
  simp_rw [hp.pow_dvd_iff_le_factorization hz, hp.pow_dvd_iff_le_factorization hw]
  exact interval_count_le _ _ _

variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
theorem baseline_eq_double_of_heights_eq (a : ι → ℕ) (p : ℕ) (i j : ι)
    (hi : 0 < a i) (heq : (a i).factorization p = (a j).factorization p) :
    primeBaseline a p i j = ((2 * a i).factorization p : ℝ) := by
  rw [factorization_two_mul hi]
  simp only [primeBaseline, ← heq, min_self, and_true, Nat.cast_add]
  split_ifs <;> simp

omit [Fintype ι] in
/-- Scalar sum-level count, expressed in the existing real baseline API. -/
theorem sum_levelCount_eq (a : ι → ℕ) (p M : ℕ) (i j : ι)
    (hp : p.Prime) (hi : 0 < a i) (hj : 0 < a j)
    (hM : (a i + a j).factorization p ≤ M) :
    levelCount p (a i + a j) (2 * a i) M =
      ((a i + a j).factorization p : ℝ) - primeBaseline a p i j := by
  rw [levelCount_eq p (a i + a j) (2 * a i) M hp (by omega) (by omega) hM]
  by_cases heq : (a i).factorization p = (a j).factorization p
  · rw [baseline_eq_double_of_heights_eq a p i j hi heq]
    apply Nat.cast_sub
    have hb := primeBaseline_le_factorization_add a hp i j hi hj
    rw [baseline_eq_double_of_heights_eq a p i j hi heq] at hb
    exact_mod_cast hb
  · rw [primeBaseline_eq_factorization_add_of_ne a hp i j hi hj heq, sub_self]
    have hle : (a i + a j).factorization p ≤ (2 * a i).factorization p := by
      rw [factorization_add_eq_min_of_ne hp hi hj heq, factorization_two_mul hi]
      exact (min_le_left _ _).trans (Nat.le_add_right _ _)
    simp only [Nat.sub_eq_zero_of_le hle, Nat.cast_zero]

/-- Entrywise cross-kernel representation, with the local prime-color
opposition lemma supplied separately. -/
theorem crossSum_eq_primeExcess_of_color_opposition (a : ι → ℕ) (S : Finset ℕ) (M : ℕ)
    (ha : ∀ i, 0 < a i) (hS : ∀ p ∈ S, p.Prime)
    (hM : ∀ p ∈ S, ∀ i j, (a i + a j).factorization p ≤ M)
    (hflip : ∀ p ∈ S, ∀ k i j, p ^ k ∣ a i + a j → ¬p ^ k ∣ 2 * a i →
      primeColor p (a i) ≠ primeColor p (a j)) (i j : ι) :
    Paired.crossSum (nodeBlock a S M) i j = primeExcessKernel a S i j := by
  rw [crossSum_eq_levels]
  calc
    _ = ∑ p : ↥S, Real.log (p : ℝ) * levelCount (p : ℕ) (a i + a j) (2 * a i) M := by
      apply Finset.sum_congr rfl
      intro p hp
      calc
        _ = ∑ k : Fin (M + 1),
            if (p : ℕ) ^ (k : ℕ) ∣ a i + a j ∧ ¬(p : ℕ) ^ (k : ℕ) ∣ 2 * a i
            then Real.log (p : ℝ) else 0 := by
          apply Finset.sum_congr rfl
          intro k hk
          exact crossLevel_eq a (p : ℕ) (k : ℕ) i j (Nat.pow_pos (hS p p.property).pos)
            (hflip p p.property k i j)
        _ = Real.log (p : ℝ) * levelCount (p : ℕ) (a i + a j) (2 * a i) M := by
          rw [Fin.sum_univ_eq_sum_range
            (fun k : ℕ => if (p : ℕ) ^ k ∣ a i + a j ∧ ¬(p : ℕ) ^ k ∣ 2 * a i
              then Real.log (p : ℝ) else 0) (M + 1)]
          unfold levelCount
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k hk
          split_ifs <;> simp
    _ = primeExcessKernel a S i j := by
      rw [Finset.sum_coe_sort S
        (fun p : ℕ => Real.log (p : ℝ) * levelCount p (a i + a j) (2 * a i) M)]
      unfold primeExcessKernel
      apply Finset.sum_congr rfl
      intro p hp
      rw [sum_levelCount_eq a p M i j (hS p hp) (ha i) (ha j) (hM p hp i j)]

end Erdos126Aux.ResidueBlocks
