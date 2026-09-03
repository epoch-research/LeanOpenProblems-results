import Submission.FirstHitSelberg
import Submission.SelbergSharpUpper

/-! The first-hit lower sieve using exact ordinary coefficient costs. -/
namespace Erdos970.FiniteSelberg
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]

/-- A conditional first-hit survivor criterion with the exact kernel L1 cost. -/
theorem survivor_of_first_hit_cost (q : ι → ℝ)
    (hq : ∀ i, 0 < q i ∧ q i < 1)
    (D : ι → Finset (Finset ι)) (hDn : ∀ i, (D i).Nonempty)
    (hD : ∀ i, ∀ A ∈ D i, ∀ B ⊆ A, B ∈ D i)
    (hprior : ∀ i, ∀ Q ∈ D i, ∀ j ∈ Q, j < i)
    (m : ℕ) (ω : ℕ → ι → Bool)
    (herr : ∀ T : Finset ι,
      |(∑ j ∈ Finset.range m, hitMonomial T (ω j)) - (m : ℝ) * ∏ i ∈ T, q i| ≤ 1)
    (hmain : (m : ℝ) * (∑ i, q i / normalizer q (D i)) +
      (∑ i, kernelCost q (canonicalOrthogonal q (D i)) ^ 2) < m) :
    ∃ j < m, ∀ i, ω j i = false := by
  classical
  by_contra hbad
  push_neg at hbad
  have hlower : (m : ℝ) ≤ ∑ j ∈ Finset.range m,
      ∑ i, hitMonomial {i} (ω j) * majorant q (D i) (ω j) := by
    calc
      _ = ∑ j ∈ Finset.range m, (1 : ℝ) := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro j hj
        apply first_hit_sum_ge_one q hq D hDn hprior (ω j)
        intro heq
        obtain ⟨i, hi⟩ := hbad j (Finset.mem_range.mp hj)
        exact hi (congrFun heq i)
  have hbound (i : ι) :
      (∑ j ∈ Finset.range m, hitMonomial {i} (ω j) * majorant q (D i) (ω j)) ≤
      (m : ℝ) * (q i / normalizer q (D i)) + kernelCost q (canonicalOrthogonal q (D i)) ^ 2 := by
    have he := arbitrary_square_hit_error q (canonicalOrthogonal q (D i)) m ω herr {i}
    simp only [linearKernel_canonical] at he
    change |(∑ j ∈ Finset.range m, hitMonomial {i} (ω j) * majorant q (D i) (ω j)) -
      (m : ℝ) * average q (fun v => hitMonomial {i} v * majorant q (D i) v)| ≤
      kernelCost q (canonicalOrthogonal q (D i)) ^ 2 at he
    have hnot (Q : Finset ι) (hQ : Q ∈ D i) : i ∉ Q := by
      intro hi
      exact lt_irrefl i (hprior i Q hQ i hi)
    rw [majorant_hit_average_of_not_mem q hq (D i) (hDn i) (hD i) i hnot] at he
    linarith [(abs_le.mp he).2]
  rw [Finset.sum_comm] at hlower
  have hupper := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hbound i)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hupper
  exact hmain.not_ge (hlower.trans hupper)


#print axioms survivor_of_first_hit_cost
end Erdos970.FiniteSelberg
