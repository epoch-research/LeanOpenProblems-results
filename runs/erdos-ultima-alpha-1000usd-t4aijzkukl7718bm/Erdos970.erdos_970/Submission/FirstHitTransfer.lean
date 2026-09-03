import Submission.FirstHitSelberg
import Submission.SieveCertificateTransfer

/-! First-hit lower polynomials and coordinatewise marginal transfer.
All coefficient costs are displayed; no asymptotic hypothesis is hidden. -/
namespace Erdos970.FiniteSelberg
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev FirstHitTerm (ι : Type*) := Option (ι × (Finset ι × Finset ι))

noncomputable def firstHitCoefficient (q : ι → ℝ) (D : ι → Finset (Finset ι)) : FirstHitTerm ι → ℝ
  | none => 1
  | some (i, T, R) => if T ∈ D i then
      if R ∈ D i then -(coefficient q (D i) T * coefficient q (D i) R) else 0 else 0

def firstHitTermSupport : FirstHitTerm ι → Finset ι
  | none => ∅
  | some (i, T, R) => {i} ∪ (T ∪ R)

lemma firstHitCoefficient_sum (q : ι → ℝ) (D : ι → Finset (Finset ι)) (f : FirstHitTerm ι → ℝ) :
    (∑ t : FirstHitTerm ι, firstHitCoefficient q D t * f t) =
      f none - ∑ i, ∑ T ∈ D i, ∑ R ∈ D i,
        (coefficient q (D i) T * coefficient q (D i) R) * f (some (i, T, R)) := by
  simp only [Fintype.sum_option, Fintype.sum_prod_type, firstHitCoefficient, one_mul,
    ite_mul, zero_mul, neg_mul]
  simp only [sum_ite_irrel, sum_ite_mem, univ_inter, sum_const_zero]
  simp only [sum_neg_distrib]
  ring

lemma firstHitCoefficient_value (q : ι → ℝ) (D : ι → Finset (Finset ι))
    (hD : ∀ i, ∀ A ∈ D i, ∀ B ⊆ A, B ∈ D i) (ω : ι → Bool) :
    (∑ t : FirstHitTerm ι, firstHitCoefficient q D t * hitMonomial (firstHitTermSupport t) ω) =
      1 - ∑ i, hitMonomial {i} ω * majorant q (D i) ω := by
  rw [firstHitCoefficient_sum]
  simp only [firstHitTermSupport]
  rw [show hitMonomial (∅ : Finset ι) ω = 1 by simp [hitMonomial]]
  congr 1
  apply sum_congr rfl
  intro i hi
  rw [majorant_expansion q (D i) (hD i), mul_sum]
  apply sum_congr rfl
  intro T hT
  rw [mul_sum]
  apply sum_congr rfl
  intro R hR
  change coefficient q (D i) T * coefficient q (D i) R * hitMonomial ({i} ∪ (T ∪ R)) ω = _
  rw [← hitMonomial_mul]
  ring

lemma firstHitCoefficient_cost_le (q : ι → ℝ) (hq : ∀ i, 0 < q i ∧ q i < 1)
    (D : ι → Finset (Finset ι)) (hDn : ∀ i, (D i).Nonempty)
    (hD : ∀ i, ∀ A ∈ D i, ∀ B ⊆ A, B ∈ D i) :
    (∑ t : FirstHitTerm ι, |firstHitCoefficient q D t|) ≤ 1 + ∑ i, ((D i).card : ℝ) ^ 2 := by
  simp only [Fintype.sum_option, Fintype.sum_prod_type, firstHitCoefficient, abs_one,
    apply_ite abs, abs_zero, abs_neg]
  simp only [sum_ite_irrel, sum_ite_mem, univ_inter, sum_const_zero]
  apply add_le_add le_rfl
  apply sum_le_sum
  intro i hi
  calc
    _ ≤ ∑ T ∈ D i, ∑ R ∈ D i, (1 : ℝ) := by
      apply sum_le_sum
      intro T hT
      apply sum_le_sum
      intro R hR
      rw [abs_mul]
      have h1 := coefficient_abs_le_one q hq (D i) (hDn i) (hD i) T
      have h2 := coefficient_abs_le_one q hq (D i) (hDn i) (hD i) R
      nlinarith [abs_nonneg (coefficient q (D i) T), abs_nonneg (coefficient q (D i) R)]
    _ = _ := by simp [pow_two]

section Ordered
variable [LinearOrder ι]

lemma firstHitCoefficient_mean (q : ι → ℝ) (hq : ∀ i, 0 < q i ∧ q i < 1)
    (D : ι → Finset (Finset ι)) (hDn : ∀ i, (D i).Nonempty)
    (hD : ∀ i, ∀ A ∈ D i, ∀ B ⊆ A, B ∈ D i)
    (hprior : ∀ i, ∀ Q ∈ D i, ∀ j ∈ Q, j < i) :
    (∑ t : FirstHitTerm ι, firstHitCoefficient q D t * ∏ i ∈ firstHitTermSupport t, q i) =
      1 - ∑ i, q i / normalizer q (D i) := by
  have hmean : (∑ t : FirstHitTerm ι, firstHitCoefficient q D t * ∏ i ∈ firstHitTermSupport t, q i) =
      average q (fun ω => ∑ t : FirstHitTerm ι,
        firstHitCoefficient q D t * hitMonomial (firstHitTermSupport t) ω) := by
    rw [average_sum]
    simp_rw [average_mul_const, average_hitMonomial]
  rw [hmean]
  simp_rw [firstHitCoefficient_value q D hD]
  rw [average_sub, average_const, average_sum]
  congr 1
  apply sum_congr rfl
  intro i hi
  exact majorant_hit_average_of_not_mem q hq (D i) (hDn i) (hD i) i
    (fun Q hQ hiQ => lt_irrefl i (hprior i Q hQ i hiQ))

/-- Reference first-hit kernels can be used at smaller actual prime-hit
marginals, with the same total absolute coefficient budget. -/
theorem survivor_of_dominating_first_hit (q q' : ι → ℝ)
    (hq : ∀ i, q i < 1 ∧ q i ≤ q' i ∧ q' i ≤ 1)
    (hq' : ∀ i, 0 < q' i ∧ q' i < 1)
    (D : ι → Finset (Finset ι)) (hDn : ∀ i, (D i).Nonempty)
    (hD : ∀ i, ∀ A ∈ D i, ∀ B ⊆ A, B ∈ D i)
    (hprior : ∀ i, ∀ Q ∈ D i, ∀ j ∈ Q, j < i)
    (m : ℕ) (ω : ℕ → ι → Bool)
    (herr : ∀ T : Finset ι,
      |(∑ j ∈ range m, hitMonomial T (ω j)) - (m : ℝ) * ∏ i ∈ T, q i| ≤ 1)
    (hmain : (m : ℝ) * (∑ i, q' i / normalizer q' (D i)) +
      1 + (∑ i, ((D i).card : ℝ) ^ 2) < m) :
    ∃ j < m, ∀ i, ω j i = false := by
  apply survivor_from_dominating_moments univ (firstHitCoefficient q' D) firstHitTermSupport q q' hq m ω herr
  · intro v hv
    rw [firstHitCoefficient_value q' D hD]
    linarith [first_hit_sum_ge_one q' hq' D hDn hprior v hv]
  · rw [firstHitCoefficient_mean q' hq' D hDn hD hprior]
    have hc := firstHitCoefficient_cost_le q' hq' D hDn hD
    nlinarith

end Ordered
#print axioms survivor_of_dominating_first_hit
end Erdos970.FiniteSelberg
