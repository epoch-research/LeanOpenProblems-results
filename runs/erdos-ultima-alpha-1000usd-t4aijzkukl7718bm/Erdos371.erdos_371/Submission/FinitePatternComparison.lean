import Submission.BooleanPatternTruncation

/-! Comparison of arbitrary bounded finite-pattern observables using only
low-degree inclusion masses and a factorial-moment remainder. -/
namespace Erdos371.FiniteSieve
open Finset
variable {ι Ω : Type*} [DecidableEq ι]

noncomputable def patternInclusionMass (X : Finset Ω) (w : Ω → ℝ)
    (A : Ω → Finset ι) (T : Finset ι) : ℝ :=
  ∑ x ∈ X, if T ⊆ A x then w x else 0

lemma patternTruncation_universe (F : Finset ι → ℝ) (S A : Finset ι) (L : ℕ)
    (hA : A ⊆ S) :
    patternTruncation F A L =
      ∑ T ∈ S.powerset, if T.card < L ∧ T ⊆ A then patternDifference F T else 0 := by
  classical
  have he : S.powerset.filter (fun T => T ⊆ A) = A.powerset := by
    ext T
    simp only [mem_filter,mem_powerset]
    exact ⟨And.right,fun h => ⟨h.trans hA,h⟩⟩
  unfold patternTruncation
  rw [← he,sum_filter]
  apply sum_congr rfl
  intro T _
  split_ifs <;> simp_all

lemma patternTruncation_weighted_sum (F : Finset ι → ℝ) (S : Finset ι) (L : ℕ)
    (X : Finset Ω) (w : Ω → ℝ) (A : Ω → Finset ι)
    (hA : ∀ x ∈ X, A x ⊆ S) :
    (∑ x ∈ X, w x*patternTruncation F (A x) L) =
      ∑ T ∈ S.powerset, if T.card < L then
        patternDifference F T*patternInclusionMass X w A T else 0 := by
  classical
  calc
    _ = ∑ x ∈ X, ∑ T ∈ S.powerset, if T.card < L then
        patternDifference F T*(if T ⊆ A x then w x else 0) else 0 := by
      apply sum_congr rfl
      intro x hx
      rw [patternTruncation_universe F S (A x) L (hA x hx),mul_sum]
      apply sum_congr rfl
      intro T _
      split_ifs <;> simp_all; ring
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro T _
      by_cases hT : T.card < L
      · simp only [if_pos hT,← mul_sum,patternInclusionMass]
      · simp only [if_neg hT,sum_const_zero]

lemma pattern_factorial_moment (S : Finset ι) (L : ℕ)
    (X : Finset Ω) (w : Ω → ℝ) (A : Ω → Finset ι)
    (hA : ∀ x ∈ X, A x ⊆ S) :
    (∑ x ∈ X, w x*((A x).card.choose L)) =
      ∑ T ∈ S.powersetCard L, patternInclusionMass X w A T := by
  classical
  calc
    _ = ∑ x ∈ X, ∑ T ∈ S.powersetCard L, if T ⊆ A x then w x else 0 := by
      apply sum_congr rfl
      intro x hx
      have he : (S.powersetCard L).filter (fun T => T ⊆ A x) = (A x).powersetCard L := by
        ext T
        simp only [mem_filter,mem_powersetCard]
        exact ⟨fun h => ⟨h.2,h.1.2⟩,fun h => ⟨⟨h.1.trans (hA x hx),h.2⟩,h.1⟩⟩
      rw [← sum_filter,he,sum_const,card_powersetCard,nsmul_eq_mul,mul_comm]
    _ = _ := by rw [sum_comm]; rfl

/-- A bounded pattern observable can be compared to prescribed low-degree
inclusion data. No independence assumption on the original sample is needed. -/
theorem finite_pattern_comparison (F : Finset ι → ℝ) (S : Finset ι) (L : ℕ)
    (X : Finset Ω) (w : Ω → ℝ) (A : Ω → Finset ι)
    (hA : ∀ x ∈ X, A x ⊆ S) (hw : ∀ x ∈ X, 0 ≤ w x)
    (hF : ∀ T ⊆ S, |F T| ≤ 1)
    (ρ R : Finset ι → ℝ)
    (hR : ∀ T ⊆ S, T.card ≤ L →
      |patternInclusionMass X w A T-ρ T| ≤ R T) :
    |(∑ x ∈ X, w x*F (A x)) -
      ∑ T ∈ S.powerset, if T.card < L then patternDifference F T*ρ T else 0| ≤
      (1+3^L)*(∑ T ∈ S.powersetCard L, (ρ T+R T)) +
        ∑ T ∈ S.powerset, if T.card < L then (2 : ℝ)^T.card*R T else 0 := by
  classical
  let J : ℝ := ∑ x ∈ X, w x*patternTruncation F (A x) L
  have htail : |(∑ x ∈ X, w x*F (A x))-J| ≤
      (1+3^L)*(∑ T ∈ S.powersetCard L, (ρ T+R T)) := by
    dsimp only [J]
    rw [← sum_sub_distrib]
    calc
      _ ≤ ∑ x ∈ X, |w x*F (A x)-w x*patternTruncation F (A x) L| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ x ∈ X, w x*((1+3^L)*((A x).card.choose L)) := by
        apply sum_le_sum
        intro x hx
        rw [← mul_sub,abs_mul,abs_of_nonneg (hw x hx)]
        exact mul_le_mul_of_nonneg_left
          (patternTruncation_error F (A x) L (fun T hT => hF T (hT.trans (hA x hx)))) (hw x hx)
      _ = (1+3^L)*(∑ T ∈ S.powersetCard L, patternInclusionMass X w A T) := by
        rw [← pattern_factorial_moment S L X w A hA,mul_sum]
        apply sum_congr rfl
        intro x _
        ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply sum_le_sum
        intro T hT
        obtain ⟨hTS,hTL⟩ := mem_powersetCard.mp hT
        have h := (le_abs_self (patternInclusionMass X w A T-ρ T)).trans (hR T hTS hTL.le)
        linarith
  have hpoly : |J-(∑ T ∈ S.powerset, if T.card < L then patternDifference F T*ρ T else 0)| ≤
      ∑ T ∈ S.powerset, if T.card < L then (2 : ℝ)^T.card*R T else 0 := by
    dsimp only [J]
    rw [patternTruncation_weighted_sum F S L X w A hA,← sum_sub_distrib]
    apply (abs_sum_le_sum_abs _ _).trans
    apply sum_le_sum
    intro T hT
    by_cases hc : T.card < L
    · rw [if_pos hc,if_pos hc,if_pos hc,← mul_sub,abs_mul]
      apply mul_le_mul
        (patternDifference_abs_le F T fun U hU => hF U (hU.trans (mem_powerset.mp hT)))
        (hR T (mem_powerset.mp hT) hc.le) (abs_nonneg _) (by positivity)
    · simp only [if_neg hc,sub_self,abs_zero,le_refl]
  exact (abs_sub_le _ J _).trans (add_le_add htail hpoly)

/-- If model inclusion masses are bounded by product local densities, the
remainder is bounded by a power divided by a factorial. -/
theorem finite_pattern_comparison_factorial (F : Finset ι → ℝ) (S : Finset ι) (L : ℕ)
    (X : Finset Ω) (w : Ω → ℝ) (A : Ω → Finset ι)
    (hA : ∀ x ∈ X, A x ⊆ S) (hw : ∀ x ∈ X, 0 ≤ w x)
    (hF : ∀ T ⊆ S, |F T| ≤ 1)
    (ρ R : Finset ι → ℝ) (g : ι → ℝ) (hg : ∀ i ∈ S, 0 ≤ g i)
    (hρ : ∀ T ∈ S.powersetCard L, ρ T ≤ ∏ i ∈ T, g i)
    (hR : ∀ T ⊆ S, T.card ≤ L →
      |patternInclusionMass X w A T-ρ T| ≤ R T) :
    |(∑ x ∈ X, w x*F (A x)) -
      ∑ T ∈ S.powerset, if T.card < L then patternDifference F T*ρ T else 0| ≤
      (1+3^L)*((∑ i ∈ S, g i)^L/L.factorial + ∑ T ∈ S.powersetCard L, R T) +
        ∑ T ∈ S.powerset, if T.card < L then (2 : ℝ)^T.card*R T else 0 := by
  apply (finite_pattern_comparison F S L X w A hA hw hF ρ R hR).trans
  apply add_le_add _ le_rfl
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [sum_add_distrib]
  apply add_le_add _ le_rfl
  exact (sum_le_sum hρ).trans (elementarySum_le_pow_div_factorial S g hg L)

#print axioms finite_pattern_comparison_factorial
end Erdos371.FiniteSieve
