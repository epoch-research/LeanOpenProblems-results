import Submission.ShortComplementSelection

/-! Uniform selection of a block for all complementary product prefixes.
The cutoff at each block may be chosen adversarially in the earlier selection
lemma, so its quantifiers yield a single uniformly good block. -/
namespace Erdos371.FiniteSieve
open Finset Filter
open scoped Topology

/-- No union bound over X is needed: choosing a bad X separately in every
block would contradict selection for arbitrary block-dependent cutoffs. -/
theorem exists_small_power_for_maximal_short_selection (k : ℕ) (Mb ε : ℝ)
    (hε : 0 < ε) :
    ∃ K : ℕ, 0 < K ∧ ∀ M : ℝ, ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ N : ℕ in atTop,
      ∀ (P : Finset ℕ) (A B : ℕ → Finset ℕ) (G : ℕ → ℝ),
      (∀ p ∈ P, p.Prime ∧ (p : ℝ) ≤ (N : ℝ)^δ) →
      (2*∑ p ∈ P, (1 : ℝ)/p) ≤ M →
      (∀ i j, i < j → j < K → A i ⊆ A j) →
      (∀ i j, i < j → j < K → A j\A i ⊆ P) →
      (∀ i, i < K → B i ⊆ P) →
      (∀ i j, i < j → j < K → Disjoint (B i) (B j)) →
      (∀ i, i < K → (2*∑ p ∈ B i, (1 : ℝ)/p) ≤ Mb) →
      (∀ n < N, |G n| ≤ 1) →
      ∃ i < K, ∀ X : ℕ, |(∑ n ∈ range N, G n*
        localPatternWitness (A i) P (shortComplementPattern (B i) X k) n)/N| < ε := by
  classical
  obtain ⟨K,hK,h⟩ := exists_small_power_for_short_complement_selection k Mb ε hε
  refine ⟨K,hK,?_⟩
  intro M
  obtain ⟨δ,hδ,h⟩ := h M
  refine ⟨δ,hδ,?_⟩
  filter_upwards [h] with N hN
  intro P A B G hP hmass hnest hdiff hBP hdisj hMb hG
  by_contra hbad
  push_neg at hbad
  let Bad (i X : ℕ) : Prop := ε ≤ |(∑ n ∈ range N, G n*
    localPatternWitness (A i) P (shortComplementPattern (B i) X k) n)/N|
  let X (i : ℕ) := if h : ∃ x, Bad i x then Classical.choose h else 0
  have hX (i : ℕ) (hi : i < K) : Bad i (X i) := by
    have he : ∃ x, Bad i x := hbad i hi
    dsimp only [X]
    rw [dif_pos he]
    exact Classical.choose_spec he
  obtain ⟨i,hi,hcorr⟩ := hN P A B X G hP hmass hnest hdiff hBP hdisj hMb hG
  exact (not_lt_of_ge (hX i hi)) hcorr

#print axioms exists_small_power_for_maximal_short_selection
end Erdos371.FiniteSieve
