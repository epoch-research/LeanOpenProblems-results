import Submission.TwoTargetShortSelection

/-! A single block is uniformly good for every product prefix and both
bounded targets, by adversarially selecting a bad target/prefix pair. -/
namespace Erdos371.FiniteSieve
open Finset Filter
open scoped Topology

theorem exists_small_power_for_two_target_maximal_selection (k : ℕ) (Mb ε : ℝ)
    (hε : 0 < ε) :
    ∃ K : ℕ, 0 < K ∧ ∀ M : ℝ, ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ N : ℕ in atTop,
      ∀ (P : Finset ℕ) (A B : ℕ → Finset ℕ) (G : Bool → ℕ → ℝ),
      (∀ p ∈ P, p.Prime ∧ (p : ℝ) ≤ (N : ℝ)^δ) →
      (2*∑ p ∈ P, (1 : ℝ)/p) ≤ M →
      (∀ i j, i < j → j < K → A i ⊆ A j) →
      (∀ i j, i < j → j < K → A j\A i ⊆ P) →
      (∀ i, i < K → B i ⊆ P) →
      (∀ i j, i < j → j < K → Disjoint (B i) (B j)) →
      (∀ i, i < K → (2*∑ p ∈ B i, (1 : ℝ)/p) ≤ Mb) →
      (∀ t n, n < N → |G t n| ≤ 1) →
      ∃ i < K, ∀ t : Bool, ∀ X : ℕ, |(∑ n ∈ range N, G t n*
        localPatternWitness (A i) P (shortComplementPattern (B i) X k) n)/N| < ε := by
  classical
  obtain ⟨K,hK,h⟩ := exists_small_power_for_two_target_short_selection k Mb ε hε
  refine ⟨K,hK,?_⟩
  intro M
  obtain ⟨δ,hδ,h⟩ := h M
  refine ⟨δ,hδ,?_⟩
  filter_upwards [h] with N hN
  intro P A B G hP hmass hnest hdiff hBP hdisj hMb hG
  by_contra hbad
  push_neg at hbad
  let Bad (i : ℕ) (p : Bool × ℕ) : Prop := ε ≤ |(∑ n ∈ range N, G p.1 n*
    localPatternWitness (A i) P (shortComplementPattern (B i) p.2 k) n)/N|
  let C (i : ℕ) : Bool × ℕ := if h : ∃ p, Bad i p then Classical.choose h else (false,0)
  have hC (i : ℕ) (hi : i < K) : Bad i (C i) := by
    have he : ∃ p, Bad i p := by
      obtain ⟨t,X,hX⟩ := hbad i hi
      exact ⟨(t,X),hX⟩
    dsimp only [C]
    rw [dif_pos he]
    exact Classical.choose_spec he
  obtain ⟨i,hi,hcorr⟩ := hN P A B (fun i => (C i).2) G (fun i => (C i).1)
    hP hmass hnest hdiff hBP hdisj hMb hG
  exact (not_lt_of_ge (hC i hi)) hcorr

#print axioms exists_small_power_for_two_target_maximal_selection
end Erdos371.FiniteSieve
