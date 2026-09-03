import Submission.CompactnessExplore

/-! Compactness for a single uniform representation-error envelope. -/
namespace Erdos66RepEnvelopeCompactness
open Erdos66Compactness AdditiveCombinatorics
open scoped Topology Classical

/-- The initial threshold is fixed before every finite final cutoff. -/
theorem exists_of_finite_envelopes (target error : ℕ → ℝ) (N : ℕ)
    (h : ∀ L : ℕ, ∃ A : Set ℕ, ∀ n, N ≤ n → n ≤ L →
      |(sumRep A n : ℝ)-target n| ≤ error n) :
    ∃ A : Set ℕ, ∀ n, N ≤ n → |(sumRep A n : ℝ)-target n| ≤ error n := by
  let C : ℕ → Set (ℕ → Bool) := fun L ↦ {f | ∀ n, N≤n → n≤L →
    |encodedRep f n-target n| ≤ error n}
  have hclosed (L : ℕ) : IsClosed (C L) := by
    dsimp only [C]
    simp only [Set.setOf_forall]
    refine isClosed_iInter (fun n ↦ isClosed_iInter (fun _ ↦ isClosed_iInter (fun _ ↦ ?_)))
    exact isClosed_le ((continuous_encodedRep n).sub continuous_const).abs continuous_const
  have hne (L : ℕ) : (C L).Nonempty := by
    obtain ⟨A,hA⟩ := h L
    refine ⟨fun i ↦ decide (i∈A),fun n hn hnl ↦ ?_⟩
    rw [encodedRep_decide]
    exact hA n hn hnl
  have hmono (L : ℕ) : C (L+1) ⊆ C L := by
    intro f hf n hn hnl
    exact hf n hn (by omega)
  obtain ⟨f,hf⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed C
    hmono hne (hclosed 0).isCompact hclosed
  refine ⟨{i | f i=true},fun n hn ↦ ?_⟩
  have hh := Set.mem_iInter.mp hf n n hn le_rfl
  rwa [encodedRep_eq_sumRep] at hh

end Erdos66RepEnvelopeCompactness
