import FormalConjecturesUtil

/-! Compactness for compatible finite-coordinate selections. The feasibility
hypothesis is uniform over every finite prefix. -/
namespace Erdos66FiniteChoiceCompactness
open scoped Topology Classical
set_option maxHeartbeats 1000000

variable (q : ℕ → ℕ) [∀ i, NeZero (q i)]

def restrict (L : ℕ) (ω : ∀ i : ℕ, Fin (q i)) : ∀ i : Fin L, Fin (q i.val) := fun i ↦ ω i.val

def restrictFinite {L M : ℕ} (h : M ≤ L) (ω : ∀ i : Fin L, Fin (q i.val)) :
    ∀ i : Fin M, Fin (q i.val) := fun i ↦ ω ⟨i.val, lt_of_lt_of_le i.isLt h⟩

lemma restrict_restrictFinite {L M : ℕ} (h : M ≤ L) (ω : ∀ i : ℕ, Fin (q i)) :
    restrictFinite q h (restrict q L ω) = restrict q M ω := rfl

lemma continuous_restrict (L : ℕ) : Continuous (restrict q L) := by
  exact continuous_pi (fun i ↦ continuous_apply i.val)

/-- If every finite problem is feasible and restrictions preserve feasibility,
one choice satisfies every finite problem simultaneously. -/
theorem exists_coherent (Good : (L : ℕ) → (∀ i : Fin L, Fin (q i.val)) → Prop)
    (hne : ∀ L, ∃ ω, Good L ω)
    (hrestrict : ∀ L M (h : M ≤ L) ω, Good L ω → Good M (restrictFinite q h ω)) :
    ∃ ω : ∀ i : ℕ, Fin (q i), ∀ L, Good L (restrict q L ω) := by
  let C : ℕ → Set (∀ i : ℕ, Fin (q i)) := fun L ↦ {ω | Good L (restrict q L ω)}
  have hclosed (L : ℕ) : IsClosed (C L) := by
    exact (isClosed_discrete (s := {ω | Good L ω})).preimage (continuous_restrict q L)
  have hnonempty (L : ℕ) : (C L).Nonempty := by
    obtain ⟨ω, hω⟩ := hne L
    let ω' : ∀ i : ℕ, Fin (q i) := fun i ↦ if h : i < L then ω ⟨i,h⟩ else 0
    refine ⟨ω', ?_⟩
    have he : restrict q L ω' = ω := by
      funext i
      simp [restrict, ω', i.isLt]
    change Good L (restrict q L ω')
    rw [he]
    exact hω
  have hmono (L : ℕ) : C (L+1) ⊆ C L := by
    intro ω hω
    exact hrestrict (L+1) L (by omega) (restrict q (L+1) ω) hω
  obtain ⟨ω, hω⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed C
    hmono hnonempty (hclosed 0).isCompact hclosed
  exact ⟨ω, Set.mem_iInter.mp hω⟩

/-- Hit counts can only decrease when coordinates are discarded. -/
lemma hits_restrict_le {L M : ℕ} (h : M ≤ L)
    (S : ∀ i : ℕ, Finset (Fin (q i))) (ω : ∀ i : Fin L, Fin (q i.val)) :
    (∑ i : Fin M, if restrictFinite q h ω i ∈ S i.val then (1 : ℝ) else 0) ≤
      ∑ i : Fin L, if ω i ∈ S i.val then (1 : ℝ) else 0 := by
  let f : Fin M → Fin L := fun i ↦ ⟨i.val, lt_of_lt_of_le i.isLt h⟩
  have hf : Function.Injective f := by
    intro i j he
    exact Fin.ext (congrArg (fun k : Fin L ↦ k.val) he)
  have hh := Finset.sum_le_sum_of_subset_of_nonneg
    (s := Finset.univ.image f) (t := Finset.univ)
    (f := fun i : Fin L ↦ if ω i ∈ S i.val then (1 : ℝ) else 0)
    (Finset.subset_univ _) (fun _ _ _ ↦ by dsimp only; split_ifs <;> norm_num)
  rw [Finset.sum_image (fun i _ j _ he ↦ hf he)] at hh
  exact hh

end Erdos66FiniteChoiceCompactness
