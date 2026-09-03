import Submission.GenericPrimePairs

/-!
The remaining exceptional set is contained in an explicit countable union of
closed nowhere-dense sets. Even the class of Liouville slopes contains a dense
set of solutions. Neither statement rules out an individual counterexample.
-/
namespace Erdos972ExceptionalSlopes

open Erdos972Topology Erdos972GenericPrimePairs Filter

def exceptionalHull : Set ℝ := ⋃ N : ℕ, (augmentedTail N)ᶜ

lemma closed_nowhereDense_exceptionalTail (N : ℕ) :
    IsClosed (augmentedTail N)ᶜ ∧ IsNowhereDense (augmentedTail N)ᶜ := by
  apply isClosed_isNowhereDense_iff_compl.mpr
  simpa only [compl_compl] using
    And.intro (isOpen_augmentedTail N) (dense_augmentedTail N)

lemma isMeagre_exceptionalHull : IsMeagre exceptionalHull :=
  isMeagre_iUnion fun N => (closed_nowhereDense_exceptionalTail N).2.isMeagre

lemma finite_primeSet_iff_mem_exceptionalHull {α : ℝ}
    (hα : 1 < α) (hI : Irrational α) :
    (primeSet α).Finite ↔ α ∈ exceptionalHull := by
  classical
  rw [← Set.not_infinite, infinite_iff_mem_all_primeTail (by linarith) hI]
  simp only [exceptionalHull, Set.mem_iUnion, Set.mem_compl_iff,
    augmentedTail, Set.mem_union, Set.mem_Iio, not_or]
  constructor
  · intro h
    push_neg at h
    obtain ⟨N, hN⟩ := h
    exact ⟨N, not_lt_of_ge hα.le, hN⟩
  · rintro ⟨N, _, hN⟩ h
    exact hN (h N)

lemma isMeagre_counterexampleSlopes :
    IsMeagre {α : ℝ | 1 < α ∧ Irrational α ∧ (primeSet α).Finite} := by
  apply isMeagre_exceptionalHull.mono
  rintro α ⟨hα, hI, hf⟩
  exact (finite_primeSet_iff_mem_exceptionalHull hα hI).mp hf

lemma eventually_residual_liouville_infinite_pairs :
    ∀ᶠ α : ℝ in residual ℝ,
      Liouville α ∧ (1 < α → (primeSet α).Infinite) := by
  filter_upwards [eventually_residual_liouville,
    eventually_residual_infinite_pairs] with α hL hP
  exact ⟨hL, hP.2⟩

/-- Arbitrarily strong rational approximability is compatible with infinitely
many genuine prime pairs; in particular it cannot alone supply a disproof. -/
theorem exists_liouville_infinite_pairs {a b : ℝ} (ha : 1 ≤ a) (hab : a < b) :
    ∃ α : ℝ, a < α ∧ α < b ∧ Liouville α ∧ (primeSet α).Infinite := by
  have hd : Dense {α : ℝ | Liouville α ∧ (1 < α → (primeSet α).Infinite)} :=
    dense_of_mem_residual eventually_residual_liouville_infinite_pairs
  obtain ⟨α, hα, hlo, hhi⟩ := hd.exists_mem_open isOpen_Ioo
    (Set.nonempty_Ioo.mpr hab)
  exact ⟨α, hlo, hhi, hα.1, hα.2 (ha.trans_lt hlo)⟩

#print axioms isMeagre_counterexampleSlopes
#print axioms exists_liouville_infinite_pairs

end Erdos972ExceptionalSlopes
