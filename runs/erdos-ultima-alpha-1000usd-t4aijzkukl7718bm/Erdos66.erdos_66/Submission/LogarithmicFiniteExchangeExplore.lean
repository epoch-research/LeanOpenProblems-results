import Submission.FiniteExchangeCapExplore
import Submission.LogarithmicMaximalCapExplore

/-! Even rigidity under arbitrary finite deletion-and-insertion exchanges
does not force a logarithmic representation limit under a fixed cap. -/
namespace Erdos66LogarithmicFiniteExchange
open Filter AdditiveCombinatorics Erdos66PointwiseCapBlocking
  Erdos66FiniteExchangeCap Erdos66LogarithmicMaximalCap Erdos66Explore
open scoped Topology Classical
set_option maxHeartbeats 1600000

/-- Any admissible competitor that deletes only finitely many old points
can only decrease representations when the set has finite-deletion rigidity. -/
lemma representation_le_of_finite_deletion (q : ℕ → ℕ) (A B : Set ℕ)
    (hrigid : ∀ C : Set ℕ, Capped q C → (A \ C).Finite → C⊆A)
    (hB : Capped q B) (hfin : (A \ B).Finite) (n : ℕ) :
    sumRep B n ≤ sumRep A n :=
  sumRep_mono (hrigid B hB hfin) n

lemma finite_exchange_additions_are_old (q : ℕ → ℕ) (A : Set ℕ)
    (hrigid : ∀ C : Set ℕ, Capped q C → (A \ C).Finite → C⊆A)
    (D F : Finset ℕ) (hcap : Capped q ((A \ (D:Set ℕ)) ∪ (F:Set ℕ))) :
    (F:Set ℕ)⊆A := by
  have hfin : (A \ ((A \ (D:Set ℕ)) ∪ (F:Set ℕ))).Finite := by
    apply D.finite_toSet.subset
    intro x hx
    by_contra hxD
    exact hx.2 (Or.inl ⟨hx.1,hxD⟩)
  exact Set.Subset.trans Set.subset_union_right (hrigid _ hcap hfin)

/-- Rigidity here is strictly stronger than inclusion-maximality: finitely
many deletions cannot unlock even ONE previously omitted point. -/
theorem exists_finitely_rigid_log_cap_without_limit (c : ℝ) (hc : 0<c) :
    ∃ A : Set ℕ, (∀ n, sumRep A n≤logCap c n) ∧
      (∀ B : Set ℕ, (∀ n, sumRep B n≤logCap c n) → (A \ B).Finite → B⊆A) ∧
      (∀ K : ℕ, ∃ n≥K, sumRep A n=0) ∧
      (∀ K : ℕ, ∃ n≥K, logCap c n≤sumRep A n+1) ∧
      ∀ d : ℝ, ¬ Tendsto (fun n ↦ (sumRep A n:ℝ)/Real.log n) atTop (𝓝 d) := by
  obtain ⟨A,hcap,hrigid,hholes,hpeaks⟩ := exists_finitely_rigid_with_holes_and_peaks
    (logCap c) (logCap_top c hc)
    (subquartic_of_log_ratio (logCap c) c (logCap_ratio c hc.le))
  exact ⟨A,hcap,hrigid,hholes,hpeaks,
    holes_peaks_no_limit (logCap c) c hc (logCap_ratio c hc.le) A hholes hpeaks⟩

/-- In particular, a bad capped set can be stable under every finite
exchange, of any size, not only under single-point insertion. -/
theorem exists_all_finite_exchanges_blocked (c : ℝ) (hc : 0<c) :
    ∃ A : Set ℕ, Capped (logCap c) A ∧
      (∀ D F : Finset ℕ, Capped (logCap c) ((A \ (D:Set ℕ)) ∪ (F:Set ℕ)) →
        (F:Set ℕ)⊆A) ∧
      (∀ K : ℕ, ∃ n≥K, sumRep A n=0) ∧
      ∀ d : ℝ, ¬ Tendsto (fun n ↦ (sumRep A n:ℝ)/Real.log n) atTop (𝓝 d) := by
  obtain ⟨A,hcap,hrigid,hholes,hpeaks,hnolim⟩ :=
    exists_finitely_rigid_log_cap_without_limit c hc
  exact ⟨A,hcap,finite_exchange_additions_are_old (logCap c) A hrigid,hholes,hnolim⟩

end Erdos66LogarithmicFiniteExchange
