import Submission.BoundedTotientSupport
import Submission.TotientCertificates

/-!
# Growing-support reformulation of adjacent equal totients

This is an equivalence, not an assertion of either equivalent condition.
-/
namespace TotientReduction
open TotientCertificates

/-- Infinitude is equivalent to having collisions with arbitrarily many
    distinct prime factors in the two consecutive arguments together. -/
theorem infinitude_iff_unbounded_support :
    Set.Infinite {n : ℕ | n.totient = (n + 1).totient} ↔
      ∀ K : ℕ, ∃ n : ℕ, n.totient = (n + 1).totient ∧
        K < (n.primeFactors ∪ (n + 1).primeFactors).card := by
  classical
  constructor
  · intro hinf K
    obtain ⟨n, hn, hnew⟩ := (hinf.diff
      (BoundedTotientSupport.finite_bounded_totient_support K)).nonempty
    refine ⟨n, hn, ?_⟩
    have hnot : ¬ (n.primeFactors ∪ (n + 1).primeFactors).card ≤ K := by
      intro hcard
      exact hnew ⟨hn, hcard⟩
    omega
  · intro hunbounded
    by_contra hinf
    have hfinite := Set.not_infinite.mp hinf
    let f : ℕ → ℕ := fun n => (n.primeFactors ∪ (n + 1).primeFactors).card
    obtain ⟨K, hK⟩ := (Set.Finite.image f hfinite).bddAbove
    obtain ⟨n, hn, hlarge⟩ := hunbounded K
    have hbound : f n ≤ K := hK ⟨n, hn, rfl⟩
    exact (not_lt_of_ge hbound) hlarge

/-- A purely finite arithmetic reformulation.  To settle infinitude positively,
    it remains to construct these certificates with unbounded combined support. -/
theorem infinitude_iff_unbounded_certificates :
    Set.Infinite {n : ℕ | n.totient = (n + 1).totient} ↔
      ∀ K : ℕ, ∃ S T : Finset ℕ, SupportCertificate S T ∧ K < (S ∪ T).card := by
  rw [infinitude_iff_unbounded_support]
  constructor
  · intro h K
    obtain ⟨n, ht, hcard⟩ := h K
    exact ⟨n.primeFactors, (n + 1).primeFactors,
      adjacent_support_certificate ht, hcard⟩
  · intro h K
    obtain ⟨S, T, hc, hcard⟩ := h K
    obtain ⟨n, ht, hnS, hnT⟩ := (support_certificate_iff S T).mp hc
    refine ⟨n, ht, ?_⟩
    simpa only [hnS, hnT] using hcard

end TotientReduction
