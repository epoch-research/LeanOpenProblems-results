import FormalConjecturesUtil
import Submission.CertificateProfile
import Submission.LocalizedColoring

/-! Verification of the assembled disproof from its component modules. -/
open Filter SimpleGraph
open Erdos74.Certificates

theorem disproofCheck.{u} : ¬ (∀ f : ℕ → ℕ, Tendsto f atTop atTop →
    ∃ (V : Type u) (G : SimpleGraph V), G.chromaticNumber = ⊤ ∧
      ∀ n, Erdos74.SimpleGraph.maxSubgraphEdgeDistToBipartite G n ≤ f n) := by
  exact not_erdos74_of_finite_certificates certificateBound
    finite_non_three_colorable_certificate

#print axioms Erdos74.Certificates.localized_coloring_or_certificate
#print axioms Erdos74.Certificates.finite_non_three_colorable_certificate
#print axioms disproofCheck
