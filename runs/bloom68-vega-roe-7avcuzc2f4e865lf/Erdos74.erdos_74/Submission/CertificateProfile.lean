import FormalConjecturesUtil
import Submission.CertificateDefs
import Submission.SpecBridges
import Submission.SlowBudget

/-!
# From finite edge certificates to a slow profile obstruction

Suppose every finite graph that is not three-colorable has a positive-parameter
Boolean edge certificate of size at most `N k`. The divergent budget
`slowBudget (fun k => 2 * N k)` then forces three-colorability on finite graphs:
the certificate is supported on at most `2 * N k` vertices, where the profile
allows fewer than `k` edge deletions, contradicting the certificate.

The compactness bridge extends this conclusion to arbitrary graphs and gives
the exact negation of the infinite-chromatic-profile assertion. This is a
conditional reduction: it assumes the finite certificate theorem and uses
neither a localization theorem nor a radius bound.
-/

namespace Erdos74.Certificates

open Filter

universe u
variable {V : Type u}

/-- A Boolean edge certificate lower-bounds any profile budget at the number
of its endpoints. The ambient graph need not be finite. -/
theorem le_profile_of_certificate {G : SimpleGraph V} {f : ℕ → ℕ}
    (hG : ∀ n, SimpleGraph.maxSubgraphEdgeDistToBipartite G n ≤ f n)
    {Q : Finset (Sym2 V)} {k : ℕ}
    (hQ : (Q : Set (Sym2 V)) ⊆ G.edgeSet)
    (hmono : ∀ d : V → Bool, k ≤ (Q.filter (mono d)).card) :
    k ≤ f (endVerts Q).card := by
  let S := endVerts Q
  let A : G.Subgraph := (⊤ : G.Subgraph).induce (S : Set V)
  have hA : A.verts.Finite := S.finite_toSet
  obtain ⟨E, _, hE, hcard, hbip⟩ :=
    SimpleGraph.exists_finite_bipartite_deletion_of_profile_le hG A hA
  have hcoe : (A.deleteEdges E).coe = (G.deleteEdges E).induce (S : Set V) := by
    ext v w
    simp [A, Function.Embedding.subtype]
  have hbip' : ((G.deleteEdges E).induce (S : Set V)).IsBipartite := by
    simpa only [hcoe] using hbip
  have hkE : k ≤ E.ncard :=
    le_ncard_ambient_deletion_of_certificate hQ Set.Subset.rfl hmono hE hbip'
  have hcard' : E.ncard ≤ f S.card := by
    simpa [A] using hcard
  exact hkE.trans hcard'

/-- A graph with the stated certificate alternative is three-colorable if
its profile is bounded by the slow budget for the endpoint thresholds.
No finiteness assumption is needed beyond the certificate alternative itself. -/
theorem colorable_of_profile_le_slowBudget_of_certificates (N : ℕ → ℕ)
    {G : SimpleGraph V}
    (hcertificate : ¬ G.Colorable 3 → ∃ k > 0, ∃ Q : Finset (Sym2 V),
      (Q : Set (Sym2 V)) ⊆ G.edgeSet ∧ Q.card ≤ N k ∧
        ∀ d : V → Bool, k ≤ (Q.filter (mono d)).card)
    (hG : ∀ n, SimpleGraph.maxSubgraphEdgeDistToBipartite G n ≤
      Erdos74Aux.slowBudget (fun k => 2 * N k) n) : G.Colorable 3 := by
  classical
  by_contra hcolor
  obtain ⟨k, hk, Q, hQ, hQcard, hmono⟩ := hcertificate hcolor
  have hsize : (endVerts Q).card ≤ 2 * N k :=
    (card_endVerts_le Q).trans (Nat.mul_le_mul_left 2 hQcard)
  have hlt : Erdos74Aux.slowBudget (fun k => 2 * N k) (endVerts Q).card < k :=
    Erdos74Aux.slowBudget_lt_of_le (fun k => 2 * N k)
      (Nat.succ_le_of_lt hk) hsize
  exact (Nat.not_le_of_lt hlt) (le_profile_of_certificate hG hQ hmono)

/-- Uniform finite edge certificates refute the infinite-chromatic-profile
assertion for the explicit divergent budget `slowBudget (fun k => 2 * N k)`.
The finite certificate hypothesis and the conclusion use the same arbitrary
universe. No monotonicity or growth assumption on `N` is required. -/
theorem not_erdos74_of_finite_certificates (N : ℕ → ℕ)
    (hfinite : ∀ (V : Type u) [Finite V] (G : SimpleGraph V),
      ¬ G.Colorable 3 → ∃ k > 0, ∃ Q : Finset (Sym2 V),
        (Q : Set (Sym2 V)) ⊆ G.edgeSet ∧ Q.card ≤ N k ∧
          ∀ d : V → Bool, k ≤ (Q.filter (mono d)).card) :
    ¬ (∀ f : ℕ → ℕ, Tendsto f atTop atTop →
      ∃ (V : Type u) (G : SimpleGraph V), G.chromaticNumber = ⊤ ∧
        ∀ n, SimpleGraph.maxSubgraphEdgeDistToBipartite G n ≤ f n) := by
  exact SimpleGraph.not_forall_exists_infinite_chromatic_profile
    (Erdos74Aux.slowBudget_tendsto (fun k => 2 * N k))
    (fun V _ G hG =>
      colorable_of_profile_le_slowBudget_of_certificates N (hfinite V G) hG)

end Erdos74.Certificates
