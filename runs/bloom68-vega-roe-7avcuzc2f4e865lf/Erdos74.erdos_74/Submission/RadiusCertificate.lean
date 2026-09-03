import FormalConjecturesUtil
import Submission.CertificateDefs
import OwnSubmission.WalkCover
import OwnSubmission.RepresentativeConstraints
import OwnSubmission.Branching

/-!
# Edge certificates from a bounded-radius walk cover

Suppose `B ≤ H`, a Boolean coloring is proper on `B`, and every vertex has a
walk in `B` of length at most `R` to one of at most `2 * t` roots. If deleting
fewer than `t` edges never makes `H` bipartite, there is a finite edge set of
size at most `radiusCertificateBound t R` containing at least `t`
monochromatic edges for every Boolean coloring.

After deleting a fault set `A`, add its endpoints to the roots. There are at
most `4 * t` resulting roots. Representative constraints give an oracle of
size at most `radiusOracleBound t R`, disjoint from `A`; finite branching
then gives the certificate. Neither the vertex type nor the graph needs to
be finite, and `t = 0` is allowed.
-/

namespace Erdos74.Certificates

/-- The maximum size of one representative certificate after fewer than `t`
faults, starting with at most `2 * t` roots and walk radius `R`. -/
def radiusOracleBound (t R : ℕ) : ℕ := (2 * R + 1) * (8 * t) ^ 2

/-- The size bound for the depth-`t` branching certificate built from the
bounded-radius oracle. -/
def radiusCertificateBound (t R : ℕ) : ℕ :=
  branchSize t (radiusOracleBound t R) t

@[simp] theorem radiusOracleBound_zero (R : ℕ) : radiusOracleBound 0 R = 0 := by
  simp [radiusOracleBound]

@[simp] theorem radiusCertificateBound_zero (R : ℕ) :
    radiusCertificateBound 0 R = 0 := rfl

universe u
variable {V : Type u}

/-- The bounded-radius oracle. A non-bipartite deletion has a uniformly bounded
finite edge certificate disjoint from the fault set `A`. The faults need not
be edges of `H`, and no finiteness assumption on `V` is required. -/
theorem exists_radius_oracle
    {B H : SimpleGraph V} (hBH : B ≤ H)
    (c : V → Bool) (hc : ∀ ⦃v w : V⦄, B.Adj v w → c v ≠ c w)
    (S : Finset V) {t R : ℕ} (hS : S.card ≤ 2 * t)
    (hcover : ∀ v : V, ∃ s ∈ S, ∃ p : B.Walk v s, p.length ≤ R)
    (A : Finset (Sym2 V)) (hA : A.card < t)
    (hfarA : ¬(H.deleteEdges (A : Set (Sym2 V))).IsBipartite) :
    ∃ Q : Finset (Sym2 V), (Q : Set (Sym2 V)) ⊆ H.edgeSet ∧
      Disjoint Q A ∧ Q.card ≤ radiusOracleBound t R ∧
      ∀ d : V → Bool, ∃ e ∈ Q, mono d e := by
  classical
  let K : Finset V := S ∪ endVerts A
  have hKcard : K.card ≤ 4 * t := by
    calc
      K.card ≤ S.card + (endVerts A).card := Finset.card_union_le _ _
      _ ≤ 2 * t + 2 * A.card := Nat.add_le_add hS (card_endVerts_le A)
      _ ≤ 4 * t := by omega
  have hPD : B.deleteEdges (A : Set (Sym2 V)) ≤
      H.deleteEdges (A : Set (Sym2 V)) := SimpleGraph.deleteEdges_mono hBH
  have hcP : ∀ ⦃v w : V⦄,
      (B.deleteEdges (A : Set (Sym2 V))).Adj v w → c v ≠ c w :=
    fun _ _ h => hc (SimpleGraph.deleteEdges_adj.mp h).1
  have hcoverP : ∀ v : V, ∃ r ∈ K,
      ∃ p : (B.deleteEdges (A : Set (Sym2 V))).Walk v r, p.length ≤ R :=
    radius_after_deletion S A hcover
  obtain ⟨Q, hQD, hQcard, hQbad⟩ :=
    exists_representative_certificate_of_walk_cover hPD c hcP K hcoverP hfarA
  have hQdiff : (Q : Set (Sym2 V)) ⊆ H.edgeSet \ (A : Set (Sym2 V)) := by
    simpa only [SimpleGraph.edgeSet_deleteEdges] using hQD
  refine ⟨Q, fun _ he => (hQdiff he).1, ?_, ?_, hQbad⟩
  · exact Finset.disjoint_left.mpr (fun _ heQ heA => (hQdiff heQ).2 heA)
  · apply hQcard.trans
    have hroots : 2 * K.card ≤ 8 * t := by omega
    unfold radiusOracleBound
    simpa only [pow_two] using
      Nat.mul_le_mul_left (2 * R + 1) (Nat.mul_le_mul hroots hroots)

/-- A bounded walk cover of a properly Boolean-colored subgraph gives a finite
certificate with at least `t` monochromatic edges for every Boolean coloring,
provided every deletion of fewer than `t` edges leaves `H` non-bipartite.
This is the generic graph-pair theorem: it uses neither finiteness of `V`,
positivity of `t`, nor a minimum bipartizing deletion. -/
theorem exists_radius_certificate
    {B H : SimpleGraph V} (hBH : B ≤ H)
    (c : V → Bool) (hc : ∀ ⦃v w : V⦄, B.Adj v w → c v ≠ c w)
    (S : Finset V) {t R : ℕ} (hS : S.card ≤ 2 * t)
    (hcover : ∀ v : V, ∃ s ∈ S, ∃ p : B.Walk v s, p.length ≤ R)
    (hfar : ∀ A : Finset (Sym2 V), A.card < t →
      ¬(H.deleteEdges (A : Set (Sym2 V))).IsBipartite) :
    ∃ Q : Finset (Sym2 V), (Q : Set (Sym2 V)) ⊆ H.edgeSet ∧
      Q.card ≤ radiusCertificateBound t R ∧
      ∀ d : V → Bool, t ≤ (Q.filter (mono d)).card := by
  exact exists_branching_certificate mono H.edgeSet t (radiusOracleBound t R)
    (fun A hA _ => exists_radius_oracle hBH c hc S hS hcover A hA (hfar A hA))

/-- Finite-vertex specialization: it suffices that every Boolean coloring of
`H` has at least `t` bad edges. Only this specialization needs `[Finite V]`. -/
theorem exists_radius_certificate_of_badEdges [Finite V]
    {B H : SimpleGraph V} (hBH : B ≤ H)
    (c : V → Bool) (hc : ∀ ⦃v w : V⦄, B.Adj v w → c v ≠ c w)
    (S : Finset V) {t R : ℕ} (hS : S.card ≤ 2 * t)
    (hcover : ∀ v : V, ∃ s ∈ S, ∃ p : B.Walk v s, p.length ≤ R)
    (hfar : ∀ d : V → Bool, t ≤ (badEdges H d).card) :
    ∃ Q : Finset (Sym2 V), (Q : Set (Sym2 V)) ⊆ H.edgeSet ∧
      Q.card ≤ radiusCertificateBound t R ∧
      ∀ d : V → Bool, t ≤ (Q.filter (mono d)).card := by
  apply exists_radius_certificate hBH c hc S hS hcover
  intro A hA hbip
  obtain ⟨d, _, hd⟩ := exists_badEdges_card_le_of_isBipartite_deleteEdges hbip
  exact (Nat.not_le_of_lt hA) ((hfar d).trans hd)

end Erdos74.Certificates
