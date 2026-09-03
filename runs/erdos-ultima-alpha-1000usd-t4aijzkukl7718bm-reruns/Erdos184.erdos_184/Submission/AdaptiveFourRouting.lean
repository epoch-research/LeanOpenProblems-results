import Submission.FourTerminalSystems

/-!
Adaptive four-terminal sewing. The input hypothesis describes the alternatives
obtained after removing a parity-correcting matching: either separate marked
cycles give the requested pairing, or one marked cycle gives a strong pairing.
The matching-completion-to-routing implication is a separate obligation.
-/
open SimpleGraph
open scoped Classical
namespace Erdos184.TerminalRouting
variable {V : Type*} [Fintype V] {G : SimpleGraph V}
set_option maxHeartbeats 800000

structure Route (G A : SimpleGraph V) (t : Fin 4 → V) (i : Fin 3) where
  paths : PairedPaths G t i
  rest : Packing G
  disjoint : Disjoint rest.edges paths.edges
  cover : rest.edges ∪ paths.edges = A.edgeSet

lemma Route.paths_subset {A : SimpleGraph V} {t : Fin 4 → V} {i : Fin 3}
    (R : Route G A t i) : R.paths.edges ⊆ A.edgeSet := by
  rw [← R.cover]
  exact Set.subset_union_right

lemma Route.rest_subset {A : SimpleGraph V} {t : Fin 4 → V} {i : Fin 3}
    (R : Route G A t i) : R.rest.edges ⊆ A.edgeSet := by
  rw [← R.cover]
  exact Set.subset_union_left

omit [Fintype V] in
lemma walkVerts_subset_support {A : SimpleGraph V} {a b : V} (p : G.Walk a b)
    (hab : a ≠ b) (he : walkEdges p ⊆ A.edgeSet) : walkVerts p ⊆ A.support := by
  intro x hx
  obtain ⟨e,heP,hxe⟩ := (Walk.mem_support_iff_exists_mem_edges_of_not_nil
    (Walk.not_nil_of_ne hab)).mp hx
  have heA := he heP
  induction e using Sym2.ind with
  | h u v =>
    rcases Sym2.mem_iff.mp hxe with rfl | rfl
    · exact ⟨v,heA⟩
    · exact ⟨u,heA.symm⟩

lemma Route.verts_subset {A : SimpleGraph V} {t : Fin 4 → V} {i : Fin 3}
    (R : Route G A t i) (ht : Function.Injective t) : R.paths.verts ⊆ A.support := by
  have hfirst : (0 : Fin 4) ≠ firstEnd i := by fin_cases i <;> decide
  have hsecond : secondStart i ≠ secondEnd i := by fin_cases i <;> decide
  apply Set.union_subset
  · exact walkVerts_subset_support R.paths.p (fun h => hfirst (ht h))
      (Set.subset_union_left.trans R.paths_subset)
  · exact walkVerts_subset_support R.paths.q (fun h => hsecond (ht h))
      (Set.subset_union_right.trans R.paths_subset)

/-- Reattach the unmarked cycle pieces once the four paths have been sewn. -/
lemma sew_routes {A B : SimpleGraph V} {t : Fin 4 → V} {i j : Fin 3}
    (RA : Route G A t i) (RB : Route G B t j) (hd : Disjoint A.edgeSet B.edgeSet)
    (P : Packing G) (hP : P.edges = RA.paths.edges ∪ RB.paths.edges) :
    ∃ Q : Packing G, Q.edges = A.edgeSet ∪ B.edgeSet ∧
      Q.pieces.card ≤ RA.rest.pieces.card + RB.rest.pieces.card + P.pieces.card := by
  have hrest : Disjoint RA.rest.edges RB.rest.edges := hd.mono RA.rest_subset RB.rest_subset
  let T := RA.rest.union RB.rest hrest
  have hTP : Disjoint T.edges P.edges := by
    rw [show T.edges = RA.rest.edges ∪ RB.rest.edges from Packing.union_edges _ _ _,hP]
    apply Set.disjoint_left.mpr
    intro e he hf
    rcases he with he | he <;> rcases hf with hf | hf
    · exact Set.disjoint_left.mp RA.disjoint he hf
    · exact Set.disjoint_left.mp hd (RA.rest_subset he) (RB.paths_subset hf)
    · exact Set.disjoint_left.mp hd (RA.paths_subset hf) (RB.rest_subset he)
    · exact Set.disjoint_left.mp RB.disjoint he hf
  refine ⟨T.union P hTP,?_,?_⟩
  · rw [Packing.union_edges,show T.edges = RA.rest.edges ∪ RB.rest.edges from Packing.union_edges _ _ _,
      hP,← RA.cover,← RB.cover]
    ext e
    simp only [Set.mem_union]
    tauto
  · have h1 := T.union_card_le P hTP
    have h2 := RA.rest.union_card_le RB.rest hrest
    change T.pieces.card ≤ RA.rest.pieces.card+RB.rest.pieces.card at h2
    omega

/-- For each requested matching either retain that pairing at the two-piece
removal budget, or obtain some vertex-disjoint pairing at the one-piece budget. -/
def FourRoutingAlternatives (G A : SimpleGraph V) (t : Fin 4 → V) (K : ℕ) : Prop :=
  ∀ i : Fin 3,
    (∃ R : Route G A t i, R.rest.pieces.card+2 ≤ K) ∨
    (∃ j : Fin 3, ∃ R : Route G A t j, R.paths.Strong ∧ R.rest.pieces.card+1 ≤ K)

/-- Adaptive matching choice avoids the fixed-pairing obstruction. This
statement consumes explicit routing alternatives, not arbitrary path systems. -/
lemma adaptive_four_routing {A B : SimpleGraph V} {t : Fin 4 → V}
    (ht : Function.Injective t) (hd : Disjoint A.edgeSet B.edgeSet)
    (hi : A.support ∩ B.support ⊆ Set.range t) (hcover : A.edgeSet ∪ B.edgeSet = G.edgeSet)
    (kA kB : ℕ) (hA : FourRoutingAlternatives G A t kA)
    (hB : FourRoutingAlternatives G B t kB) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G D ∧ D.card ≤ kA+kB+4 := by
  have finish {i j : Fin 3} (RA : Route G A t i) (RB : Route G B t j)
      (hc : i = j ∨ RA.paths.Strong ∧ RB.paths.Strong)
      (hb : RA.rest.pieces.card + RB.rest.pieces.card + 6 ≤ kA+kB+4) :
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
        IsDecomposition G D ∧ D.card ≤ kA+kB+4 := by
    have hpd := hd.mono RA.paths_subset RB.paths_subset
    have hpv : RA.paths.verts ∩ RB.paths.verts ⊆ Set.range t := by
      intro x hx
      exact hi ⟨RA.verts_subset ht hx.1,RB.verts_subset ht hx.2⟩
    have hex : ∃ P : Packing G, P.edges = RA.paths.edges ∪ RB.paths.edges ∧ P.pieces.card ≤ 6 := by
      rcases hc with hij | hs
      · subst j
        exact paired_paths_compatible RA.paths RB.paths hpd hpv
      · exact paired_paths_strong ht RA.paths RB.paths hs.1 hs.2 hpd hpv
    obtain ⟨P,hP,hcard⟩ := hex
    obtain ⟨Q,hQ,hbQ⟩ := sew_routes RA RB hd P hP
    exact ⟨Q.pieces,Q.cycles,⟨Q.disjoint,hQ.trans hcover⟩,by omega⟩
  have strongA {i : Fin 3} (RA : Route G A t i) (hstrong : RA.paths.Strong)
      (hbA : RA.rest.pieces.card+1 ≤ kA) :
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
        IsDecomposition G D ∧ D.card ≤ kA+kB+4 := by
    rcases hB i with ⟨RB,hbB⟩ | ⟨j,RB,hstrongB,hbB⟩
    · exact finish RA RB (Or.inl rfl) (by omega)
    · exact finish RA RB (Or.inr ⟨hstrong,hstrongB⟩) (by omega)
  rcases hA 0 with ⟨RA,hbA⟩ | ⟨i,RA,hstrong,hbA⟩
  · rcases hB 0 with ⟨RB,hbB⟩ | ⟨j,RB,hstrongB,hbB⟩
    · exact finish RA RB (Or.inl rfl) (by omega)
    · rcases hA j with ⟨RA',hbA'⟩ | ⟨i,RA',hstrongA',hbA'⟩
      · exact finish RA' RB (Or.inl rfl) (by omega)
      · exact strongA RA' hstrongA' hbA'
  · exact strongA RA hstrong hbA

end Erdos184.TerminalRouting
