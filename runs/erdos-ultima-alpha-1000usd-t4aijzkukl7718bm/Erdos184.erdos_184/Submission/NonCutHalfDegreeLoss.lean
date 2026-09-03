import Submission.HighlyConnectedSingletonLeaf

/-! A non-cut vertex costs at most half its degree, rounded up, in the
arbitrary-subgraph hull recurrence. This is degree-dependent, not a uniform
constant, and does not establish the conjecture in Spec.lean. -/
open Filter SimpleGraph
open scoped Classical
namespace Erdos184Work.NonCutHalfDegreeLoss
open Critical EdgeHull VertexSeparators
set_option maxHeartbeats 1200000
universe u
variable {V : Type*} [Fintype V]

private noncomputable def stableNumber {W : Type*} [Finite W]
    (H : SimpleGraph W) : ℕ := @number W (Fintype.ofFinite W) H

private lemma number_stable {W : Type*} [Fintype W] (H : SimpleGraph W) :
    number H = stableNumber H :=
  congrArg (fun i : Fintype W => @number W i H) (Subsingleton.elim _ _)

private noncomputable def stableValue {W : Type*} [Finite W]
    (H : SimpleGraph W) : ℕ := @value W (Fintype.ofFinite W) H

private lemma value_stable {W : Type*} [Fintype W] (H : SimpleGraph W) :
    value H = stableValue H :=
  congrArg (fun i : Fintype W => @value W i H) (Subsingleton.elim _ _)

lemma even_degree_bound (G : SimpleGraph V) (v : V)
    (hc : (G.induce ({v}ᶜ : Set V)).Preconnected) (he : Even (G.degree v)) :
    number G ≤ value (G.induce ({v}ᶜ : Set V)) + G.degree v / 2 := by
  have hc' : (G.induce {w : V | w ≠ v}).Preconnected := hc
  obtain ⟨L,D,hLG,hD,hdec,hstar,hcard⟩ := Vertex.exists_vertex_cycle_cover G v hc' he
  have hLnum : number L ≤ D.card := by
    apply number_le D _ hdec
    intro H hH
    apply Or.inl
    simpa only [SimpleGraph.IsRegularOfDegree,
      ← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using hD H hH
  have hs : (G \ L).support ⊆ ({v}ᶜ : Set V) := by
    rintro x ⟨y,hxy⟩ hx
    have hxv : x = v := hx
    subst x
    exact hxy.2 ((hstar y).mpr hxy.1)
  have hn := number_induce_support (G \ L) ({v}ᶜ : Set V) hs
  have hi : (G \ L).induce ({v}ᶜ : Set V) ≤ G.induce ({v}ᶜ : Set V) := by
    intro x y hxy
    exact hxy.1
  have hh := le_value hi
  have hb := number_sdiff_add_le G L hLG
  simp only [number_stable, value_stable,
    ← SimpleGraph.card_neighborSet_eq_degree,
    ← Nat.card_eq_fintype_card] at hn hh hb hLnum hcard ⊢
  omega

omit [Fintype V] in
lemma delete_incident_induce (G : SimpleGraph V) (v w : V) :
    (G.deleteEdges {s(v,w)}).induce ({v}ᶜ : Set V) =
      G.induce ({v}ᶜ : Set V) := by
  ext x y
  change (G.deleteEdges {s(v,w)}).Adj x.val y.val ↔ G.Adj x.val y.val
  rw [SimpleGraph.deleteEdges_adj]
  constructor
  · exact And.left
  · intro hxy
    refine ⟨hxy,?_⟩
    intro he
    rcases Sym2.eq_iff.mp (Set.mem_singleton_iff.mp he) with h | h
    · exact x.property h.1
    · exact y.property h.2

/-- An even set of incident edges can be covered by pairwise edge-disjoint
cycles through v; at odd degree one extra singleton suffices. -/
lemma half_degree_bound (G : SimpleGraph V) (v : V)
    (hc : (G.induce ({v}ᶜ : Set V)).Preconnected) :
    number G ≤ value (G.induce ({v}ᶜ : Set V)) + (G.degree v + 1) / 2 := by
  by_cases he : Even (G.degree v)
  · have hb := even_degree_bound G v hc he
    omega
  · have ho := Nat.odd_iff.mp (Nat.not_even_iff_odd.mp he)
    have hp : 0 < G.degree v := by omega
    obtain ⟨w,hw⟩ := (G.degree_pos_iff_exists_adj v).mp hp
    let K := G.deleteEdges {s(v,w)}
    have hI : K.induce ({v}ᶜ : Set V) = G.induce ({v}ᶜ : Set V) :=
      delete_incident_induce G v w
    have hcK : (K.induce ({v}ᶜ : Set V)).Preconnected := hI.symm ▸ hc
    have hd : K.degree v + 1 = G.degree v := Compression.delete_edge_degree_left hw
    have heK : Even (Nat.card (K.neighborSet v)) := by
      simp only [← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] at hd ho
      rw [Nat.even_iff]
      omega
    have hb := even_degree_bound K v hcK (by
      simpa only [← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] using heK)
    rw [hI] at hb
    have hu := number_restore_edge G ⟨s(v,w),hw⟩
    change number G ≤ number K + 1 at hu
    simp only [number_stable, value_stable,
      ← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] at hb hu hd ⊢
    omega

lemma loss_two_of_degree_le_four (G : SimpleGraph V) (v : V)
    (hc : (G.induce ({v}ᶜ : Set V)).Preconnected) (hd : G.degree v ≤ 4) :
    number G ≤ value (G.induce ({v}ᶜ : Set V)) + 2 := by
  have h := half_degree_bound G v hc
  omega

lemma degree_large_of_loss (G : SimpleGraph V) (v : V) (C : ℕ)
    (hc : (G.induce ({v}ᶜ : Set V)).Preconnected)
    (hl : value (G.induce ({v}ᶜ : Set V)) + C < number G) :
    2 * C < G.degree v := by
  have h := half_degree_bound G v hc
  omega

/-- This strengthens the earlier necessary degree bound by a factor of two.
It is conditional on failure of the original conjecture. -/
lemma high_minimum_degree_obstruction
    (hbad : ¬ (∃ f : ℕ → ℝ,
      (f =O[atTop] fun n : ℕ => (n : ℝ)) ∧
      ∀ {W : Type u} [Fintype W] [DecidableEq W] (G : SimpleGraph W),
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
        (D.card : ℝ) ≤ f (Fintype.card W))) (k C : ℕ) (hk : 1 ≤ k) :
    ∃ (W : Type u) (_ : Fintype W) (G : SimpleGraph W),
      Minimal G ∧ DeletionConnected G k ∧ 2*k+1 < Fintype.card W ∧
        (∀ v : W, 2*C < G.degree v) ∧
        (∀ v : W, value (G.induce ({v}ᶜ : Set W)) + C < number G) := by
  obtain ⟨W,iW,G,hm,hc,hn,hv⟩ :=
    HighlyConnectedVertexLoss.obstruction_of_asymptotic_failure hbad k C
  letI := iW
  refine ⟨W,iW,G,hm,hc,hn,?_,hv⟩
  intro v
  exact degree_large_of_loss G v C (hc {v} (by simpa using hk)) (hv v)

end Erdos184Work.NonCutHalfDegreeLoss
#print axioms Erdos184Work.NonCutHalfDegreeLoss.even_degree_bound
#print axioms Erdos184Work.NonCutHalfDegreeLoss.half_degree_bound
#print axioms Erdos184Work.NonCutHalfDegreeLoss.degree_large_of_loss

#print axioms Erdos184Work.NonCutHalfDegreeLoss.high_minimum_degree_obstruction
