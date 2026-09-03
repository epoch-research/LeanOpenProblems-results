import Submission.GatewayFamily

/-! Bounded monotone separable degree potentials do not uniformly pay for
long-cycle density-halving phases. This is not a disproof of Erdős 184. -/
open SimpleGraph
open scoped Classical
namespace Erdos184.GatewayFamily

def coreParam (d : ℕ) := 3 * d^2 + 13 * d + 13

lemma coreParam_odd {d : ℕ} (hd : Odd d) : Odd (coreParam d) := by
  obtain ⟨t, rfl⟩ := hd
  refine ⟨6*t^2 + 19*t + 14, ?_⟩
  simp only [coreParam]
  ring

variable {d : ℕ}
local notation "G" => (graph (r := coreParam d) (d := d))

lemma family_size : (G).edgeFinset.card = 2 * (coreParam d + 2) * (d + 2)^2 := by
  have hh := twice_graph_size (r := coreParam d) (d := d)
  simp only [coreParam] at hh ⊢
  nlinarith

lemma family_halving_count_lower (hd : Odd d) (D : Finset (G).Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hdis : Set.PairwiseDisjoint (D : Set (G).Subgraph) (fun H => H.edgeSet))
    (hlong : ∀ H ∈ D, d + 2 < H.edgeSet.ncard)
    (hhalf : ((G) \ unionPieces (G) D).edgeFinset.card ≤ (coreParam d + 2) * (d + 2)^2) :
    (d + 1)^2 + 1 ≤ D.card := by
  have hpack := packing_edge_upper (coreParam_odd hd) hd D hc hdis hlong
  have hpart := cycle_packing_edge_card_partition (G) D hdis
  have hsum := unionPieces_edge_card (G) D hdis
  have hsize := family_size (d := d)
  simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hpack hpart hsum hsize hhalf
  rw [← hsum] at hpart
  have hh : (coreParam d + 2) * ((d + 1)^2 + 1) ≤ (coreParam d + 2) * D.card := by
    nlinarith
  exact Nat.le_of_mul_le_mul_left hh (by omega)

lemma family_core_bound (hd : 3 ≤ d) : coreParam d + 2 ≤ 6 * ((d + 1)^2 + 1) := by
  simp only [coreParam]
  nlinarith

lemma family_phase_exists (_hd : Odd d) :
    ∃ D : Finset (G).Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2 ∧ d + 3 < H.edgeSet.ncard) ∧
      Set.PairwiseDisjoint (D : Set (G).Subgraph) (fun H => H.edgeSet) ∧
      ((G) \ unionPieces (G) D).edgeFinset.card ≤ (coreParam d + 2) * (d + 2)^2 := by
  obtain ⟨D, hc, hdis, hmax⟩ := exists_maximal_long_cycle_packing (G) (d + 3)
  refine ⟨D, ?_, hdis, ?_⟩
  · intro H hH
    refine ⟨(hc H hH).1, ?_, (hc H hH).2.2⟩
    intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using (hc H hH).2.1 v
  · have hh := edge_card_le_of_cycle_length_bound ((G) \ unionPieces (G) D) (d + 3)
      (by omega) hmax
    rw [graph_order] at hh
    simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hh ⊢
    have heq : d + 3 - 1 = d + 2 := by omega
    rw [heq] at hh
    convert hh using 1
    ring

/-- Every fixed bounded monotone degree weight has arbitrarily large members
of this graph family on which no admissible phase can pay for itself. -/
lemma exists_family_potential_failure (φ : ℕ → ℝ) (hm : Monotone φ)
    (hb : BddAbove (Set.range φ)) (C : ℝ) (hC : 0 < C) (N : ℕ) :
    ∃ d ≥ N, 3 ≤ d ∧ Odd d ∧
      ∀ D : Finset (graph (r := coreParam d) (d := d)).Subgraph,
        (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) →
        Set.PairwiseDisjoint (D : Set (graph (r := coreParam d) (d := d)).Subgraph)
          (fun H => H.edgeSet) →
        (∀ H ∈ D, d + 2 < H.edgeSet.ncard) →
        ((graph (r := coreParam d) (d := d)) \
          unionPieces (graph (r := coreParam d) (d := d)) D).edgeFinset.card ≤
          (coreParam d + 2) * (d + 2)^2 →
        C * (∑ v : V (coreParam d) d,
          (φ ((graph (r := coreParam d) (d := d)).degree v) -
            φ (((graph (r := coreParam d) (d := d)) \
              unionPieces (graph (r := coreParam d) (d := d)) D).degree v))) < D.card := by
  obtain ⟨δ, hδN, heδ, hδ2, hsmall⟩ :=
    DegreePotential.exists_even_small_tail_and_increment hm hb
      (by positivity : 0 < 1 / (6 * C)) (max (N + 1) 4)
  let d := δ - 1
  have hd3 : 3 ≤ d := by omega
  have hdeq : d + 1 = δ := by omega
  have hdsub : d - 1 = δ - 2 := by omega
  have hd : Odd d := by
    obtain ⟨a, ha⟩ := heδ
    exact ⟨a - 1, by omega⟩
  refine ⟨d, by omega, hd3, hd, ?_⟩
  intro D hc hdis hlong hhalf
  have hdrop := potential_drop_upper (coreParam_odd hd) hd D hc hdis hlong φ hm hb
  have hcount := family_halving_count_lower hd D hc hdis hlong hhalf
  have hcore := family_core_bound hd3
  have hsmall' : (⨆ i, φ i) - φ (d - 1) +
      (d + 1 : ℕ) * (φ (d + 1) - φ (d - 1)) < 1 / (6 * C) := by
    simpa only [hdeq, hdsub] using hsmall
  have hC6 : (6 * C) * (1 / (6 * C)) = 1 := by field_simp
  have hbound : C * ((⨆ i, φ i) - φ (d - 1) +
      (d + 1 : ℕ) * (φ (d + 1) - φ (d - 1))) < 1 / 6 := by
    nlinarith [mul_lt_mul_of_pos_left hsmall' (by positivity : 0 < 6 * C)]
  have hcore' : (coreParam d + 2 : ℕ) ≤ 6 * (D.card : ℝ) := by
    exact_mod_cast hcore.trans (Nat.mul_le_mul_left 6 hcount)
  have hdrop' := mul_le_mul_of_nonneg_left hdrop hC.le
  have hstrict := mul_lt_mul_of_pos_left hbound
    (by positivity : 0 < ((coreParam d + 2 : ℕ) : ℝ))
  nlinarith

end Erdos184.GatewayFamily

namespace Erdos184

/-- An edge-disjoint long-cycle packing removing at least half the edges. -/
def IsLongHalvingPhase {V : Type*} [Fintype V] (G : SimpleGraph V)
    (k : ℕ) (D : Finset G.Subgraph) : Prop :=
  (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2 ∧ k < H.edgeSet.ncard) ∧
  Set.PairwiseDisjoint (D : Set G.Subgraph) (fun H => H.edgeSet) ∧
  2 * (G \ unionPieces G D).edgeFinset.card ≤ G.edgeFinset.card

set_option maxHeartbeats 1000000 in
/-- This density-phase charging principle is false, even allowing the
packing to be chosen optimally for each graph. -/
theorem no_uniform_bounded_degree_potential :
    ¬ ∃ φ : ℕ → ℝ, Monotone φ ∧ BddAbove (Set.range φ) ∧
      ∃ C : ℝ, 0 < C ∧
        ∀ {V : Type} [Fintype V] (G : SimpleGraph V),
          (∀ v, Even (G.degree v)) →
          ∀ k : ℕ, 2 ≤ k → G.edgeFinset.card = 2 * (k - 1) * Fintype.card V →
          ∃ D : Finset G.Subgraph, IsLongHalvingPhase G k D ∧
            (D.card : ℝ) ≤ C * (∑ v : V,
              (φ (G.degree v) - φ ((G \ unionPieces G D).degree v))) := by
  rintro ⟨φ, hm, hb, C, hC, hcharge⟩
  obtain ⟨d, _, hd3, hd, hfail⟩ :=
    GatewayFamily.exists_family_potential_failure φ hm hb C hC 0
  let G := GatewayFamily.graph (r := GatewayFamily.coreParam d) (d := d)
  have he : ∀ v, Even (G.degree v) := by
    intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using GatewayFamily.graph_even (GatewayFamily.coreParam_odd hd) hd v
  have hsize : G.edgeFinset.card =
      2 * (d + 3 - 1) * Fintype.card (GatewayFamily.V (GatewayFamily.coreParam d) d) := by
    have hh := GatewayFamily.family_size (d := d)
    simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hh ⊢
    change Nat.card G.edgeSet = _ at hh
    rw [hh, Nat.card_eq_fintype_card, GatewayFamily.graph_order]
    have hh' : d + 3 - 1 = d + 2 := by omega
    rw [hh']
    ring
  obtain ⟨D, hphase, hcost⟩ := hcharge G (by
    intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using he v) (d + 3) (by omega) (by
      simpa only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] using hsize)
  obtain ⟨hc, hdis, hhalf⟩ := hphase
  have hc' : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2 := by
    intro H hH
    refine ⟨(hc H hH).1, ?_⟩
    intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using (hc H hH).2.1 v
  have hhalf' : (G \ unionPieces G D).edgeFinset.card ≤
      (GatewayFamily.coreParam d + 2) * (d + 2)^2 := by
    have hs := GatewayFamily.family_size (d := d)
    simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hs hhalf ⊢
    change 2 * Nat.card (G \ unionPieces G D).edgeSet ≤ Nat.card G.edgeSet at hhalf
    change Nat.card G.edgeSet = _ at hs
    nlinarith
  have hcontra := hfail D (by
    intro H hH
    refine ⟨(hc' H hH).1, ?_⟩
    intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using (hc' H hH).2 v) hdis
    (fun H hH => by have := (hc H hH).2.2; omega) (by
      simpa only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] using hhalf')
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hcontra hcost
  exact (not_lt_of_ge hcost) hcontra

end Erdos184
