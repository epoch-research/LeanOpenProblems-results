import Submission.CriticalNestedCycles
import Submission.ShortestCycle

/-!
Greedy vertex-disjoint cycle extraction in graphs with no triangles or
four-cycles. The resulting count-dependent critical-degree bound is not a
uniform degree bound and does not settle Erdős 184.
-/
open SimpleGraph
open scoped Classical
namespace Erdos184.HighGirthCritical
open CountCritical CycleNumberSubmodularity FractionalEnvelope
variable {V : Type*} [Fintype V]
set_option maxHeartbeats 1000000

def avoid (G : SimpleGraph V) (S : Set V) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ u ∉ S ∧ v ∉ S
  symm := by intro u v h; exact ⟨h.1.symm,h.2.2,h.2.1⟩
  loopless := by intro u h; exact h.1.ne rfl

omit [Fintype V] in
lemma avoid_le (G : SimpleGraph V) (S : Set V) : avoid G S ≤ G := fun _ _ h => h.1

omit [Fintype V] in
lemma avoid_support_subset (G : SimpleGraph V) (S : Set V) :
    (avoid G S).support ⊆ G.support \ S := by
  rintro v ⟨w,hw⟩
  exact ⟨⟨w,hw.1⟩,hw.2.1⟩

lemma degree_avoid_add_lost (G : SimpleGraph V) (S : Set V) {v : V} (hv : v ∉ S) :
    (avoid G S).degree v + (G.neighborSet v ∩ S).ncard = G.degree v := by
  have hn : (avoid G S).neighborSet v = G.neighborSet v \ S := by
    ext w
    simp [mem_neighborSet,avoid,hv]
  simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card,Nat.card_coe_set_eq]
  rw [hn]
  have hh := Set.ncard_inter_add_ncard_diff_eq_ncard (G.neighborSet v) S
  omega

lemma outside_degree_loss_le_one (G : SimpleGraph V) {a : V}
    (p : G.Walk a a) (hp : p.IsCycle) (hg : G.girth = p.length)
    (hlen : 5 ≤ p.length) {v : V} (hv : v ∉ p.toSubgraph.verts) :
    G.degree v ≤ (avoid G p.toSubgraph.verts).degree v + 1 := by
  have hsmall : (G.neighborSet v ∩ p.toSubgraph.verts).Subsingleton := by
    intro x hx y hy
    by_contra hxy
    have hh := ShortestCycle.common_neighbor_mem_support p hp hg hlen
      (p.mem_verts_toSubgraph.mp hx.2) (p.mem_verts_toSubgraph.mp hy.2) hxy
      hx.1.symm hy.1.symm
    exact hv (p.mem_verts_toSubgraph.mpr hh)
  have hc := Set.ncard_le_one_iff_subsingleton.mpr hsmall
  have he := degree_avoid_add_lost G p.toSubgraph.verts hv
  omega

lemma exists_shortest_cycle (G : SimpleGraph V) (hne : G ≠ ⊥)
    (hmin : ∀ v ∈ G.support, 2 ≤ G.degree v) :
    ∃ a, ∃ p : G.Walk a a, p.IsCycle ∧ G.girth = p.length := by
  apply SimpleGraph.exists_girth_eq_length.mpr
  intro ha
  obtain ⟨v,hv⟩ := DegreeTightOptimal.exists_nonisolated_degree_one_of_acyclic G ha hne
  have hs : v ∈ G.support := (G.degree_pos_iff_mem_support v).mp (by omega)
  have hh := hmin v hs
  omega

/-- If the supported minimum degree is at least three, removing a shortest
cycle of length at least five leaves a nonempty graph and loses at most one
from the supported minimum degree. -/
lemma shortest_step (d : ℕ) (G : SimpleGraph V) (hne : G ≠ ⊥)
    (hmin : ∀ v ∈ G.support, d+3 ≤ G.degree v)
    (hshort : ∀ a (p : G.Walk a a), p.IsCycle → 5 ≤ p.length) :
    ∃ a, ∃ p : G.Walk a a, p.IsCycle ∧ G.girth = p.length ∧
      avoid G p.toSubgraph.verts ≠ ⊥ ∧
      (∀ v ∈ (avoid G p.toSubgraph.verts).support,
        d+2 ≤ (avoid G p.toSubgraph.verts).degree v) := by
  obtain ⟨a,p,hp,hg⟩ := exists_shortest_cycle G hne (by intro v hv; have := hmin v hv; omega)
  have hlen := hshort a p hp
  have hc := cycle_subgraph_regular G hp
  have hind := ShortestCycle.isInduced p hp hg
  have ha : a ∈ p.toSubgraph.verts := p.mem_verts_toSubgraph.mpr p.start_mem_support
  have haG : a ∈ G.support := by
    have hdeg := CriticalNestedCycles.cycle_degree p.toSubgraph hc a
    rw [if_pos ha] at hdeg
    have hle := SimpleGraph.degree_le_of_le (v := a) p.toSubgraph.spanningCoe_le
    apply (G.degree_pos_iff_mem_support a).mp
    simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hdeg hle ⊢
    omega
  have hex : ∃ w, G.Adj a w ∧ w ∉ p.toSubgraph.verts := by
    by_contra! hn
    have hsub : G.neighborSet a ⊆ p.toSubgraph.neighborSet a := by
      intro w hw
      exact hind ha (hn w hw) hw
    have hb := Set.ncard_le_ncard hsub
    have hc2 := hp.ncard_neighborSet_toSubgraph_eq_two p.start_mem_support
    have hm := hmin a haG
    simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card,Nat.card_coe_set_eq] at hm
    omega
  obtain ⟨w,hw,hwout⟩ := hex
  have hwmin := hmin w (show w ∈ G.support from ⟨a,hw.symm⟩)
  have hwloss := outside_degree_loss_le_one G p hp hg hlen hwout
  have hAne : avoid G p.toSubgraph.verts ≠ ⊥ := by
    intro hb
    have hz : (avoid G p.toSubgraph.verts).degree w = 0 := by
      simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      rw [hb]
      simp
    omega
  refine ⟨a,p,hp,hg,hAne,?_⟩
  intro v hv
  have hv' := avoid_support_subset G p.toSubgraph.verts hv
  have hm := hmin v hv'.1
  have hl := outside_degree_loss_le_one G p hp hg hlen hv'.2
  omega

/-- A graph with supported minimum degree d+2 and girth at least five
contains an even restriction of maximum degree two and exact fractional
cycle count d+1. Equivalently it contains d+1 vertex-disjoint cycles. -/
lemma exists_cycle_union (d : ℕ) (G : SimpleGraph V) (hne : G ≠ ⊥)
    (hmin : ∀ v ∈ G.support, d+2 ≤ G.degree v)
    (hshort : ∀ a (p : G.Walk a a), p.IsCycle → 5 ≤ p.length) :
    ∃ H : SimpleGraph V, H ≤ G ∧ (∀ v, Even (H.degree v)) ∧
      (∀ v, H.degree v ≤ 2) ∧ optimum H = (d+1 : ℕ) := by
  induction d generalizing G with
  | zero =>
    obtain ⟨a,p,hp,_⟩ := exists_shortest_cycle G hne (by simpa using hmin)
    have hc := cycle_subgraph_regular G hp
    refine ⟨p.toSubgraph.spanningCoe,p.toSubgraph.spanningCoe_le,?_,?_,?_⟩
    · intro v
      have hd := CriticalNestedCycles.cycle_degree p.toSubgraph hc v
      simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hd ⊢
      rw [hd]
      split_ifs <;> decide
    · intro v
      have hd := CriticalNestedCycles.cycle_degree p.toSubgraph hc v
      simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hd ⊢
      rw [hd]
      split_ifs <;> omega
    · simpa using CycleFactors.optimum_cycle (G := G) (⟨p.toSubgraph,hc⟩ : FractionalCycles.CyclePiece G)
  | succ d ih =>
    obtain ⟨a,p,hp,hg,hAne,hAmin⟩ := shortest_step d G hne (by simpa [Nat.add_assoc] using hmin) hshort
    let A := avoid G p.toSubgraph.verts
    have hAl : A ≤ G := avoid_le G p.toSubgraph.verts
    have hAsh : ∀ a (q : A.Walk a a), q.IsCycle → 5 ≤ q.length := by
      intro a q hq
      have hh := hshort a (q.mapLe hAl) (hq.mapLe hAl)
      simpa using hh
    obtain ⟨H,hHA,heH,hdH,hval⟩ := ih A hAne (by
      intro v hv
      simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hAmin v hv) hAsh
    let C := p.toSubgraph.spanningCoe
    have hc := cycle_subgraph_regular G hp
    have hCdegree (v : V) : C.degree v = if v ∈ p.toSubgraph.verts then 2 else 0 := by
      simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
        using CriticalNestedCycles.cycle_degree p.toSubgraph hc v
    have heC : ∀ v, Even (C.degree v) := by
      intro v
      rw [hCdegree]
      split_ifs <;> decide
    have hsupport : Disjoint C.support H.support := by
      apply Set.disjoint_left.mpr
      rintro v ⟨w,hw⟩ hv
      have hvC := p.toSubgraph.edge_vert hw
      have hvA := SimpleGraph.support_mono hHA hv
      exact (avoid_support_subset G p.toSubgraph.verts hvA).2 hvC
    have hover : (C.support ∩ H.support).ncard ≤ 1 := by
      rw [Set.disjoint_iff_inter_eq_empty.mp hsupport]
      simp
    have hedge := FractionalSeparated.disjoint_of_support_inter_le_one hover
    have heU : ∀ v, Even ((C ⊔ H).degree v) := by
      intro v
      simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
        using FractionalSeparated.even_sup hedge heC (by
          intro w
          simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using heH w) v
    refine ⟨C ⊔ H,sup_le p.toSubgraph.spanningCoe_le (hHA.trans hAl),?_,?_,?_⟩
    · intro v
      simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using heU v
    · intro v
      have hh := degree_sup_of_edge_disjoint C H hedge v
      have hc2 : C.degree v ≤ 2 := by rw [hCdegree]; split_ifs <;> omega
      have hh2 := hdH v
      by_cases hv : v ∈ C.support
      · have hn : v ∉ H.support := fun h => Set.disjoint_left.mp hsupport hv h
        have hz := (H.degree_eq_zero_iff_notMem_support v).mpr hn
        simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hh hc2 hz ⊢
        omega
      · have hz := (C.degree_eq_zero_iff_notMem_support v).mpr hv
        simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hh hh2 hz ⊢
        omega
    · have heq := FractionalSeparated.optimum_add (G := C ⊔ H)
        (by rw [edgeSet_sup]) hover heC (by
          intro v
          simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using heH v)
      have hvC : optimum C = 1 := CycleFactors.optimum_cycle (G := G)
        (⟨p.toSubgraph,hc⟩ : FractionalCycles.CyclePiece G)
      rw [heq,hvC,hval]
      push_cast
      ring

/-- This bound depends on the critical count, not on a universal constant.
The restriction k ≥ 2 is necessary, since a single cycle is count-one
critical and every one of its supported degrees is two. -/
lemma exists_positive_degree_le_count_high_girth {G : SimpleGraph V} {k : ℕ}
    (hG : IsCountCritical k G) (hk : 2 ≤ k) (hne : G ≠ ⊥)
    (hshort : ∀ a (p : G.Walk a a), p.IsCycle → 5 ≤ p.length) :
    ∃ v ∈ G.support, G.degree v ≤ k := by
  by_contra! hn
  obtain ⟨H,hHG,heH,hdH,hval⟩ := exists_cycle_union (k-1) G hne (by
    intro v hv
    have hh := hn v hv
    omega) hshort
  have hproper : H ≠ G := by
    intro heq
    obtain ⟨v,w,hvw⟩ := SimpleGraph.ne_bot_iff_exists_adj.mp hne
    have hb := hdH v
    have hh := hn v ⟨w,hvw⟩
    simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hb hh
    rw [heq] at hb
    omega
  have hlow := hG.2.2 H hHG hproper (by
    intro v
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using heH v)
  have hupper := optimum_le_number H (by
    intro v
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using heH v)
  rw [hval] at hupper
  have hbig : k-1+1 ≤ cycleNumber H := by exact_mod_cast hupper
  omega

/-- Consequently, a degree-two-free critical graph at count at most three
must contain a triangle or a four-cycle. -/
lemma degree_two_of_count_le_three_high_girth {G : SimpleGraph V} {k : ℕ}
    (hG : IsCountCritical k G) (hk : k ≤ 3) (hne : G ≠ ⊥)
    (hshort : ∀ a (p : G.Walk a a), p.IsCycle → 5 ≤ p.length) :
    ∃ v, G.degree v = 2 := by
  by_contra hno
  have hno' : ∀ v, G.degree v ≠ 2 := by simpa using hno
  have hfour := LowCountCritical.supported_degree_eq_four_of_count_le_three hG hk hne hno'
  obtain ⟨H,hHG,heH,hdH,hval⟩ := exists_cycle_union 2 G hne (by
    intro v hv
    rw [hfour v hv]) hshort
  have hproper : H ≠ G := by
    intro heq
    obtain ⟨v,w,hvw⟩ := SimpleGraph.ne_bot_iff_exists_adj.mp hne
    have hb := hdH v
    rw [heq,hfour v ⟨w,hvw⟩] at hb
    omega
  have hlow := hG.2.2 H hHG hproper (by
    intro v
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using heH v)
  have hupper := optimum_le_number H (by
    intro v
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using heH v)
  rw [hval] at hupper
  have h3 : 3 ≤ cycleNumber H := by exact_mod_cast hupper
  omega

end Erdos184.HighGirthCritical
