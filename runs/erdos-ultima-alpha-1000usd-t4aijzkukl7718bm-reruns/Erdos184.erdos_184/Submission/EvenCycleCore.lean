import Submission.CriticalOutsideCycles

/-!
The union of all even restrictions is the cyclic core. Symmetric-difference
averaging bounds its degree when the cycle envelope is at most one. These
lemmas do not give a uniform bound for arbitrary count-critical graphs.
-/
open SimpleGraph
open scoped Classical BigOperators symmDiff
namespace Erdos184.EvenCycleCore
open CycleEnvelope CountCritical CycleNumberSubmodularity
variable {V : Type*} [Fintype V]
set_option maxHeartbeats 1000000

lemma degree_xor (A B : SimpleGraph V) (v : V) :
    (A ∆ B).degree v + 2 * (A.neighborFinset v ∩ B.neighborFinset v).card =
      A.degree v + B.degree v := by
  have hN : (A ∆ B).neighborFinset v =
      (A.neighborFinset v \ B.neighborFinset v) ∪
        (B.neighborFinset v \ A.neighborFinset v) := by
    ext w
    simp only [mem_neighborFinset,Finset.mem_union,Finset.mem_sdiff,
      symmDiff_def,sup_adj,sdiff_adj]
  have hdis : Disjoint (A.neighborFinset v \ B.neighborFinset v)
      (B.neighborFinset v \ A.neighborFinset v) := by
    apply Finset.disjoint_left.mpr
    intro w ha hb
    exact (Finset.mem_sdiff.mp ha).2 (Finset.mem_sdiff.mp hb).1
  have hA := Finset.card_sdiff_add_card_inter (A.neighborFinset v) (B.neighborFinset v)
  have hB := Finset.card_sdiff_add_card_inter (B.neighborFinset v) (A.neighborFinset v)
  rw [Finset.inter_comm] at hB
  have hC := congrArg Finset.card hN
  rw [Finset.card_union_of_disjoint hdis] at hC
  simp only [card_neighborFinset_eq_degree] at hA hB hC
  omega

lemma even_xor {A B : SimpleGraph V}
    (hA : ∀ v, Even (A.degree v)) (hB : ∀ v, Even (B.degree v)) :
    ∀ v, Even ((A ∆ B).degree v) := by
  intro v
  have hh := degree_xor A B v
  obtain ⟨a,ha⟩ := hA v
  obtain ⟨b,hb⟩ := hB v
  refine ⟨a+b-(A.neighborFinset v ∩ B.neighborFinset v).card,?_⟩
  simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hh ha hb ⊢
  omega

lemma xor_mem {G A B : SimpleGraph V} (hA : A ∈ evenSubgraphs G)
    (hB : B ∈ evenSubgraphs G) : A ∆ B ∈ evenSubgraphs G := by
  obtain ⟨hAG,heA⟩ := mem_evenSubgraphs.mp hA
  obtain ⟨hBG,heB⟩ := mem_evenSubgraphs.mp hB
  apply mem_evenSubgraphs.mpr
  refine ⟨(symmDiff_le_sup).trans (sup_le hAG hBG),?_⟩
  intro v
  simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using even_xor heA heB v

/-- The edges that occur in at least one even restriction. Below this is
identified with the union of the edges of the genuine cycle pieces. -/
def core (G : SimpleGraph V) : SimpleGraph V where
  Adj v w := ∃ H ∈ evenSubgraphs G, H.Adj v w
  symm := by rintro v w ⟨H,hH,ha⟩; exact ⟨H,hH,ha.symm⟩
  loopless := by rintro v ⟨H,hH,ha⟩; exact ha.ne rfl

lemma core_le (G : SimpleGraph V) : core G ≤ G := by
  rintro v w ⟨H,hH,ha⟩
  exact (mem_evenSubgraphs.mp hH).1 ha

lemma even_le_core {G H : SimpleGraph V} (hH : H ∈ evenSubgraphs G) : H ≤ core G :=
  fun _ _ h => ⟨H,hH,h⟩

lemma bot_mem (G : SimpleGraph V) : (⊥ : SimpleGraph V) ∈ evenSubgraphs G := by
  apply mem_evenSubgraphs.mpr
  refine ⟨bot_le,?_⟩
  intro v
  simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
  simp

/-- Toggling an even restriction containing an edge pairs the even
restrictions that contain that edge with those that omit it. -/
lemma half_incidence {G : SimpleGraph V} {v w : V} (h : (core G).Adj v w) :
    2 * ((evenSubgraphs G).filter (fun H => H.Adj v w)).card =
      (evenSubgraphs G).card := by
  obtain ⟨A,hA,ha⟩ := h
  have heq : ((evenSubgraphs G).filter (fun H => H.Adj v w)).card =
      ((evenSubgraphs G).filter (fun H => ¬ H.Adj v w)).card := by
    apply Finset.card_bij (fun H _ => H ∆ A)
    · intro H hH
      obtain ⟨hHG,hadj⟩ := Finset.mem_filter.mp hH
      apply Finset.mem_filter.mpr
      exact ⟨xor_mem hHG hA,by simp [symmDiff_def,ha,hadj]⟩
    · intro H hH K hK heq
      have hh := congrArg (fun J : SimpleGraph V => J ∆ A) heq
      simpa only [symmDiff_symmDiff_cancel_right] using hh
    · intro H hH
      obtain ⟨hHG,hadj⟩ := Finset.mem_filter.mp hH
      refine ⟨H ∆ A,Finset.mem_filter.mpr ⟨xor_mem hHG hA,?_⟩,?_⟩
      · simp [symmDiff_def,ha,hadj]
      · exact symmDiff_symmDiff_cancel_right A H
  have hh := Finset.card_filter_add_card_filter_not (s := evenSubgraphs G)
    (fun H => H.Adj v w)
  omega

lemma degree_sum (G : SimpleGraph V) (v : V) :
    (evenSubgraphs G).card * (core G).degree v =
      2 * ∑ H ∈ evenSubgraphs G, H.degree v := by
  have hinner (H : SimpleGraph V) (hH : H ∈ evenSubgraphs G) :
      (∑ w ∈ (core G).neighborFinset v, if H.Adj v w then (1 : ℕ) else 0) =
        H.degree v := by
    rw [Finset.sum_boole]
    have heq : ((core G).neighborFinset v).filter (fun w => H.Adj v w) =
        H.neighborFinset v := by
      ext w
      simp only [Finset.mem_filter,mem_neighborFinset]
      exact ⟨And.right,fun hw => ⟨⟨H,hH,hw⟩,hw⟩⟩
    rw [heq,card_neighborFinset_eq_degree]
    simp only [Nat.cast_id]
  calc
    (evenSubgraphs G).card * (core G).degree v =
        ∑ w ∈ (core G).neighborFinset v, (evenSubgraphs G).card := by
          simp [Nat.mul_comm]
    _ = ∑ w ∈ (core G).neighborFinset v,
        2 * ((evenSubgraphs G).filter (fun H => H.Adj v w)).card := by
          apply Finset.sum_congr rfl
          intro w hw
          exact (half_incidence ((mem_neighborFinset _ _ _).mp hw)).symm
    _ = 2 * ∑ w ∈ (core G).neighborFinset v,
        ∑ H ∈ evenSubgraphs G, if H.Adj v w then (1 : ℕ) else 0 := by
          simp only [Finset.sum_boole,Finset.mul_sum,Nat.cast_id]
    _ = 2 * ∑ H ∈ evenSubgraphs G,
        ∑ w ∈ (core G).neighborFinset v, if H.Adj v w then (1 : ℕ) else 0 := by
          rw [Finset.sum_comm]
    _ = 2 * ∑ H ∈ evenSubgraphs G, H.degree v := by
          congr 1
          exact Finset.sum_congr rfl hinner

lemma even_degree_le_twice_envelope {G H : SimpleGraph V}
    (hH : H ∈ evenSubgraphs G) (v : V) : H.degree v ≤ 2 * envelope G := by
  obtain ⟨hle,he⟩ := mem_evenSubgraphs.mp hH
  obtain ⟨D,hc,hd,hcard⟩ := minimum_exists H he
  have hh := cycle_decomposition_vertex_count H D hc hd v
  have hb := Finset.card_filter_le D (fun C => v ∈ C.verts)
  have hn := number_le_envelope hle he
  omega

lemma degree_sum_le (G : SimpleGraph V) (v : V) :
    (∑ H ∈ evenSubgraphs G, H.degree v) ≤
      2 * envelope G * ((evenSubgraphs G).card - 1) := by
  have hzero : (⊥ : SimpleGraph V).degree v = 0 := by
    simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
    simp
  have heq := Finset.sum_erase_add (s := evenSubgraphs G)
    (f := fun H : SimpleGraph V => H.degree v) (bot_mem G)
  dsimp only at heq
  simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hzero heq ⊢
  rw [hzero,Nat.add_zero] at heq
  rw [← heq]
  have hsum := Finset.sum_le_sum (s := (evenSubgraphs G).erase ⊥)
    (f := fun H : SimpleGraph V => H.degree v) (g := fun _ => 2 * envelope G)
    (fun H hH => even_degree_le_twice_envelope (Finset.mem_erase.mp hH).2 v)
  simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card,
    Finset.sum_const,smul_eq_mul,nsmul_eq_mul,Finset.card_erase_of_mem (bot_mem G),
    Nat.mul_comm] using hsum

/-- A strict bound follows because the empty restriction contributes zero
rather than the maximum permitted degree to the average. -/
lemma core_degree_lt_four_envelope (G : SimpleGraph V) (v : V)
    (hpos : 0 < envelope G) : (core G).degree v < 4 * envelope G := by
  have hp : 0 < (evenSubgraphs G).card := Finset.card_pos.mpr
    (FractionalEnvelope.evenSubgraphs_nonempty G)
  have hs := degree_sum G v
  have hb := degree_sum_le G v
  have hpred : (evenSubgraphs G).card - 1 + 1 = (evenSubgraphs G).card := by omega
  by_contra! hn
  nlinarith

/-- In particular, an envelope-at-most-one graph has at most three cyclic
edges incident to each vertex. Bridges need not obey this bound. -/
lemma core_degree_le_three (G : SimpleGraph V) (hG : envelope G ≤ 1) (v : V) :
    (core G).degree v ≤ 3 := by
  have hp : 0 < (evenSubgraphs G).card := Finset.card_pos.mpr
    (FractionalEnvelope.evenSubgraphs_nonempty G)
  have hs := degree_sum G v
  have hb := degree_sum_le G v
  have hpred : (evenSubgraphs G).card - 1 + 1 = (evenSubgraphs G).card := by omega
  by_contra! hn
  have hbound : (∑ H ∈ evenSubgraphs G, H.degree v) ≤
      2 * ((evenSubgraphs G).card - 1) := by
    exact hb.trans (Nat.mul_le_mul_right _ (by omega))
  nlinarith

lemma core_adj_iff_piece (G : SimpleGraph V) (v w : V) :
    (core G).Adj v w ↔ ∃ C : G.Subgraph,
      (C.coe.Connected ∧ C.coe.IsRegularOfDegree 2) ∧ C.Adj v w := by
  constructor
  · rintro ⟨H,hH,ha⟩
    obtain ⟨hle,he⟩ := mem_evenSubgraphs.mp hH
    obtain ⟨D,hc,hd⟩ := even_cycle_decomposition H he
    have hh : s(v,w) ∈ ⋃ C ∈ D, C.edgeSet := hd.2.symm ▸ ha
    obtain ⟨C,hC,hvw⟩ := Set.mem_iUnion₂.mp hh
    refine ⟨promote hle C,⟨(hc C hC).1,?_⟩,hvw⟩
    intro x
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using (hc C hC).2 x
  · rintro ⟨C,hc,hvw⟩
    exact ⟨C.spanningCoe,mem_evenSubgraphs.mpr ⟨C.spanningCoe_le,
      CriticalOutsideCycles.cycle_even C hc⟩,hvw⟩

lemma core_adj_iff_not_bridge (G : SimpleGraph V) (v w : V) :
    (core G).Adj v w ↔ G.Adj v w ∧ ¬ G.IsBridge s(v,w) := by
  constructor
  · intro h
    refine ⟨core_le G h,?_⟩
    obtain ⟨C,hc,hvw⟩ := (core_adj_iff_piece G v w).mp h
    obtain ⟨p,hp,heq⟩ := CycleRing.cycle_piece_walk_at C hc.1 hc.2 v (C.edge_vert hvw)
    intro hb
    apply (isBridge_iff_adj_and_forall_cycle_notMem.mp hb).2 p hp
    apply p.mem_edges_toSubgraph.mp
    rw [heq]
    exact hvw
  · rintro ⟨hvw,hb⟩
    by_contra hn
    apply hb
    apply isBridge_iff_adj_and_forall_cycle_notMem.mpr
    refine ⟨hvw,?_⟩
    intro a p hp he
    apply hn
    apply (core_adj_iff_piece G v w).mpr
    exact ⟨p.toSubgraph,cycle_subgraph_regular G hp,p.mem_edges_toSubgraph.mpr he⟩

lemma evenSubgraphs_core (G : SimpleGraph V) : evenSubgraphs (core G) = evenSubgraphs G := by
  ext H
  constructor
  · intro hH
    obtain ⟨hle,he⟩ := mem_evenSubgraphs.mp hH
    exact mem_evenSubgraphs.mpr ⟨hle.trans (core_le G),he⟩
  · intro hH
    exact mem_evenSubgraphs.mpr ⟨even_le_core hH,(mem_evenSubgraphs.mp hH).2⟩

lemma core_idempotent (G : SimpleGraph V) : core (core G) = core G := by
  ext v w
  change (∃ H ∈ evenSubgraphs (core G), H.Adj v w) ↔ ∃ H ∈ evenSubgraphs G, H.Adj v w
  rw [evenSubgraphs_core]

lemma envelope_core (G : SimpleGraph V) : envelope (core G) = envelope G := by
  unfold envelope
  rw [evenSubgraphs_core]

lemma core_no_bridges (G : SimpleGraph V) (e : Sym2 V) : ¬ (core G).IsBridge e := by
  induction e using Sym2.ind with
  | h v w =>
    intro hb
    have ha := (isBridge_iff.mp hb).1
    have hh : (core (core G)).Adj v w := by simpa only [core_idempotent] using ha
    exact ((core_adj_iff_not_bridge (core G) v w).mp hh).2 hb

lemma core_degree_two_le {G : SimpleGraph V} {v : V} (hv : v ∈ (core G).support) :
    2 ≤ (core G).degree v := by
  obtain ⟨w,hw⟩ := hv
  obtain ⟨C,hc,hvw⟩ := (core_adj_iff_piece G v w).mp hw
  have hC : C.spanningCoe ≤ core G := even_le_core
    (mem_evenSubgraphs.mpr ⟨C.spanningCoe_le,CriticalOutsideCycles.cycle_even C hc⟩)
  have hh := SimpleGraph.degree_le_of_le (v := v) hC
  have hdeg := CriticalNestedCycles.cycle_degree C hc v
  rw [if_pos (C.edge_vert hvw)] at hdeg
  simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hh hdeg ⊢
  omega

lemma core_degree_two_or_three (G : SimpleGraph V) (hG : envelope G ≤ 1)
    {v : V} (hv : v ∈ (core G).support) :
    (core G).degree v = 2 ∨ (core G).degree v = 3 := by
  have hl := core_degree_two_le hv
  have hu := core_degree_le_three G hG v
  omega

lemma outside_core_acyclic (G : SimpleGraph V) : (G \ core G).IsAcyclic := by
  intro v p hp
  have hle : G \ core G ≤ G := sdiff_le
  have hq := hp.mapLe hle
  have hh := (core_adj_iff_piece G v (p.mapLe hle).snd).mpr
    ⟨(p.mapLe hle).toSubgraph,cycle_subgraph_regular G hq,
      (p.mapLe hle).toSubgraph_adj_snd hq.not_nil⟩
  have hadj : (G \ core G).Adj v p.snd := p.adj_snd hp.not_nil
  have hsnd : (p.mapLe hle).snd = p.snd := by simp [Walk.mapLe]
  rw [hsnd] at hh
  exact hadj.2 hh

/-- No two genuine cycles are edge-disjoint. The graph itself need not be even. -/
def NoTwoCycles (G : SimpleGraph V) : Prop :=
  ∀ P Q : G.Subgraph,
    (P.coe.Connected ∧ P.coe.IsRegularOfDegree 2) →
    (Q.coe.Connected ∧ Q.coe.IsRegularOfDegree 2) →
    ¬ Disjoint P.edgeSet Q.edgeSet

lemma envelope_le_one_of_no_two {G : SimpleGraph V} (hG : NoTwoCycles G) : envelope G ≤ 1 := by
  apply envelope_le
  intro H hHG heH
  obtain ⟨D,hc,hd,hcard⟩ := minimum_exists H heH
  by_contra! hn
  obtain ⟨P,hP,Q,hQ,hPQ⟩ := Finset.one_lt_card.mp (show 1 < D.card by omega)
  let p := FractionalCycles.promoteCycle hHG (⟨P,hc P hP⟩ : FractionalCycles.CyclePiece H)
  let q := FractionalCycles.promoteCycle hHG (⟨Q,hc Q hQ⟩ : FractionalCycles.CyclePiece H)
  exact hG p.val q.val p.property q.property (hd.1 hP hQ hPQ)

lemma no_two_of_envelope_le_one {G : SimpleGraph V} (hG : envelope G ≤ 1) : NoTwoCycles G := by
  intro P Q hp hq hd
  have hne : P ≠ Q := by
    intro heq
    obtain ⟨e,he⟩ := cycle_edgeSet_nonempty P hp.1 hp.2
    exact Set.disjoint_left.mp hd he (heq ▸ he)
  have hcU : ∀ J ∈ ({P,Q} : Finset G.Subgraph),
      J.coe.Connected ∧ J.coe.IsRegularOfDegree 2 := by
    intro J hJ
    simp only [Finset.mem_insert,Finset.mem_singleton] at hJ
    rcases hJ with rfl | rfl <;> assumption
  have hdU : Set.PairwiseDisjoint (({P,Q} : Finset G.Subgraph) : Set G.Subgraph)
      (fun J => J.edgeSet) := by
    intro A hA B hB hAB
    simp only [Finset.mem_coe,Finset.mem_insert,Finset.mem_singleton] at hA hB
    rcases hA with rfl | rfl <;> rcases hB with rfl | rfl
    · exact (hAB rfl).elim
    · exact hd
    · exact hd.symm
    · exact (hAB rfl).elim
  have heU := SmallSlackExact.union_even {P,Q} hcU hdU
  have hfrac := SmallSlackExact.pair_exact P Q hne hp hq hd
  have hupper := FractionalEnvelope.optimum_le_number (unionPieces G {P,Q}) (by
    intro v
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using heU v)
  have hn := number_le_envelope (unionPieces_le G {P,Q}) heU
  have hlow : 2 ≤ cycleNumber (unionPieces G {P,Q}) := by
    rw [hfrac] at hupper
    exact_mod_cast hupper
  omega

lemma no_two_iff_envelope_le_one (G : SimpleGraph V) : NoTwoCycles G ↔ envelope G ≤ 1 :=
  ⟨envelope_le_one_of_no_two,no_two_of_envelope_le_one⟩

lemma core_degree_le_three_of_no_two {G : SimpleGraph V} (hG : NoTwoCycles G) (v : V) :
    (core G).degree v ≤ 3 := core_degree_le_three G (envelope_le_one_of_no_two hG) v

/-- With envelope at most one there is at most one nontrivial cyclic
component. Isolated vertices of the ambient type are harmless. -/
lemma core_reachable {G : SimpleGraph V} (hG : envelope G ≤ 1)
    {v w : V} (hv : v ∈ (core G).support) (hw : w ∈ (core G).support) :
    (core G).Reachable v w := by
  obtain ⟨a,hva⟩ := hv
  obtain ⟨b,hwb⟩ := hw
  have hva' : (core (core G)).Adj v a := by simpa only [core_idempotent] using hva
  have hwb' : (core (core G)).Adj w b := by simpa only [core_idempotent] using hwb
  obtain ⟨P,hp,hP⟩ := (core_adj_iff_piece (core G) v a).mp hva'
  obtain ⟨Q,hq,hQ⟩ := (core_adj_iff_piece (core G) w b).mp hwb'
  have hn := no_two_of_envelope_le_one (G := core G) (by simpa [envelope_core] using hG)
    P Q hp hq
  obtain ⟨e,heP,heQ⟩ := Set.not_disjoint_iff.mp hn
  induction e using Sym2.ind with
  | h x y =>
    have hvx : (core G).Reachable v x :=
      (hp.1.preconnected ⟨v,P.edge_vert hP⟩ ⟨x,P.edge_vert heP⟩).map P.hom
    have hxw : (core G).Reachable x w :=
      (hq.1.preconnected ⟨x,Q.edge_vert heQ⟩ ⟨w,Q.edge_vert hQ⟩).map Q.hom
    exact hvx.trans hxw

lemma walk_support_of_start_supported {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (hu : u ∈ G.support) : ∀ x ∈ p.support, x ∈ G.support := by
  induction p with
  | nil => simpa using hu
  | @cons a b c hab p ih =>
    intro x hx
    simp only [Walk.support_cons,List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hu
    · exact ih ⟨a,hab.symm⟩ x hx

lemma core_connected_on_support {G : SimpleGraph V} (hG : envelope G ≤ 1)
    (hne : core G ≠ ⊥) : ((core G).induce (core G).support).Connected := by
  obtain ⟨a,b,hab⟩ := SimpleGraph.ne_bot_iff_exists_adj.mp hne
  letI : Nonempty (core G).support := ⟨⟨a,⟨b,hab⟩⟩⟩
  apply Connected.mk
  intro u v
  obtain ⟨p⟩ := core_reachable hG u.property v.property
  exact ⟨p.induce _ (walk_support_of_start_supported p u.property)⟩

end Erdos184.EvenCycleCore
