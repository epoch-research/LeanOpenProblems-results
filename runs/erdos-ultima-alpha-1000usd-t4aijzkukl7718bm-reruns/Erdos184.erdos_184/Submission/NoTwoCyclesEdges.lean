import Submission.NoTwoCyclesCore
import Submission.ActualPartialSmoothing

/-! Edge bounds for graphs without two edge-disjoint cycles.
These auxiliary results do not assert the original conjecture. -/
open SimpleGraph
open scoped Classical
namespace Erdos184.NoTwoCyclesEdges
open EvenCycleCore PartialSmoothing CountCritical CycleEnvelope
variable {V : Type*} [Fintype V]
set_option maxHeartbeats 1000000

lemma no_two_mono {G A : SimpleGraph V} (h : A ≤ G) (hG : NoTwoCycles G) :
    NoTwoCycles A := by
  intro P Q hp hq hd
  let p := FractionalCycles.promoteCycle h (⟨P,hp⟩ : FractionalCycles.CyclePiece A)
  let q := FractionalCycles.promoteCycle h (⟨Q,hq⟩ : FractionalCycles.CyclePiece A)
  exact hG p.val q.val p.property q.property hd

lemma cycle_reambient {G K : SimpleGraph V} (P : G.Subgraph)
    (hp : P.coe.Connected ∧ P.coe.IsRegularOfDegree 2) (h : P.spanningCoe ≤ K) :
    ∃ Q : K.Subgraph, (Q.coe.Connected ∧ Q.coe.IsRegularOfDegree 2) ∧
      Q.edgeSet = P.edgeSet := by
  let Q : K.Subgraph :=
    { verts := P.verts
      Adj := P.Adj
      adj_sub := fun hx => h hx
      edge_vert := P.edge_vert
      symm := P.symm }
  refine ⟨Q,⟨hp.1,?_⟩,rfl⟩
  intro v
  simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hp.2 v

lemma residual_acyclic {G : SimpleGraph V} (hG : NoTwoCycles G)
    (P : G.Subgraph) (hp : P.coe.Connected ∧ P.coe.IsRegularOfDegree 2) :
    (G \ P.spanningCoe).IsAcyclic := by
  intro v p hc
  let Q := FractionalCycles.promoteCycle (show G \ P.spanningCoe ≤ G from sdiff_le)
    (⟨p.toSubgraph,cycle_subgraph_regular _ hc⟩ : FractionalCycles.CyclePiece (G \ P.spanningCoe))
  apply hG P Q.val hp Q.property
  apply Set.disjoint_left.mpr
  intro e heP heQ
  have hh := p.toSubgraph.edgeSet_subset heQ
  rw [edgeSet_sdiff] at hh
  exact hh.2 heP

lemma short_cycle_edge_bound {G : SimpleGraph V} (hG : NoTwoCycles G)
    (P : G.Subgraph) (hp : P.coe.Connected ∧ P.coe.IsRegularOfDegree 2)
    (hlen : P.edgeSet.ncard ≤ 4) : G.edgeSet.ncard ≤ G.support.ncard + 3 := by
  obtain ⟨e,he⟩ := cycle_edgeSet_nonempty P hp.1 hp.2
  have hsne : G.support.Nonempty := by
    induction e using Sym2.ind with
    | h u v => exact ⟨u,⟨v,P.adj_sub he⟩⟩
  letI : Nonempty G.support := hsne.to_subtype
  let R := G \ P.spanningCoe
  have hRle : R ≤ G := sdiff_le
  have hRsup : R.support ⊆ G.support := support_mono hRle
  have hforest := forest_edge_card_lt_vertex_card (R.induce G.support)
    ((residual_acyclic hG P hp).comap (Embedding.induce G.support).toHom Subtype.val_injective)
  have hcard := R.card_edgeFinset_induce_of_support_subset hRsup
  simp only [edgeFinset_card,← Nat.card_eq_fintype_card,Nat.card_coe_set_eq] at hforest hcard
  rw [hcard] at hforest
  have hc : R.edgeSet.ncard + P.edgeSet.ncard = G.edgeSet.ncard := by
    dsimp only [R]
    rw [edgeSet_sdiff]
    change (G.edgeSet \ P.edgeSet).ncard + P.edgeSet.ncard = G.edgeSet.ncard
    exact Set.ncard_diff_add_ncard_of_subset P.edgeSet_subset
  omega

lemma short_cycle_of_min_degree_three {G : SimpleGraph V} (hG : NoTwoCycles G)
    (hne : G ≠ ⊥) (hmin : ∀ v ∈ G.support, 3 ≤ G.degree v) :
    ∃ v, ∃ p : G.Walk v v, p.IsCycle ∧ p.length ≤ 4 := by
  by_contra! hn
  obtain ⟨H,hHG,heH,_,hvH⟩ := HighGirthCritical.exists_cycle_union 1 G hne
    (by intro v hv; simpa using hmin v hv) (by intro v p hp; have := hn v p hp; omega)
  have hnH := number_le_envelope hHG heH
  have hfH := FractionalEnvelope.optimum_le_number H heH
  have hg := envelope_le_one_of_no_two hG
  rw [hvH] at hfH
  have hh : 2 ≤ CycleNumberSubmodularity.cycleNumber H := by exact_mod_cast hfH
  omega

lemma edge_bound_of_min_degree_three {G : SimpleGraph V} (hG : NoTwoCycles G)
    (hne : G ≠ ⊥) (hmin : ∀ v ∈ G.support, 3 ≤ G.degree v) :
    G.edgeSet.ncard ≤ G.support.ncard + 3 := by
  obtain ⟨v,p,hp,hlen⟩ := short_cycle_of_min_degree_three hG hne hmin
  apply short_cycle_edge_bound hG p.toSubgraph (cycle_subgraph_regular G hp)
  have hh := trail_spanning_edge_card p hp.isTrail
  simp only [edgeFinset_card,← Nat.card_eq_fintype_card,Nat.card_coe_set_eq] at hh
  exact hh.le.trans hlen

lemma cycle_avoiding_smoothing_edge (A : SimpleGraph V) (v a b : V)
    (P : (smooth A a b).Subgraph)
    (hp : P.coe.Connected ∧ P.coe.IsRegularOfDegree 2) (hn : ¬P.Adj a b) :
    ∃ Q : (unsmooth A v a b).Subgraph,
      (Q.coe.Connected ∧ Q.coe.IsRegularOfDegree 2) ∧ Q.edgeSet = P.edgeSet := by
  apply cycle_reambient P hp
  intro x y hxy
  apply base_le_unsmooth A v a b
  rcases P.adj_sub hxy with h | h
  · exact h
  · obtain ⟨(⟨rfl,rfl⟩ | ⟨rfl,rfl⟩),_⟩ := (edge_adj ..).mp h
    · exact (hn hxy).elim
    · exact (hn (P.symm hxy)).elim

lemma smooth_apex_unsupported (A : SimpleGraph V) {v a b : V}
    (hva : v ≠ a) (hvb : v ≠ b) (hiso : ∀ w, ¬A.Adj v w) :
    v ∉ (smooth A a b).support := by
  rintro ⟨w,hw⟩
  rcases hw with hw | hw
  · exact hiso w hw
  · obtain ⟨(⟨hx,_⟩ | ⟨hx,_⟩),_⟩ := (edge_adj ..).mp hw
    · exact hva hx
    · exact hvb hx

lemma no_two_smooth (A : SimpleGraph V) {v a b : V}
    (hva : v ≠ a) (hvb : v ≠ b) (hab : a ≠ b)
    (hiso : ∀ w, ¬A.Adj v w) (hG : NoTwoCycles (unsmooth A v a b)) :
    NoTwoCycles (smooth A a b) := by
  have hmarked (P Q : (smooth A a b).Subgraph)
      (hp : P.coe.Connected ∧ P.coe.IsRegularOfDegree 2)
      (hq : Q.coe.Connected ∧ Q.coe.IsRegularOfDegree 2)
      (hd : Disjoint P.edgeSet Q.edgeSet) (he : P.Adj a b) : False := by
    have hnQ : ¬Q.Adj a b := fun h => Set.disjoint_left.mp hd
      (show s(a,b) ∈ P.edgeSet from he) (show s(a,b) ∈ Q.edgeSet from h)
    have hvP : v ∉ P.verts := fun h => smooth_apex_unsupported A hva hvb hiso
      (CriticalOutsideCycles.cycle_verts_in_support P hp.2 h)
    obtain ⟨P',hp',hP'⟩ := lift_avoiding_cycle A hva hvb hab P hp he hvP
    obtain ⟨Q',hq',hQ'⟩ := cycle_avoiding_smoothing_edge A v a b Q hq hnQ
    apply hG P' Q' hp' hq'
    rw [hP',hQ']
    apply Set.disjoint_left.mpr
    intro e heP heQ
    simp only [Set.mem_insert_iff,Set.mem_diff,Set.mem_singleton_iff] at heP
    rcases heP with rfl | rfl | heP
    · exact smooth_apex_unsupported A hva hvb hiso ⟨a,Q.adj_sub heQ⟩
    · exact smooth_apex_unsupported A hva hvb hiso ⟨b,Q.adj_sub heQ⟩
    · exact Set.disjoint_left.mp hd heP.1 heQ
  intro P Q hp hq hd
  by_cases heP : P.Adj a b
  · exact hmarked P Q hp hq hd heP
  by_cases heQ : Q.Adj a b
  · exact hmarked Q P hq hp hd.symm heQ
  obtain ⟨P',hp',hP'⟩ := cycle_avoiding_smoothing_edge A v a b P hp heP
  obtain ⟨Q',hq',hQ'⟩ := cycle_avoiding_smoothing_edge A v a b Q hq heQ
  exact hG P' Q' hp' hq' (by rwa [hP',hQ'])

lemma smooth_support_subset (A : SimpleGraph V) {v a b : V}
    (hva : v ≠ a) (hvb : v ≠ b) (hiso : ∀ w, ¬A.Adj v w) :
    (smooth A a b).support ⊆ (unsmooth A v a b).support \ {v} := by
  intro x hx
  refine ⟨?_,?_⟩
  · obtain ⟨y,hxy⟩ := hx
    rcases hxy with hxy | hxy
    · exact ⟨y,base_le_unsmooth A v a b hxy⟩
    · obtain ⟨(⟨rfl,_⟩ | ⟨rfl,_⟩),_⟩ := (edge_adj ..).mp hxy
      · exact ⟨v,(unsmooth_left A hva).symm⟩
      · exact ⟨v,(unsmooth_right A hvb).symm⟩
  · intro he
    have he' : x = v := he
    exact smooth_apex_unsupported A hva hvb hiso (he' ▸ hx)

lemma support_card_drop {G A : SimpleGraph V} {v : V}
    (h : A.support ⊆ G.support \ {v}) (hv : v ∈ G.support) :
    A.support.ncard + 1 ≤ G.support.ncard := by
  have hle := Set.ncard_le_ncard h
  have heq := Set.ncard_diff_singleton_add_one hv
  omega

lemma triangle_walk {G : SimpleGraph V} {v a b : V}
    (hva : G.Adj v a) (hab : G.Adj a b) (hbv : G.Adj b v) :
    ∃ p : G.Walk v v, p.IsCycle ∧ p.length = 3 := by
  let p : G.Walk v v := .cons hva (.cons hab (.cons hbv .nil))
  refine ⟨p,?_,rfl⟩
  apply (Walk.cons_isCycle_iff _ _).mpr
  constructor
  · rw [Walk.isPath_def]
    change [a,b,v].Nodup
    simp [hva.ne.symm,hab.ne,hbv.ne]
  · simp [hva.ne,hab.ne,hbv.ne.symm]

/-- The edge surplus of a graph with no two edge-disjoint cycles is at most three.
The bound is sharp for K₃,₃. -/
lemma edge_bound (G : SimpleGraph V) (hG : NoTwoCycles G) :
    G.edgeSet.ncard ≤ G.support.ncard + 3 := by
  generalize hn : G.support.ncard = n
  induction n using Nat.strong_induction_on generalizing G with
  | h n ih =>
    by_cases hbot : G = ⊥
    · subst G
      simp
    by_cases hshort : ∃ v, ∃ p : G.Walk v v, p.IsCycle ∧ p.length ≤ 4
    · obtain ⟨v,p,hp,hlen⟩ := hshort
      have hh := trail_spanning_edge_card p hp.isTrail
      simp only [edgeFinset_card,← Nat.card_eq_fintype_card,Nat.card_coe_set_eq] at hh
      have hb := short_cycle_edge_bound hG p.toSubgraph (cycle_subgraph_regular G hp)
        (hh.le.trans hlen)
      omega
    have hvsmall : ∃ v ∈ G.support, G.degree v ≤ 2 := by
      by_contra! hv
      apply hshort
      exact short_cycle_of_min_degree_three hG hbot (by intro v hm; have := hv v hm; omega)
    obtain ⟨v,hvs,hvsmall⟩ := hvsmall
    have hvpos := (G.degree_pos_iff_mem_support v).mpr hvs
    by_cases hv1 : G.degree v = 1
    · let R := G.deleteIncidenceSet v
      have hs : R.support.ncard + 1 ≤ G.support.ncard :=
        support_card_drop (G.support_deleteIncidenceSet_subset v) hvs
      have hR := ih R.support.ncard (by omega) R (no_two_mono (G.deleteIncidenceSet_le v) hG) rfl
      have hc := G.card_edgeFinset_deleteIncidenceSet v
      have hd := G.degree_le_card_edgeFinset v
      simp only [edgeFinset_card,← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card,
        Nat.card_coe_set_eq] at hc hd hv1
      change R.edgeSet.ncard = G.edgeSet.ncard - (G.neighborSet v).ncard at hc
      omega
    have hv2 : G.degree v = 2 := by omega
    have hvN : (G.neighborSet v).ncard = 2 := by
      simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card,Nat.card_coe_set_eq] using hv2
    obtain ⟨a,b,hab,hN⟩ := Set.ncard_eq_two.mp hvN
    have hva : G.Adj v a := by change a ∈ G.neighborSet v; rw [hN]; simp
    have hvb : G.Adj v b := by change b ∈ G.neighborSet v; rw [hN]; simp
    have hnotab : ¬G.Adj a b := by
      intro habG
      obtain ⟨p,hp,hl⟩ := triangle_walk hva habG hvb.symm
      exact hshort ⟨v,p,hp,by omega⟩
    let A := removeSpokes G v a b
    have hiso : ∀ w, ¬A.Adj v w := by
      intro w hw
      have hwG : w ∈ G.neighborSet v := (G.deleteEdges_le _) hw
      rw [hN] at hwG
      rcases hwG with hwA | hwG
      · rw [hwA] at hw
        exact removeSpokes_left G v a b hw
      · have hw' : w = b := hwG
        subst w
        exact removeSpokes_right G v a b hw
    have heq : unsmooth A v a b = G := unsmooth_removeSpokes G hva hvb
    let S := smooth A a b
    have hS : NoTwoCycles S := no_two_smooth A hva.ne hvb.ne hab hiso (by rwa [heq])
    have hsup : S.support ⊆ G.support \ {v} := by
      have hh := smooth_support_subset A hva.ne hvb.ne hiso
      rwa [heq] at hh
    have hs := support_card_drop hsup hvs
    have hbound := ih S.support.ncard (by omega) S hS rfl
    have hc := edge_card_relation A hva.ne hvb.ne hab (hiso a) (hiso b)
      (removeSpokes_pair (v := v) G hnotab)
    rw [heq] at hc
    change S.edgeSet.ncard + 1 = G.edgeSet.ncard at hc
    omega

lemma edge_bound_order (G : SimpleGraph V) (hG : NoTwoCycles G) :
    G.edgeFinset.card ≤ Fintype.card V + 3 := by
  have hb := edge_bound G hG
  have hs : G.support.ncard ≤ Fintype.card V := by
    simpa only [Nat.card_eq_fintype_card] using Set.ncard_le_card G.support
  simp only [edgeFinset_card,← Nat.card_eq_fintype_card,Nat.card_coe_set_eq] at hs ⊢
  omega

end Erdos184.NoTwoCyclesEdges
