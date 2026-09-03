import Submission.BlockRankPotential
import Submission.DegreeTightOptimal

/-!
Strictness and plateau properties of the block-rank potential. These do not
prove existence of a descending cycle in every count-critical graph.
-/
open SimpleGraph
open scoped Classical BigOperators
namespace Erdos184.BlockRankPotential
open RankCritical RainbowComplements
variable {V : Type*} [Fintype V]
set_option maxHeartbeats 1000000

lemma deleted_rank_eq_of_plateau {A G : SimpleGraph V} (h : A ≤ G)
    (hr : graphRank A = graphRank G) (hp : potential A = potential G) (v : V) :
    graphRank (A.deleteIncidenceSet v) = graphRank (G.deleteIncidenceSet v) := by
  have hm := rank_mono (delete_mono h v)
  by_contra hn
  have hd := potential_drop_of_deleted_rank_drop h hr v (lt_of_le_of_ne hm hn)
  omega

lemma deleted_reachable_iff_of_plateau {A G : SimpleGraph V} (h : A ≤ G)
    (hr : graphRank A = graphRank G) (hp : potential A = potential G) (v x y : V) :
    (A.deleteIncidenceSet v).Reachable x y ↔ (G.deleteIncidenceSet v).Reachable x y :=
  reachable_iff_of_rank_eq (delete_mono h v) (deleted_rank_eq_of_plateau h hr hp v) x y

omit [Fintype V] in
lemma not_reachable_of_unsupported {G : SimpleGraph V} {v w : V}
    (hv : v ∉ G.support) (hvw : v ≠ w) : ¬G.Reachable v w :=
  fun h => hv (mem_support_of_reachable hvw h)

lemma two_spoke_increase (A : SimpleGraph V) (v u w : V)
    (hv : v ∉ A.support) (hvu : v ≠ u) (hvw : v ≠ w) (huw : u ≠ w)
    (hr : A.Reachable u w) :
    potential A + 1 ≤ potential ((A ⊔ edge v u) ⊔ edge v w) := by
  let B := A ⊔ edge v u
  let G := B ⊔ edge v w
  have hPB : potential B = potential A := potential_add_bridge A
    (not_reachable_of_unsupported hv hvu)
  have hreach : B.Reachable v w :=
    (show B.Adj v u from Or.inr ((edge_adj ..).mpr ⟨Or.inl ⟨rfl,rfl⟩,hvu⟩)).reachable.trans
      (hr.mono le_sup_left)
  have hRG : graphRank B = graphRank G := (rank_add_edge_of_reachable B hreach).symm
  have hBu : B.deleteIncidenceSet u = A.deleteIncidenceSet u := by
    ext x y
    simp only [B,deleteIncidenceSet_adj,sup_adj,edge_adj]
    tauto
  have hGu : G.deleteIncidenceSet u = A.deleteIncidenceSet u ⊔ edge v w := by
    ext x y
    simp only [G,B,deleteIncidenceSet_adj,sup_adj,edge_adj]
    constructor
    · tauto
    · rintro (hh | ⟨(⟨rfl,rfl⟩ | ⟨rfl,rfl⟩),hne⟩)
      · tauto
      · exact ⟨Or.inr ⟨Or.inl ⟨rfl,rfl⟩,hne⟩,hvu,huw.symm⟩
      · exact ⟨Or.inr ⟨Or.inr ⟨rfl,rfl⟩,hne⟩,huw.symm,hvu⟩
  have hnu : ¬ (A.deleteIncidenceSet u).Reachable v w := fun h =>
    not_reachable_of_unsupported hv hvw (h.mono (A.deleteIncidenceSet_le u))
  have hru : graphRank (B.deleteIncidenceSet u) < graphRank (G.deleteIncidenceSet u) := by
    rw [hBu,hGu,rank_add_edge_of_not_reachable _ hnu]
    omega
  have hh := potential_drop_of_deleted_rank_drop (show B ≤ G from le_sup_left) hRG u hru
  simpa only [hPB] using hh

omit [Fintype V] in
lemma cycle_neighbors_reachable_after_vertex_delete {G : SimpleGraph V} {v : V}
    (p : G.Walk v v) (hp : p.IsCycle) :
    (G.deleteIncidenceSet v).Reachable p.snd p.penultimate := by
  have hlen := hp.three_le_length
  have hnot (i : ℕ) (hi : 0 < i) (hil : i < p.length) : p.getVert i ≠ v := by
    intro he
    have hh := (hp.getVert_endpoint_iff hil.le).mp he
    omega
  have hseq : ∀ i : ℕ, i ≤ p.length-2 →
      (G.deleteIncidenceSet v).Reachable (p.getVert 1) (p.getVert (i+1)) := by
    intro i
    induction i with
    | zero => intro _; exact .refl _
    | succ i ih =>
      intro hi
      apply (ih (by omega)).trans
      apply Adj.reachable
      apply deleteIncidenceSet_adj.mpr
      refine ⟨?_,hnot _ (by omega) (by omega),hnot _ (by omega) (by omega)⟩
      exact p.adj_getVert_succ (by omega)
  have hh := hseq (p.length-2) le_rfl
  simpa only [Walk.snd,Walk.penultimate,show p.length-2+1=p.length-1 by omega] using hh

lemma cycle_vertex_deletion_drop {G : SimpleGraph V} {v : V}
    (p : G.Walk v v) (hp : p.IsCycle) :
    potential (G.deleteIncidenceSet v) + 1 ≤ potential G := by
  let A := G.deleteIncidenceSet v
  have hv : v ∉ A.support := by
    rintro ⟨w,hw⟩
    exact (deleteIncidenceSet_adj.mp hw).2.1 rfl
  have hvs := p.adj_snd hp.not_nil
  have hvp := (p.adj_penultimate hp.not_nil).symm
  have hle : (A ⊔ edge v p.snd) ⊔ edge v p.penultimate ≤ G := by
    exact sup_le (sup_le (G.deleteIncidenceSet_le v) ((edge_le_iff G).mpr (Or.inr hvs)))
      ((edge_le_iff G).mpr (Or.inr hvp))
  have hh := two_spoke_increase A v p.snd p.penultimate hv hvs.ne hvp.ne
    hp.snd_ne_penultimate (cycle_neighbors_reachable_after_vertex_delete p hp)
  exact hh.trans (potential_mono hle)

lemma cycle_piece_vertex_deletion_drop {G : SimpleGraph V} (C : G.Subgraph)
    (hc : C.coe.Connected ∧ C.coe.IsRegularOfDegree 2) (v : V) (hv : v ∈ C.verts) :
    potential (G.deleteIncidenceSet v) + 1 ≤ potential G := by
  obtain ⟨p,hp,_⟩ := CycleRing.cycle_piece_walk_at C hc.1 hc.2 v hv
  exact cycle_vertex_deletion_drop p hp

lemma even_supported_vertex_deletion_drop {G : SimpleGraph V}
    (he : ∀ v, Even (G.degree v)) (v : V) (hv : v ∈ G.support) :
    potential (G.deleteIncidenceSet v) + 1 ≤ potential G := by
  obtain ⟨w,hw⟩ := hv
  obtain ⟨D,hc,hd⟩ := even_cycle_decomposition G he
  have hh : s(v,w) ∈ G.edgeSet := hw
  rw [← hd.2] at hh
  obtain ⟨C,hC,heC⟩ := Set.mem_iUnion₂.mp hh
  exact cycle_piece_vertex_deletion_drop C (hc C hC) v (C.edge_vert heC)

lemma potential_drop_of_support_loss {A G : SimpleGraph V} (h : A ≤ G)
    (he : ∀ v, Even (G.degree v)) (v : V) (hvG : v ∈ G.support) (hvA : v ∉ A.support) :
    potential A + 1 ≤ potential G := by
  have hAD : A ≤ G.deleteIncidenceSet v := by
    intro x y hxy
    exact deleteIncidenceSet_adj.mpr ⟨h hxy,
      fun hx => hvA (hx ▸ ⟨y,hxy⟩),fun hy => hvA (hy ▸ ⟨x,hxy.symm⟩)⟩
  have hm := potential_mono hAD
  have hd := even_supported_vertex_deletion_drop he v hvG
  omega

lemma support_eq_of_even_plateau {A G : SimpleGraph V} (h : A ≤ G)
    (he : ∀ v, Even (G.degree v)) (hp : potential A = potential G) : A.support = G.support := by
  apply Set.Subset.antisymm (SimpleGraph.support_mono h)
  intro v hv
  by_contra hn
  have hh := potential_drop_of_support_loss h he v hv hn
  omega

lemma cycle_drop_of_degree_two {G : SimpleGraph V} (C : G.Subgraph)
    (hc : C.coe.Connected ∧ C.coe.IsRegularOfDegree 2) (v : V)
    (hv : v ∈ C.verts) (hd : G.degree v = 2) :
    potential (G \ C.spanningCoe) + 1 ≤ potential G := by
  have hcd : C.spanningCoe.degree v = 2 := by
    have hh := hc.2 ⟨v,hv⟩
    rw [Subgraph.coe_degree] at hh
    rw [Subgraph.degree_spanningCoe]
    simpa only [Subgraph.degree, ← Nat.card_eq_fintype_card] using hh
  have hzero : (G \ C.spanningCoe).degree v = 0 := by
    have hh := degree_sdiff_of_le C.spanningCoe_le v
    simp only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hh hd hcd ⊢
    omega
  have hn : v ∉ (G \ C.spanningCoe).support :=
    ((G \ C.spanningCoe).degree_eq_zero_iff_notMem_support v).mp hzero
  have hle : G \ C.spanningCoe ≤ G.deleteIncidenceSet v := by
    intro x y hxy
    exact deleteIncidenceSet_adj.mpr ⟨hxy.1,
      fun hx => hn (hx ▸ ⟨y,hxy⟩),fun hy => hn (hy ▸ ⟨x,hxy.symm⟩)⟩
  have hm := potential_mono hle
  have hh := cycle_piece_vertex_deletion_drop C hc v hv
  omega

lemma exists_cycle_drop_of_degree_two {G : SimpleGraph V}
    (he : ∀ v, Even (G.degree v)) (v : V) (hv : G.degree v = 2) :
    ∃ C : G.Subgraph, (C.coe.Connected ∧ C.coe.IsRegularOfDegree 2) ∧
      potential (G \ C.spanningCoe) + 1 ≤ potential G := by
  obtain ⟨D,hc,hd⟩ := even_cycle_decomposition G he
  have hp : 0 < G.degree v := by omega
  obtain ⟨w,hw⟩ := (G.degree_pos_iff_exists_adj v).mp hp
  have hh : s(v,w) ∈ G.edgeSet := hw
  rw [← hd.2] at hh
  obtain ⟨C,hC,heC⟩ := Set.mem_iUnion₂.mp hh
  exact ⟨C,hc C hC,cycle_drop_of_degree_two C (hc C hC) v (C.edge_vert heC) hv⟩

lemma critical_degree_tight_cycle_drop {G : SimpleGraph V} {k : ℕ}
    (hG : CountCritical.IsCountCritical k G) (hk : 0 < k)
    (v : V) (hv : G.degree v = 2*k) :
    ∃ C : G.Subgraph, (C.coe.Connected ∧ C.coe.IsRegularOfDegree 2) ∧
      potential (G \ C.spanningCoe) + 1 ≤ potential G := by
  have hne : G ≠ ⊥ := by
    intro hh
    have hn := hG.2.1
    rw [hh,CountCritical.number_bot] at hn
    omega
  obtain ⟨D,hc,hd,hcard⟩ := CountCritical.minimum_exists G hG.1
  have hD : D.card = k := hcard.trans hG.2.1
  obtain ⟨w,hw⟩ := DegreeTightOptimal.all_optimal_degree_tight_has_degree_two hG.1 hne
    hG.allCyclesOptimal D hc hd v (by simpa only [hD] using hv)
  exact exists_cycle_drop_of_degree_two hG.1 w hw

lemma critical_count_le_two_cycle_drop {G : SimpleGraph V} {k : ℕ}
    (hG : CountCritical.IsCountCritical k G) (hk : 0 < k) (hk2 : k ≤ 2) :
    ∃ C : G.Subgraph, (C.coe.Connected ∧ C.coe.IsRegularOfDegree 2) ∧
      potential (G \ C.spanningCoe) + 1 ≤ potential G := by
  have hne : G ≠ ⊥ := by
    intro hh
    have hn := hG.2.1
    rw [hh,CountCritical.number_bot] at hn
    omega
  by_cases ht : ∃ v, G.degree v = 2
  · obtain ⟨v,hv⟩ := ht
    exact exists_cycle_drop_of_degree_two hG.1 v hv
  · have hno : ∀ v, G.degree v ≠ 2 := by simpa using ht
    obtain ⟨D,hc,hd,hcard⟩ := CountCritical.minimum_exists G hG.1
    have hD : D.card = k := hcard.trans hG.2.1
    obtain ⟨v,w,hvw⟩ := SimpleGraph.ne_bot_iff_exists_adj.mp hne
    have hp := hvw.degree_pos_left
    have hb := DegreeTightOptimal.strict_degree_slack hG.1 hne hG.allCyclesOptimal hno D hc hd v
    have he := hG.1 v
    have hn := hno v
    obtain ⟨j,hj⟩ := he
    simp only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hp hb hj hn
    omega

/-- The sharp support-sensitive upper estimate, before replacing support by order. -/
lemma potential_le_twice_rank_sub_support (G : SimpleGraph V) :
    potential G ≤ 2 * (graphRank G : ℤ) - G.support.ncard := by
  have hs : (G.support.ncard : ℤ) ≤ ∑ v, (vertexLoss G v : ℤ) := by
    exact_mod_cast support_le_loss_sum G
  unfold potential
  omega

/-- A vertex-deleted graph with exactly one isolated vertex and all remaining
vertices mutually reachable has two connected components. -/
lemma deleted_component_card {G : SimpleGraph V} (v w : V) (hvw : v ≠ w)
    (hc : ∀ a b, a ≠ v → b ≠ v → (G.deleteIncidenceSet v).Reachable a b) :
    Nat.card (G.deleteIncidenceSet v).ConnectedComponent = 2 := by
  let A := G.deleteIncidenceSet v
  have hv : v ∉ A.support := by
    rintro ⟨z,hz⟩
    exact (deleteIncidenceSet_adj.mp hz).2.1 rfl
  let label : V → Bool := fun x => decide (x=v)
  have hl : ∀ a b, A.Reachable a b → label a = label b := by
    intro a b hab
    by_cases ha : a=v
    · subst a
      have hb : b=v := by
        by_contra hb
        exact not_reachable_of_unsupported hv (Ne.symm hb) hab
      simp [label,hb]
    · have hb : b≠v := by
        intro hb
        subst b
        exact not_reachable_of_unsupported hv (Ne.symm ha) hab.symm
      simp [label,ha,hb]
  let f : A.ConnectedComponent → Bool := Quot.lift label (fun a b hab => hl a b hab)
  have hi : Function.Injective f := by
    intro c d hcd
    induction c using ConnectedComponent.ind with
    | _ a =>
      induction d using ConnectedComponent.ind with
      | _ b =>
        change label a = label b at hcd
        apply ConnectedComponent.sound
        by_cases ha : a=v
        · have hb : b=v := by simpa [label,ha] using hcd.symm
          subst a; subst b; exact .refl _
        · have hb : b≠v := by simpa [label,ha] using hcd.symm
          exact hc a b ha hb
  have hs : Function.Surjective f := by
    intro b
    cases b with
    | false => exact ⟨A.connectedComponentMk w,by change label w = false; simp [label,hvw.symm]⟩
    | true => exact ⟨A.connectedComponentMk v,by change label v = true; simp [label]⟩
  simpa using Nat.card_congr (Equiv.ofBijective f ⟨hi,hs⟩)

lemma potential_of_no_cut {G : SimpleGraph V} (hG : G.Connected)
    (hn : 2 ≤ Fintype.card V)
    (hcut : ∀ v a b, a ≠ v → b ≠ v → (G.deleteIncidenceSet v).Reachable a b) :
    potential G = (Fintype.card V : ℤ) - 2 := by
  haveI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have hr := RankCriticalPartitions.connected_rank hG
  have hl : ∀ v, vertexLoss G v = 1 := by
    intro v
    obtain ⟨w,hw⟩ := exists_ne v
    have hh := deleted_component_card v w hw.symm (hcut v)
    unfold vertexLoss graphRank
    unfold graphRank at hr
    omega
  simp only [potential,hl,Nat.cast_one,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
  have hr' : (graphRank G : ℤ) + 1 = Fintype.card V := by exact_mod_cast hr
  omega

lemma rank_eq_of_even_no_cut_plateau {A G : SimpleGraph V} (h : A ≤ G)
    (he : ∀ v, Even (G.degree v)) (hG : G.Connected) (hn : 2 ≤ Fintype.card V)
    (hcut : ∀ v a b, a ≠ v → b ≠ v → (G.deleteIncidenceSet v).Reachable a b)
    (hp : potential A = potential G) : graphRank A = graphRank G := by
  haveI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have hsup : A.support = Set.univ :=
    (support_eq_of_even_plateau h he hp).trans hG.preconnected.support_eq_univ
  have hsa : A.support.ncard = Fintype.card V := by simp [hsup]
  have hu := potential_le_twice_rank_sub_support A
  rw [hp,potential_of_no_cut hG hn hcut,hsa] at hu
  have hr := RankCriticalPartitions.connected_rank hG
  have hr' : (graphRank G : ℤ) + 1 = Fintype.card V := by exact_mod_cast hr
  have hm : (graphRank A : ℤ) ≤ graphRank G := by exact_mod_cast rank_mono h
  have hh : (graphRank A : ℤ) = graphRank G := by omega
  exact_mod_cast hh

lemma plateau_iff_connected_no_cut {A G : SimpleGraph V} (h : A ≤ G)
    (he : ∀ v, Even (G.degree v)) (hG : G.Connected) (hn : 2 ≤ Fintype.card V)
    (hcut : ∀ v a b, a ≠ v → b ≠ v → (G.deleteIncidenceSet v).Reachable a b) :
    potential A = potential G ↔ A.Connected ∧
      ∀ v a b, a ≠ v → b ≠ v → (A.deleteIncidenceSet v).Reachable a b := by
  constructor
  · intro hp
    have hr := rank_eq_of_even_no_cut_plateau h he hG hn hcut hp
    haveI := hG.nonempty
    refine ⟨⟨fun a b => (reachable_iff_of_rank_eq h hr a b).mpr (hG.preconnected a b)⟩,?_⟩
    intro v a b ha hb
    exact (deleted_reachable_iff_of_plateau h hr hp v a b).mpr (hcut v a b ha hb)
  · rintro ⟨ha,hca⟩
    rw [potential_of_no_cut ha hn hca,potential_of_no_cut hG hn hcut]


end Erdos184.BlockRankPotential
