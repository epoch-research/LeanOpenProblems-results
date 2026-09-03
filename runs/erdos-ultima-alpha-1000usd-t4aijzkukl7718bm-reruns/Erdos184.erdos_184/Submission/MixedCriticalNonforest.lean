import Submission.MixedCritical

/-! A seven-vertex graph needs at least seven mixed pieces. Extracting a
mixed-critical restriction disproves the auxiliary assertion that all such
critical graphs are forests. It does NOT disprove the O(n) conjecture. -/
open SimpleGraph
open scoped Classical
namespace Erdos184.MixedCriticalNonforest
open MixedCritical RankCritical
set_option maxHeartbeats 1000000

abbrev V := Fin 7

def G : SimpleGraph V where
  Adj u v := u ≠ v ∧ (u.val < 3 ∨ v.val < 3)
  symm := by intro u v h; exact ⟨h.1.symm,h.2.symm⟩
  loopless := by intro v h; exact h.1 rfl

instance : DecidableRel G.Adj := fun u v => inferInstanceAs (Decidable (u ≠ v ∧ (u.val < 3 ∨ v.val < 3)))

lemma hub_degrees : G.degree 0 = 6 ∧ G.degree 1 = 6 ∧ G.degree 2 = 6 := by decide
lemma leaf_degrees : G.degree 3 = 3 ∧ G.degree 4 = 3 ∧ G.degree 5 = 3 ∧ G.degree 6 = 3 := by decide

def leaves : Finset V := {3,4,5,6}

lemma leaves_independent : ∀ u ∈ leaves, ∀ v ∈ leaves, ¬G.Adj u v := by decide

lemma partition_lower (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, IsCycleOrEdge H.coe) (hd : IsDecomposition G D) :
    7 ≤ D.card := by
  obtain ⟨c,s,A,B,hcard,hA,hB,hBs,hdeg,heA,hcA⟩ := split_partition G D hc hd
  have hleaf (v : V) (hv : v ∈ leaves) : 1 ≤ B.degree v := by
    have hvG : G.degree v = 3 := by
      have hh : ∀ v ∈ leaves, G.degree v = 3 := by decide
      exact hh v hv
    have hh := hdeg v
    obtain ⟨r,hr⟩ := heA v
    simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hh hvG hr ⊢
    rw [hvG] at hh
    omega
  have h3 := hleaf 3 (by decide)
  have h4 := hleaf 4 (by decide)
  have h5 := hleaf 5 (by decide)
  have h6 := hleaf 6 (by decide)
  have hs := independent_degree_sum_le_edges B leaves
    (fun u hu v hv huv => leaves_independent u hu v hv (hB huv))
  have hhand := B.sum_degrees_eq_twice_card_edges
  rw [hBs] at hs hhand
  simp only [leaves,Finset.sum_insert,Finset.sum_singleton,
    Finset.mem_insert,Finset.mem_singleton,Fin.reduceEq,or_false,not_false_eq_true] at hs
  simp [Fin.sum_univ_succ] at hhand
  have h0 := hdeg 0
  have h1 := hdeg 1
  have h2 := hdeg 2
  have hhubs := hub_degrees
  simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hhubs h0 h1 h2
  rw [hhubs.1] at h0
  rw [hhubs.2.1] at h1
  rw [hhubs.2.2] at h2
  have ha0 := hcA 0
  have ha1 := hcA 1
  have ha2 := hcA 2
  simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at ha0 ha1 ha2 hs hhand h3 h4 h5 h6
  omega

lemma number_lower : 7 ≤ number G := by
  obtain ⟨D,hc,hd,hcard⟩ := minimum_exists G
  rw [← hcard]
  exact partition_lower D hc hd

lemma connected : G.Connected := by
  have hr (v : V) : G.Reachable 0 v := by
    by_cases h : 0 = v
    · exact h ▸ Reachable.refl _
    · exact (show G.Adj 0 v from ⟨h,Or.inl (by decide)⟩).reachable
  exact ⟨fun u v => (hr u).symm.trans (hr v)⟩

lemma rank_eq : graphRank G = 6 := by
  have h := RankCriticalPartitions.connected_rank connected
  simpa using h

lemma exists_nonforest_critical :
    ∃ H : SimpleGraph V, H ≤ G ∧ MixedCritical.IsCritical 7 H ∧ ¬H.IsAcyclic := by
  obtain ⟨H,hHG,hH⟩ := extract G 7 (by decide) number_lower
  refine ⟨H,hHG,hH,?_⟩
  intro hf
  have hh := forest_number_eq_rank H hf
  have hr := rank_mono hHG
  rw [hH.1] at hh
  rw [rank_eq] at hr
  omega

def cycleEdges : Finset (Sym2 V) :=
  {s(0,1),s(1,6),s(6,2),s(2,0),s(0,3),s(3,1),s(1,5),s(5,2),s(2,4),s(4,0)}
def A : SimpleGraph V := fromEdgeSet (cycleEdges : Set (Sym2 V))
instance : DecidableRel A.Adj := by unfold A; infer_instance

lemma A_le : A ≤ G := by intro u v; revert u v; decide
instance : DecidableRel (G \ A).Adj := fun u v =>
  inferInstanceAs (Decidable (G.Adj u v ∧ ¬A.Adj u v))
lemma residual_card : (G \ A).edgeFinset.card = 5 := by
  rw [edgeFinset_sdiff]
  decide

def w0 : A.Walk 0 0 :=
  .cons (by decide : A.Adj 0 1) <|
  .cons (by decide : A.Adj 1 6) <|
  .cons (by decide : A.Adj 6 2) <|
  .cons (by decide : A.Adj 2 0) .nil

def w1 : A.Walk 0 0 :=
  .cons (by decide : A.Adj 0 3) <|
  .cons (by decide : A.Adj 3 1) <|
  .cons (by decide : A.Adj 1 5) <|
  .cons (by decide : A.Adj 5 2) <|
  .cons (by decide : A.Adj 2 4) <|
  .cons (by decide : A.Adj 4 0) .nil

lemma w0_cycle : w0.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w0],by decide⟩
lemma w1_cycle : w1.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w1],by decide⟩

def walks : Fin 2 → A.Walk 0 0 := ![w0,w1]

lemma A_number_le : number A ≤ 2 := by
  obtain ⟨D,hc,hd,hb⟩ := CycleNumberSubmodularity.upper_of_walk_family A
    (fun i : Fin 2 => ⟨0,walks i⟩)
    (by intro i; fin_cases i; exact w0_cycle; exact w1_cycle)
    (by intro i j hij; rw [List.disjoint_left]; revert i j; decide)
    (by intro u v; revert u v; decide)
  have hh := number_le A D (by
    intro H hH
    left
    refine ⟨(hc H hH).1,?_⟩
    intro v
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using (hc H hH).2 v) hd
  exact hh.trans (by simpa using hb)

lemma number_eq : number G = 7 := by
  apply Nat.le_antisymm _ number_lower
  have hh := number_le_restriction_add_edges A_le
  have hu := A_number_le
  have hr := residual_card
  simp only [edgeFinset_card,← Nat.card_eq_fintype_card,Nat.card_coe_set_eq] at hr
  rw [hr] at hh
  omega

lemma not_all_critical_forests :
    ¬ (∀ (H : SimpleGraph V) (k : ℕ), MixedCritical.IsCritical k H → H.IsAcyclic) := by
  intro h
  obtain ⟨H,_,hH,hn⟩ := exists_nonforest_critical
  exact hn (h H 7 hH)

lemma not_mixed_rank_bound : ¬ (∀ H : SimpleGraph V, number H ≤ graphRank H) := by
  intro h
  have hh := h G
  rw [number_eq,rank_eq] at hh
  omega

end Erdos184.MixedCriticalNonforest
