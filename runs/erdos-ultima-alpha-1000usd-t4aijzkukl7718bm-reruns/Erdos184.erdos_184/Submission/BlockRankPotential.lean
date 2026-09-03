import Submission.RankComponents
import Submission.RainbowComplements
import Submission.CountCriticalFractional

/-!
A bounded potential built from spanning-forest ranks and vertex-deleted ranks.
The required descent assertion on count-critical kernels is NOT proved here.
The identification with a sum over graph blocks is not used in this file.
-/
open SimpleGraph
open scoped Classical BigOperators
namespace Erdos184.BlockRankPotential
open RankCritical RankComponents RainbowComplements
variable {V : Type*} [Fintype V]
set_option maxHeartbeats 1000000

lemma sum_components (G : SimpleGraph V) (f : V → ℕ) :
    (∑ c : G.ConnectedComponent, ∑ v : c, f v.val) = ∑ v, f v := by
  have h := (Equiv.sigmaFiberEquiv G.connectedComponentMk).sum_comp f
  rw [Fintype.sum_sigma] at h
  exact h

lemma forest_rank (G : SimpleGraph V) (ha : G.IsAcyclic) :
    graphRank G = G.edgeFinset.card := by
  have hlocal : ∀ c : G.ConnectedComponent,
      (∑ v : c, G.degree v.val) = 2 * (Fintype.card c - 1) := by
    intro c
    have ht := ha.isTree_connectedComponent c
    have he := ht.card_edgeFinset
    have hd := c.toSimpleGraph.sum_degrees_eq_twice_card_edges
    have hs : (∑ v : c, c.toSimpleGraph.degree v) = ∑ v : c, G.degree v.val := by
      apply Finset.sum_congr rfl
      intro v _
      simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using
        component_degree G c v
    rw [hs] at hd
    omega
  have hs := Finset.sum_congr (s₁ := (Finset.univ : Finset G.ConnectedComponent)) rfl
    (fun c _ => hlocal c)
  have hs₁ := sum_components G (fun v => G.degree v)
  have hs₂ := G.sum_degrees_eq_twice_card_edges
  simp only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hs hs₁ hs₂
  rw [hs₁, ← Finset.mul_sum] at hs
  have hr := rank_eq_sum_component_order G
  simp only [← Nat.card_eq_fintype_card] at hr
  rw [← hr] at hs
  simp only [edgeFinset_card, ← Nat.card_eq_fintype_card] at hs₂ ⊢
  omega

omit [Fintype V] in
lemma delete_mono {A G : SimpleGraph V} (h : A ≤ G) (v : V) :
    A.deleteIncidenceSet v ≤ G.deleteIncidenceSet v := by
  intro x y hxy
  obtain ⟨hxy,hx,hy⟩ := deleteIncidenceSet_adj.mp hxy
  exact deleteIncidenceSet_adj.mpr ⟨h hxy,hx,hy⟩

noncomputable def vertexLoss (G : SimpleGraph V) (v : V) : ℕ :=
  graphRank G - graphRank (G.deleteIncidenceSet v)

noncomputable def potential (G : SimpleGraph V) : ℤ :=
  2 * (graphRank G : ℤ) - ∑ v, (vertexLoss G v : ℤ)

lemma loss_le_of_same_rank {A G : SimpleGraph V} (h : A ≤ G)
    (hr : graphRank A = graphRank G) (v : V) : vertexLoss G v ≤ vertexLoss A v := by
  have hd := rank_mono (delete_mono h v)
  unfold vertexLoss
  omega

lemma forest_loss (G : SimpleGraph V) (ha : G.IsAcyclic) (v : V) :
    vertexLoss G v = G.degree v := by
  have hd := G.card_edgeFinset_deleteIncidenceSet v
  have hle := G.degree_le_card_edgeFinset v
  have hf := forest_rank G ha
  have hfd := forest_rank (G.deleteIncidenceSet v) (ha.anti (G.deleteIncidenceSet_le v))
  unfold vertexLoss
  simp only [edgeFinset_card, ← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
    at hd hle hf hfd ⊢
  omega

lemma loss_sum_le (G : SimpleGraph V) : ∑ v, vertexLoss G v ≤ 2 * graphRank G := by
  obtain ⟨T,_,hm⟩ := exists_maximal_isAcyclic_of_le_isAcyclic
    (show (⊥ : SimpleGraph V) ≤ G from bot_le) isAcyclic_bot
  have hr : graphRank T = graphRank G := by
    apply rank_eq_of_adj_reachable hm.prop.1
    intro u v huv
    rw [reachable_eq_of_maximal_isAcyclic T hm]
    exact huv.reachable
  calc
    ∑ v, vertexLoss G v ≤ ∑ v, vertexLoss T v :=
      Finset.sum_le_sum (fun v _ => loss_le_of_same_rank hm.prop.1 hr v)
    _ = ∑ v, T.degree v := by
      apply Finset.sum_congr rfl
      intro v _
      simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using
        forest_loss T hm.prop.2 v
    _ = 2 * T.edgeFinset.card := T.sum_degrees_eq_twice_card_edges
    _ = 2 * graphRank G := by rw [← forest_rank T hm.prop.2,hr]

lemma potential_nonneg (G : SimpleGraph V) : 0 ≤ potential G := by
  have h : (∑ v, (vertexLoss G v : ℤ)) ≤ 2 * (graphRank G : ℤ) := by
    exact_mod_cast loss_sum_le G
  unfold potential
  omega

lemma potential_le_twice_order (G : SimpleGraph V) :
    potential G ≤ 2 * (Fintype.card V : ℤ) := by
  have hsum : 0 ≤ ∑ v, (vertexLoss G v : ℤ) := Finset.sum_nonneg (by intros; positivity)
  have hr : (graphRank G : ℤ) ≤ Fintype.card V := by exact_mod_cast rank_le_card G
  unfold potential
  omega

lemma potential_mono_of_same_rank {A G : SimpleGraph V} (h : A ≤ G)
    (hr : graphRank A = graphRank G) : potential A ≤ potential G := by
  have hs : (∑ v, (vertexLoss G v : ℤ)) ≤ ∑ v, (vertexLoss A v : ℤ) := by
    apply Finset.sum_le_sum
    intro v _
    exact_mod_cast loss_le_of_same_rank h hr v
  unfold potential
  rw [hr]
  omega

lemma potential_drop_of_deleted_rank_drop {A G : SimpleGraph V} (h : A ≤ G)
    (hr : graphRank A = graphRank G) (v : V)
    (hv : graphRank (A.deleteIncidenceSet v) < graphRank (G.deleteIncidenceSet v)) :
    potential A + 1 ≤ potential G := by
  have hG := rank_mono (G.deleteIncidenceSet_le v)
  have hA := rank_mono (A.deleteIncidenceSet_le v)
  have hl : vertexLoss G v < vertexLoss A v := by unfold vertexLoss; omega
  have hs : (∑ w, (vertexLoss G w : ℤ)) < ∑ w, (vertexLoss A w : ℤ) := by
    apply Finset.sum_lt_sum
    · intro w _
      exact_mod_cast loss_le_of_same_rank h hr w
    · exact ⟨v,Finset.mem_univ _,by exact_mod_cast hl⟩
  unfold potential
  rw [hr]
  omega

lemma loss_pos_of_supported (G : SimpleGraph V) (v : V) (hv : v ∈ G.support) :
    0 < vertexLoss G v := by
  obtain ⟨w,hw⟩ := hv
  have hm := rank_mono (G.deleteIncidenceSet_le v)
  by_contra! hn
  have he : graphRank (G.deleteIncidenceSet v) = graphRank G := by
    unfold vertexLoss at hn
    omega
  have hr := (reachable_iff_of_rank_eq (G.deleteIncidenceSet_le v) he v w).mpr hw.reachable
  obtain ⟨z,hz⟩ := mem_support_of_reachable hw.ne hr
  exact (deleteIncidenceSet_adj.mp hz).2.1 rfl

lemma support_le_loss_sum (G : SimpleGraph V) : G.support.ncard ≤ ∑ v, vertexLoss G v := by
  have h : G.support.toFinset.card ≤ ∑ v ∈ G.support.toFinset, vertexLoss G v := by
    calc
      G.support.toFinset.card = ∑ _v ∈ G.support.toFinset, 1 := by simp
      _ ≤ _ := Finset.sum_le_sum (fun v hv =>
        loss_pos_of_supported G v (Set.mem_toFinset.mp hv))
  have hs : (∑ v ∈ G.support.toFinset, vertexLoss G v) ≤ ∑ v, vertexLoss G v :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  rw [Set.ncard_eq_toFinset_card' G.support]
  exact h.trans hs

lemma potential_le_rank (G : SimpleGraph V) : potential G ≤ (graphRank G : ℤ) := by
  have hr : graphRank G ≤ G.support.ncard := by
    by_cases hb : G = ⊥
    · subst G
      rw [RankCritical.rank_bot]
      omega
    · exact (RankBlocks.rank_le_support_sub_one G hb).trans (Nat.sub_le _ _)
  have hs : (graphRank G : ℤ) ≤ ∑ v, (vertexLoss G v : ℤ) := by
    exact_mod_cast hr.trans (support_le_loss_sum G)
  unfold potential
  omega

lemma potential_le_order (G : SimpleGraph V) : potential G ≤ (Fintype.card V : ℤ) :=
  (potential_le_rank G).trans (by exact_mod_cast rank_le_card G)

lemma forest_potential (G : SimpleGraph V) (ha : G.IsAcyclic) : potential G = 0 := by
  have hs : (∑ v, vertexLoss G v) = 2 * graphRank G := by
    calc
      (∑ v, vertexLoss G v) = ∑ v, G.degree v := by
        apply Finset.sum_congr rfl
        intro v _
        simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using
          forest_loss G ha v
      _ = 2 * G.edgeFinset.card := G.sum_degrees_eq_twice_card_edges
      _ = 2 * graphRank G := by rw [forest_rank G ha]
  have hs' : (∑ v, (vertexLoss G v : ℤ)) = 2 * (graphRank G : ℤ) := by exact_mod_cast hs
  simp [potential,hs']

lemma rank_add_edge_of_reachable (G : SimpleGraph V) {u v : V}
    (h : G.Reachable u v) : graphRank (G ⊔ edge u v) = graphRank G := by
  symm
  apply rank_eq_of_adj_reachable le_sup_left
  intro x y hxy
  rcases hxy with hxy | hxy
  · exact hxy.reachable
  · rcases (edge_adj ..).mp hxy with ⟨(⟨rfl,rfl⟩ | ⟨rfl,rfl⟩),_⟩
    · exact h
    · exact h.symm

lemma rank_add_edge_of_not_reachable (G : SimpleGraph V) {u v : V}
    (h : ¬ G.Reachable u v) : graphRank (G ⊔ edge u v) = graphRank G + 1 := by
  obtain ⟨T,_,hm⟩ := exists_maximal_isAcyclic_of_le_isAcyclic
    (show (⊥ : SimpleGraph V) ≤ G from bot_le) isAcyclic_bot
  have ht : ¬ T.Reachable u v := fun hr => h (hr.mono hm.prop.1)
  have he : u ≠ v := fun he => h (he ▸ Reachable.refl _)
  have ha : (T ⊔ edge u v).IsAcyclic :=
    (isAcyclic_add_edge_iff_of_not_reachable u v ht).mpr hm.prop.2
  have hrT : graphRank T = graphRank G := by
    apply rank_eq_of_adj_reachable hm.prop.1
    intro x y hxy
    rw [reachable_eq_of_maximal_isAcyclic T hm]
    exact hxy.reachable
  have hr : graphRank (T ⊔ edge u v) = graphRank (G ⊔ edge u v) := by
    apply rank_eq_of_adj_reachable (sup_le_sup_right hm.prop.1 _)
    intro x y hxy
    rcases hxy with hxy | hxy
    · have hT : T.Reachable x y := by
        rw [reachable_eq_of_maximal_isAcyclic T hm]
        exact hxy.reachable
      exact hT.mono le_sup_left
    · exact (show (T ⊔ edge u v).Adj x y from Or.inr hxy).reachable
  have hc := T.card_edgeFinset_sup_edge (fun ha => ht ha.reachable) he
  have hf := forest_rank _ ha
  have hfT := forest_rank T hm.prop.2
  simp only [edgeFinset_card, ← Nat.card_eq_fintype_card] at hc hf hfT
  omega

lemma potential_add_bridge (G : SimpleGraph V) {u v : V} (h : ¬ G.Reachable u v) :
    potential (G ⊔ edge u v) = potential G := by
  have he : u ≠ v := fun he => h (he ▸ Reachable.refl _)
  have hr := rank_add_edge_of_not_reachable G h
  have hl : ∀ w, vertexLoss (G ⊔ edge u v) w =
      vertexLoss G w + (if w=u then 1 else 0) + (if w=v then 1 else 0) := by
    intro w
    have hm := rank_mono (G.deleteIncidenceSet_le w)
    by_cases hwu : w=u
    · subst w
      have hd : (G ⊔ edge u v).deleteIncidenceSet u = G.deleteIncidenceSet u := by
        ext x y
        simp only [deleteIncidenceSet_adj,sup_adj,edge_adj]
        tauto
      simp only [vertexLoss,hd,hr,if_true,if_neg he]
      omega
    · by_cases hwv : w=v
      · subst w
        have hd : (G ⊔ edge u v).deleteIncidenceSet v = G.deleteIncidenceSet v := by
          ext x y
          simp only [deleteIncidenceSet_adj,sup_adj,edge_adj]
          tauto
        simp only [vertexLoss,hd,hr,if_true,if_neg hwu]
        omega
      · have hd : (G ⊔ edge u v).deleteIncidenceSet w =
            G.deleteIncidenceSet w ⊔ edge u v := by
          ext x y
          simp only [deleteIncidenceSet_adj,sup_adj,edge_adj]
          constructor
          · tauto
          · rintro (hh | ⟨(⟨rfl,rfl⟩ | ⟨rfl,rfl⟩),hne⟩)
            · tauto
            · exact ⟨Or.inr ⟨Or.inl ⟨rfl,rfl⟩,hne⟩,Ne.symm hwu,Ne.symm hwv⟩
            · exact ⟨Or.inr ⟨Or.inr ⟨rfl,rfl⟩,hne⟩,Ne.symm hwv,Ne.symm hwu⟩
        have hnot : ¬ (G.deleteIncidenceSet w).Reachable u v :=
          fun hh => h (hh.mono (G.deleteIncidenceSet_le w))
        have hdr := rank_add_edge_of_not_reachable (G.deleteIncidenceSet w) hnot
        simp only [vertexLoss,hd,hr,hdr,if_neg hwu,if_neg hwv]
        omega
  have hs : (∑ w, vertexLoss (G ⊔ edge u v) w) = (∑ w, vertexLoss G w) + 2 := by
    simp_rw [hl]
    simp [Finset.sum_add_distrib]
  have hs' : (∑ w, (vertexLoss (G ⊔ edge u v) w : ℤ)) =
      (∑ w, (vertexLoss G w : ℤ)) + 2 := by exact_mod_cast hs
  unfold potential
  rw [hs',hr]
  push_cast
  ring

lemma potential_le_add_edge (G : SimpleGraph V) (u v : V) :
    potential G ≤ potential (G ⊔ edge u v) := by
  by_cases h : G.Reachable u v
  · exact potential_mono_of_same_rank le_sup_left (rank_add_edge_of_reachable G h).symm
  · rw [potential_add_bridge G h]

/-- Full edge-subgraph monotonicity, not just the equal-rank special case. -/
lemma potential_mono {A G : SimpleGraph V} (hle : A ≤ G) : potential A ≤ potential G := by
  generalize hn : G.edgeSet.ncard = n
  induction n using Nat.strong_induction_on generalizing G with
  | h n ih =>
    by_cases he : A = G
    · subst G; rfl
    · have hstrict : A.edgeSet ⊂ G.edgeSet := edgeSet_strict_mono (lt_of_le_of_ne hle he)
      obtain ⟨e,heG,heA⟩ := Set.exists_of_ssubset hstrict
      induction e using Sym2.ind with
      | h u v =>
        let H := G \ edge u v
        have hHG : H ≤ G := sdiff_le
        have hAH : A ≤ H := by
          intro x y hxy
          refine ⟨hle hxy,?_⟩
          intro hh
          rcases (edge_adj ..).mp hh with ⟨(⟨rfl,rfl⟩ | ⟨rfl,rfl⟩),_⟩
          · exact heA hxy
          · exact heA hxy.symm
        have hne : H ≠ G := by
          intro hh
          have huv : H.Adj u v := hh.symm ▸ heG
          exact huv.2 ((edge_adj ..).mpr ⟨Or.inl ⟨rfl,rfl⟩,(show G.Adj u v from heG).ne⟩)
        have hlt := CountCritical.edges_lt hHG hne
        have hb := ih H.edgeSet.ncard (by omega) hAH rfl
        have hrec : H ⊔ edge u v = G := by
          apply le_antisymm
          · exact sup_le hHG ((edge_le_iff G).mpr (Or.inr heG))
          · intro x y hxy
            by_cases hh : (edge u v).Adj x y
            · exact Or.inr hh
            · exact Or.inl ⟨hxy,hh⟩
        exact hb.trans (by simpa only [hrec] using potential_le_add_edge H u v)

/-- This descent hypothesis is the missing structural assertion. The next kernel
may be smaller than a one-cycle residual; no inheritance of criticality is assumed. -/
def CriticalDescent (G : SimpleGraph V) : Prop :=
  ∀ H : SimpleGraph V, H ≤ G → ∀ k : ℕ, 0 < k → CountCritical.IsCountCritical k H →
    ∃ K : SimpleGraph V, K ≤ H ∧ CountCritical.IsCountCritical (k-1) K ∧
      potential K + 1 ≤ potential H

lemma criticalDescent_of_cycle_descent (G : SimpleGraph V)
    (hdesc : ∀ H : SimpleGraph V, H ≤ G → ∀ k : ℕ, 0 < k →
      CountCritical.IsCountCritical k H →
      ∃ C : H.Subgraph, (C.coe.Connected ∧ C.coe.IsRegularOfDegree 2) ∧
        potential (H \ C.spanningCoe) + 1 ≤ potential H) : CriticalDescent G := by
  intro H hHG k hk hH
  obtain ⟨C,hc,hstep⟩ := hdesc H hHG k hk hH
  cases k with
  | zero => omega
  | succ j =>
    by_cases hj : j = 0
    · subst j
      refine ⟨⊥,bot_le,?_,?_⟩
      · refine ⟨by
          intro v
          simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using
            (show Even ((⊥ : SimpleGraph V).degree v) by simp),CountCritical.number_bot,?_⟩
        intro A hA hne _
        exact (hne (le_bot_iff.mp hA)).elim
      · have hn := potential_nonneg (H \ C.spanningCoe)
        rw [forest_potential _ isAcyclic_bot]
        omega
    · obtain ⟨K,hK,hcrit⟩ := hH.residual_kernel (Nat.pos_of_ne_zero hj) C hc
      refine ⟨K,hK.trans sdiff_le,by simpa using hcrit,?_⟩
      have hm := potential_mono hK
      omega

lemma critical_bound_of_descent (G : SimpleGraph V) (hdesc : CriticalDescent G) :
    ∀ k : ℕ, ∀ H : SimpleGraph V, H ≤ G → CountCritical.IsCountCritical k H →
      (k : ℤ) ≤ potential H := by
  intro k
  induction k with
  | zero => intro H _ _; exact potential_nonneg H
  | succ k ih =>
    intro H hHG hH
    obtain ⟨K,hKH,hK,hstep⟩ := hdesc H hHG (k+1) (by omega) hH
    have hK' : CountCritical.IsCountCritical k K := by simpa using hK
    have hh := ih K (hKH.trans hHG) hK'
    exact_mod_cast (show (k : ℤ) + 1 ≤ potential H by omega)

lemma decomposition_bound_of_descent (G : SimpleGraph V)
    (he : ∀ v, Even (G.degree v)) (hdesc : CriticalDescent G) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G D ∧ (D.card : ℝ) ≤ Fintype.card V := by
  apply CountCritical.bound_of_critical_subgraph_bound G he (Fintype.card V : ℝ) (by positivity)
  intro H hHG k hH
  have hh := (critical_bound_of_descent G hdesc k H hHG hH).trans (potential_le_order H)
  have hh' : k ≤ Fintype.card V := by exact_mod_cast hh
  exact_mod_cast hh'

universe u
/-- A conditional implication only: no universal critical descent is asserted. -/
lemma conjecture_of_critical_descent
    (hdesc : ∀ {V : Type u} [Fintype V] (G : SimpleGraph V), CriticalDescent G) :
    ∃ f : ℕ → ℝ,
      (f =O[Filter.atTop] fun n : ℕ => (n : ℝ)) ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
        (D.card : ℝ) ≤ f (Fintype.card V) := by
  apply conjecture_iff_even_bound.mpr
  refine ⟨1,?_⟩
  intro V _ _ G he
  obtain ⟨D,hc,hd,hbound⟩ := decomposition_bound_of_descent G he (hdesc G)
  refine ⟨D,?_,hd,by simpa using hbound⟩
  intro H hH
  apply Or.inl
  refine ⟨(hc H hH).1,?_⟩
  intro v
  simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using (hc H hH).2 v

end Erdos184.BlockRankPotential
