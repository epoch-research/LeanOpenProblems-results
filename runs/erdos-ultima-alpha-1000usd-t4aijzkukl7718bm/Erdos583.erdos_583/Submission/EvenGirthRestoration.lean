import Submission.NormalForestRestoration

/-! Repeated normal restoration when small even-vertex sets induce forests. -/
namespace Erdos583EvenGirthRestorationDevelopment
open SimpleGraph Erdos583Work Erdos583EvenEdgeRestorationDevelopment
open Erdos583NormalForestRestorationDevelopment Erdos583Work.EvenMatchingRestore
open scoped Classical
set_option maxHeartbeats 1600000
set_option Elab.async false

lemma small_even_forests_delete_edge {V : Type*} [Fintype V] {G : SimpleGraph V}
    {u v : V} (h : G.Adj v u)
    (hu : Even (Nat.card (G.neighborSet u))) (hv : Even (Nat.card (G.neighborSet v)))
    (hf : SmallEvenForests G) : SmallEvenForests (G.deleteEdges {s(v,u)}) := by
  classical
  let J := G.deleteEdges {s(v,u)}
  have hcount : evenCount J+2=evenCount G := by
    simp only [evenCount_eq_filter,J]
    exact even_count_delete_edge h hu hv
  intro S hS hsize
  have hS' : S ⊆ {x | Even (Nat.card (G.neighborSet x))} := by
    intro x hx
    by_cases hxu : x=u
    · subst x; exact hu
    by_cases hxv : x=v
    · subst x; exact hv
    · have hd : Nat.card (J.neighborSet x)=Nat.card (G.neighborSet x) := by
        simp only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree,J]
        exact degree_delete_edge_other G hxv hxu
      have hh := hS hx
      change Even (Nat.card (J.neighborSet x)) at hh
      rwa [hd] at hh
  have hforest := hf S hS' (by change 2*S.ncard ≤ evenCount J+2 at hsize; omega)
  exact hforest.anti (fun _ _ hxy ↦ G.deleteEdges_le _ hxy)

lemma restore_matching_small_even_forests {V : Type*} [Fintype V] (G F : SimpleGraph V)
    (hFG : F ≤ G) (hm : ∀ x, (F.neighborSet x).Subsingleton)
    (he : ∀ ⦃x y⦄, F.Adj x y → Even (Nat.card (G.neighborSet x)))
    (hf : SmallEvenForests G)
    (hbase : NormalBound (G \ F)) : NormalBound G := by
  classical
  induction hn : F.edgeSet.ncard using Nat.strong_induction_on generalizing G F with
  | h n ih =>
    by_cases hbot : F=⊥
    · have hEq : G \ F=G := by
        ext a b
        simp only [hbot,sdiff_adj,bot_adj,not_false_eq_true,and_true]
      rw [hEq] at hbase
      exact hbase
    obtain ⟨v,u,h⟩ := ne_bot_iff_exists_adj.mp hbot
    let J := G.deleteEdges {s(v,u)}
    let K := F.deleteEdges {s(v,u)}
    have hKJ : K ≤ J := deleteEdges_mono hFG
    have hKm : ∀ x, (K.neighborSet x).Subsingleton := by
      intro x a ha b hb
      exact hm x (F.deleteEdges_le _ ha) (F.deleteEdges_le _ hb)
    have hKe : ∀ ⦃x y⦄, K.Adj x y → Even (Nat.card (J.neighborSet x)) := by
      intro x y hxy
      obtain ⟨hxv,hxu⟩ := matching_delete_endpoints hm h hxy
      have heq : Nat.card (J.neighborSet x)=Nat.card (G.neighborSet x) := by
        simp only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree]
        exact degree_delete_edge_other G hxv hxu
      rw [heq]
      exact he (F.deleteEdges_le _ hxy)
    have hJf := small_even_forests_delete_edge (hFG h) (he h.symm) (he h) hf
    have hdiff : J \ K=G \ F := by
      ext a b
      simp only [J,K,sdiff_adj,deleteEdges_adj,Set.mem_singleton_iff]
      constructor
      · rintro ⟨⟨hab,hne⟩,hn⟩
        exact ⟨hab,fun hF ↦ hn ⟨hF,hne⟩⟩
      · rintro ⟨hab,hn⟩
        refine ⟨⟨hab,?_⟩,fun hh ↦ hn hh.1⟩
        intro heq
        exact hn ((F.adj_congr_of_sym2 heq).mpr h)
    have hlt : K.edgeSet.ncard<n := by
      rw [←hn]
      change (F.deleteEdges {s(v,u)}).edgeSet.ncard < F.edgeSet.ncard
      rw [edgeSet_deleteEdges]
      exact Set.ncard_diff_singleton_lt_of_mem (show s(v,u) ∈ F.edgeSet from h)
    have hbaseJ : NormalBound (J \ K) := by rwa [hdiff]
    have hNJ := ih K.edgeSet.ncard hlt J K hKJ hKm hKe hJf hbaseJ rfl
    exact restore_normal_small_even_forests (hFG h) (he h.symm) (he h) hf hNJ


lemma normal_bound_of_matching_deficiency_le_three {V : Type*} [Fintype V]
    (G F : SimpleGraph V) (hFG : F ≤ G) (hm : ∀ x, (F.neighborSet x).Subsingleton)
    (he : ∀ ⦃x y⦄, F.Adj x y → Even (Nat.card (G.neighborSet x)))
    (hf : SmallEvenForests G)
    (hsmall : {x : V | Even (Nat.card (G.neighborSet x)) ∧ F.neighborSet x=∅}.ncard ≤ 3) :
    NormalBound G := by
  apply restore_matching_small_even_forests G F hFG hm he hf
  apply normal_bound_of_three_even
  have hset : {x : V | Even (Nat.card ((G \ F).neighborSet x))}=
      {x : V | Even (Nat.card (G.neighborSet x)) ∧ F.neighborSet x=∅} := by
    ext x; exact even_after_matching_iff G F hFG hm he x
  simpa only [evenCount,hset] using hsmall

lemma small_even_forests_of_egirth {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hg : ((evenCount G/2+1 : ℕ) : ℕ∞) < (G.induce {x | Even (Nat.card (G.neighborSet x))}).egirth) :
    SmallEvenForests G := by
  intro S hS hsize a p hp
  let f := G.induceHomOfLE hS
  have hcycle : (p.map f.toHom).IsCycle := hp.map f.injective
  have hlen : p.length ≤ S.ncard := by
    have hc := Set.ncard_le_card (p.toSubgraph.verts)
    rw [Walk.verts_toSubgraph,cycle_support_ncard hp] at hc
    simpa only [Nat.card_coe_set_eq] using hc
  have hbound := egirth_le_length hcycle
  rw [Walk.length_map] at hbound
  have hc : (p.length : ℕ∞) ≤ ((evenCount G/2+1 : ℕ) : ℕ∞) := by
    exact_mod_cast (show p.length ≤ evenCount G/2+1 by omega)
  exact (not_lt_of_ge (hbound.trans hc)) hg

/-- A matching leaving at most three even vertices uncovered suffices if every
cycle in the even-induced graph is longer than half its vertex count plus one.
The conclusion retains a normal decomposition, not just a path count. -/
lemma normal_bound_of_even_girth {V : Type*} [Fintype V]
    (G F : SimpleGraph V) (hFG : F ≤ G) (hm : ∀ x, (F.neighborSet x).Subsingleton)
    (he : ∀ ⦃x y⦄, F.Adj x y → Even (Nat.card (G.neighborSet x)))
    (hg : ((evenCount G/2+1 : ℕ) : ℕ∞) < (G.induce {x | Even (Nat.card (G.neighborSet x))}).egirth)
    (hsmall : {x : V | Even (Nat.card (G.neighborSet x)) ∧ F.neighborSet x=∅}.ncard ≤ 3) :
    NormalBound G :=
  normal_bound_of_matching_deficiency_le_three G F hFG hm he
    (small_even_forests_of_egirth G hg) hsmall

end Erdos583EvenGirthRestorationDevelopment
