import Submission.LocalZeroNormalization
import Submission.ThreeEvenSharpRestoration

/-! Exact endpoint transport while restoring a guarded simple path. The
neighborhood guard is an explicit hypothesis, not an automatic property of
arbitrary paths. -/
namespace Erdos583GuardedPathRestorationDevelopment
open SimpleGraph Erdos583Work Erdos583Work.QuotaTrails
open Erdos583Work.PendantCompletion Erdos583Work.EndpointSelection
open Erdos583Work.ComponentDeficit
open Erdos583EvenEdgeRestorationDevelopment
open Erdos583LocalZeroNormalizationDevelopment
open Erdos583ThreeEvenSharpRestorationDevelopment
open scoped Classical
set_option maxHeartbeats 2500000
set_option Elab.async false

lemma delete_cons_edge_restoration {V : Type*} {G : SimpleGraph V} {s x b : V}
    (h : G.Adj s x) (Q : G.Walk x b) (hp : (Walk.cons h Q).IsPath) :
    (G.deleteEdges (Walk.cons h Q).toSubgraph.edgeSet) ≤ G.deleteEdges Q.toSubgraph.edgeSet ∧
    (G.deleteEdges Q.toSubgraph.edgeSet).Adj x s ∧
    s(x,s) ∉ (G.deleteEdges (Walk.cons h Q).toSubgraph.edgeSet).edgeSet ∧
    (G.deleteEdges Q.toSubgraph.edgeSet).edgeSet=
      insert s(x,s) (G.deleteEdges (Walk.cons h Q).toSubgraph.edgeSet).edgeSet := by
  have hn : s(s,x) ∉ Q.edges := (Walk.isTrail_cons h Q).mp hp.isTrail |>.2
  refine ⟨?_,?_,?_,?_⟩
  · intro u v huv
    obtain ⟨huv,he⟩ := deleteEdges_adj.mp huv
    refine deleteEdges_adj.mpr ⟨huv,?_⟩
    intro hv
    exact he ((Walk.cons h Q).mem_edges_toSubgraph.mpr (by
      simp only [Walk.edges_cons,List.mem_cons]
      exact Or.inr (Q.mem_edges_toSubgraph.mp hv)))
  · refine deleteEdges_adj.mpr ⟨h.symm,?_⟩
    simpa only [Walk.mem_edges_toSubgraph,Sym2.eq_swap] using hn
  · simp [edgeSet_deleteEdges,Sym2.eq_swap]
  · ext e
    simp only [edgeSet_deleteEdges,Set.mem_diff,Set.mem_insert_iff,
      Walk.mem_edges_toSubgraph,Walk.edges_cons,List.mem_cons,Sym2.eq_swap (a := x)]
    constructor
    · rintro ⟨he,hne⟩
      by_cases hh : e=s(s,x)
      · exact Or.inl hh
      · exact Or.inr ⟨he,not_or.mpr ⟨hh,hne⟩⟩
    · rintro (rfl|⟨he,hne⟩)
      · exact ⟨h,hn⟩
      · exact ⟨he,fun hh ↦ hne (Or.inr hh)⟩

/-- The one extra endpoint can be transported through every vertex of the
restored path. Each new endpoint must avoid adjacency to at least one of the
two possible zero-quota labels. -/
lemma restore_guarded_path_tracked {V : Type*} [Fintype V] {G : SimpleGraph V}
    {k : ℕ} (a c : V) (hac : a ≠ c) {s b : V} (Q : G.Walk s b)
    (hQ : Q.IsPath) (T : TrailFamily (G.deleteEdges Q.toSubgraph.edgeSet) k)
    (hp : ∀ i, (T.walk i).IsPath)
    (hq : ∀ z, T.quota z+(if a=z then 1 else 0)=
      (if z=c then 0 else 1)+(if s=z then 1 else 0))
    (hg : ∀ z ∈ Q.support, z ≠ s → ¬G.Adj z a ∨ ¬G.Adj z c) :
    ∃ P : TrailFamily G k, (∀ i, (P.walk i).IsPath) ∧
      ∀ z, P.quota z+(if a=z then 1 else 0)=
        (if z=c then 0 else 1)+(if b=z then 1 else 0) := by
  classical
  induction Q with
  | @nil s =>
    have hh : ∃ P : TrailFamily (G.deleteEdges (Walk.nil : G.Walk s s).toSubgraph.edgeSet) k,
        (∀ i, (P.walk i).IsPath) ∧ ∀ z, P.quota z+(if a=z then 1 else 0)=
          (if z=c then 0 else 1)+(if s=z then 1 else 0) := ⟨T,hp,hq⟩
    have he : (Walk.nil : G.Walk s s).toSubgraph.edgeSet=∅ := by
      ext e
      simp only [Walk.mem_edges_toSubgraph,Walk.edges_nil,List.not_mem_nil,Set.notMem_empty]
    rw [he,deleteEdges_empty] at hh
    exact hh
  | @cons s x b h Q ih =>
    obtain ⟨hle,hxs,hnew,hcover⟩ := delete_cons_edge_restoration h Q hQ
    have hpos : 0 < T.quota s := by
      have hh := hq s
      by_cases has : a=s
      · have hsc : s ≠ c := has ▸ hac
        simp only [has,hsc,↓reduceIte] at hh
        omega
      · simp only [has,↓reduceIte,add_zero] at hh
        split_ifs at hh <;> omega
    obtain ⟨i,hi⟩ := DeletionEndpoint.endpoint_of_positive_quota T hpos
    obtain ⟨U,hUs,hUq,_,hUr⟩ := DeletionEndpoint.append_new_edge_tracked hle T hp i hi hxs hnew hcover
    have hquota (z : V) : U.quota z+(if a=z then 1 else 0)=
        (if z=c then 0 else 1)+(if x=z then 1 else 0) := by
      have h1 := hq z
      have h2 := hUq z
      omega
    have hz (z : V) (hzero : U.quota z=0) : z=a ∨ z=c := by
      by_cases hza : z=a
      · exact Or.inl hza
      by_cases hzc : z=c
      · exact Or.inr hzc
      have hh := hquota z
      simp only [hzero,Ne.symm hza,hzc,↓reduceIte,add_zero] at hh
      omega
    have hgx : ¬G.Adj x a ∨ ¬G.Adj x c :=
      hg x (by simp only [Walk.support_cons,List.mem_cons]; exact Or.inr Q.start_mem_support) h.ne.symm
    have hfew : {z | (G.deleteEdges Q.toSubgraph.edgeSet).Adj x z ∧ U.quota z=0}.Subsingleton := by
      intro y hy z hz'
      have hyG := G.deleteEdges_le _ hy.1
      have hzG := G.deleteEdges_le _ hz'.1
      rcases hgx with hxa|hxc
      · exact ((hz y hy.2).resolve_left (fun he ↦ hxa (he ▸ hyG))).trans
          ((hz z hz'.2).resolve_left (fun he ↦ hxa (he ▸ hzG))).symm
      · exact ((hz y hy.2).resolve_right (fun he ↦ hxc (he ▸ hyG))).trans
          ((hz z hz'.2).resolve_right (fun he ↦ hxc (he ▸ hzG))).symm
    obtain ⟨R,hR,hRq⟩ : ∃ R : TrailFamily (G.deleteEdges Q.toSubgraph.edgeSet) k,
        (∀ i, (R.walk i).IsPath) ∧ ∀ z, R.quota z=U.quota z := by
      by_cases hUp : ∀ i, (U.walk i).IsPath
      · exact ⟨U,hUp,fun _ ↦ rfl⟩
      · have hs : U.score+1=(G.deleteEdges Q.toSubgraph.edgeSet).edgeSet.ncard+k := by
          have hu := U.score_le_edges_add
          have hn := U.score_eq_edges_add_iff.not.mpr hUp
          omega
        obtain ⟨R,hRq,hR⟩ := repair_of_subsingleton_zero_neighbors U x hs (hUr hUp) hfew
        exact ⟨R,hR,hRq⟩
    apply ih hQ.of_cons R hR (fun z ↦ by rw [hRq]; exact hquota z)
    intro z hzQ _
    apply hg z (by simp only [Walk.support_cons,List.mem_cons]; exact Or.inr hzQ)
    intro hzs
    exact (Walk.cons_isPath_iff h Q).mp hQ |>.2 (hzs ▸ hzQ)


lemma sharp_three_even_guarded_path {V : Type*} [Fintype V] (G : SimpleGraph V)
    (a b c : V) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (he : ∀ x, Even (Nat.card (G.neighborSet x)) ↔ x=a ∨ x=b ∨ x=c)
    (P : G.Walk a b) (hP : P.IsPath)
    (hg : ∀ z ∈ P.support, z ≠ a → ¬G.Adj z a ∨ ¬G.Adj z c) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      2*D.card+1 ≤ Fintype.card V := by
  classical
  let J := G.deleteEdges P.toSubgraph.edgeSet
  have hpn : ¬P.Nil := Walk.not_nil_of_ne hab
  have hJa : Odd (Nat.card (J.neighborSet a)) := by
    have hd := ncard_neighbor_delete_subgraph_add P.toSubgraph a
    rw [hP.neighborSet_toSubgraph_startpoint hpn,Set.ncard_singleton] at hd
    have hh := (he a).mpr (Or.inl rfl)
    simp only [Nat.card_coe_set_eq,Nat.even_iff] at hh
    rw [Nat.card_coe_set_eq,Nat.odd_iff]
    change (J.neighborSet a).ncard+1=_ at hd
    omega
  have hJb : Odd (Nat.card (J.neighborSet b)) := by
    have hd := ncard_neighbor_delete_subgraph_add P.toSubgraph b
    rw [hP.neighborSet_toSubgraph_endpoint hpn,Set.ncard_singleton] at hd
    have hh := (he b).mpr (Or.inr (Or.inl rfl))
    simp only [Nat.card_coe_set_eq,Nat.even_iff] at hh
    rw [Nat.card_coe_set_eq,Nat.odd_iff]
    change (J.neighborSet b).ncard+1=_ at hd
    omega
  have hJc : Even (Nat.card (J.neighborSet c)) :=
    (TipParity.delete_path_degree_parity P hP hac.symm hbc.symm).mpr
      ((he c).mpr (Or.inr (Or.inr rfl)))
  have ho (z : V) (hzc : z ≠ c) : Odd (Nat.card (J.neighborSet z)) := by
    by_cases hza : z=a
    · subst z; exact hJa
    by_cases hzb : z=b
    · subst z; exact hJb
    apply Nat.not_even_iff_odd.mp
    rw [TipParity.delete_path_degree_parity P hP hza hzb,he]
    tauto
  obtain ⟨D,hD,hne,hDq,hDc⟩ := MarkedBudgets.one_even_path_partition J c hJc ho
  obtain ⟨T,hT,hTq⟩ := decomposition_path_family_tracked D hD hne
  obtain ⟨Q,hQ,_⟩ := restore_guarded_path_tracked a c hac P hP T hT
    (fun z ↦ by rw [hTq,hDq]) hg
  obtain ⟨E,hE,hEc⟩ := MatchingAppend.path_family_partition Q hQ
  exact ⟨E,hE,by omega⟩

lemma shortest_path_guard_of_first_nonadjacent {V : Type*} {G : SimpleGraph V}
    {a b c : V} (P : G.Walk a b) (hl : P.length=G.dist a b)
    (hfirst : ¬G.Adj P.snd c) :
    ∀ z ∈ P.support, z ≠ a → ¬G.Adj z a ∨ ¬G.Adj z c := by
  intro z hz _
  by_cases hs : z=P.snd
  · exact Or.inr (hs ▸ hfirst)
  · exact Or.inl (fun hza ↦ TipParity.shortest_path_neighbor_not_mem P hl hza.symm hs hz)

/-- Removing the common neighbors of a and c leaves an a-b connection only
if the sharp floor-half bound already holds. -/
lemma sharp_three_even_common_neighbor_avoidance {V : Type*} [Fintype V]
    (G : SimpleGraph V) (a b c : V) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (he : ∀ x, Even (Nat.card (G.neighborSet x)) ↔ x=a ∨ x=b ∨ x=c)
    (haS : a ∈ {z | ¬G.Adj z a ∨ ¬G.Adj z c})
    (hbS : b ∈ {z | ¬G.Adj z a ∨ ¬G.Adj z c})
    (hr : (G.induce {z | ¬G.Adj z a ∨ ¬G.Adj z c}).Reachable ⟨a,haS⟩ ⟨b,hbS⟩) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      2*D.card+1 ≤ Fintype.card V := by
  obtain ⟨P,hP,_⟩ := hr.exists_path_of_dist
  let f := (Embedding.induce (G := G) {z | ¬G.Adj z a ∨ ¬G.Adj z c}).toHom
  apply sharp_three_even_guarded_path G a b c hab hac hbc he (P.map f)
    (Walk.map_isPath_of_injective Subtype.val_injective hP)
  intro z hz _
  rw [Walk.support_map] at hz
  obtain ⟨x,_,hx⟩ := List.mem_map.mp hz
  exact hx ▸ x.property

end Erdos583GuardedPathRestorationDevelopment
