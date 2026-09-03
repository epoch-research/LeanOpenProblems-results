import Submission.EvenCycleCore
import Submission.PartialSmoothing

/-!
Leafless graphs with no two edge-disjoint cycles equal their cyclic core.
This is part of a restricted structural analysis, not Erdős 184.
-/
open SimpleGraph
open scoped Classical BigOperators
namespace Erdos184.NoTwoCyclesCore
open EvenCycleCore
variable {V : Type*} [Fintype V]
set_option maxHeartbeats 1000000

/-- One unit of degree deficit cannot account for a finite forest. -/
lemma not_acyclic_of_degree_defect_one (G : SimpleGraph V) (u : V)
    (hdeg : ∀ v, 2 ≤ G.degree v + if v = u then 1 else 0) : ¬ G.IsAcyclic := by
  intro ha
  letI : Nonempty V := ⟨u⟩
  have he := forest_edge_card_lt_vertex_card G ha
  have hs := G.sum_degrees_eq_twice_card_edges
  have hl := Finset.sum_le_sum (s := (Finset.univ : Finset V))
    (f := fun _ => (2 : ℕ)) (g := fun v => G.degree v + if v = u then 1 else 0)
    (fun v _ => hdeg v)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
    Finset.sum_ite_eq',Finset.mem_univ,if_true,Nat.cast_id] at hl
  omega

/-- Each side of a bridge in a graph of supported minimum degree two
contains a cycle. The ambient graph need not be even. -/
lemma cycle_in_bridge_side (G : SimpleGraph V)
    (hmin : ∀ v ∈ G.support, 2 ≤ G.degree v) {u v : V}
    (hb : G.IsBridge s(u,v)) :
    ∃ P : G.Subgraph, (P.coe.Connected ∧ P.coe.IsRegularOfDegree 2) ∧
      P.verts ⊆ ((G \ edge u v).connectedComponentMk u).supp := by
  have huv := (isBridge_iff.mp hb).1
  have hnot : ¬ (G \ edge u v).Reachable u v := (isBridge_iff.mp hb).2
  let R := G \ edge u v
  let C := R.connectedComponentMk u
  have hrle : R ≤ G := sdiff_le
  have huC : u ∈ C.supp := ConnectedComponent.connectedComponentMk_mem
  have hvC : v ∉ C.supp := fun h => hnot (C.reachable_of_mem_supp huC h)
  let root : C := ⟨u,huC⟩
  have hdeg : ∀ x : C, 2 ≤ C.toSimpleGraph.degree x + if x = root then 1 else 0 := by
    intro x
    have hxG : x.val ∈ G.support := by
      by_cases hx : x.val = u
      · exact hx.symm ▸ (show u ∈ G.support from ⟨v,huv⟩)
      · have hr : G.Reachable x.val u := (C.reachable_of_mem_supp x.property huC).mono hrle
        exact mem_support_of_reachable hx hr
    have hminx := hmin x.val hxG
    have hedge : edge u v ≤ G := (edge_le_iff G).mpr (Or.inr huv)
    have hR := degree_sdiff_of_le hedge x.val
    have hE := TwoTerminalGluing.degree_edge_eq huv.ne x.val
    have hcomp := component_degree R C x
    have hxv : x.val ≠ v := fun h => hvC (h ▸ x.property)
    simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hminx hR hE hcomp ⊢
    have hR' : Nat.card (R.neighborSet x.val) =
        Nat.card (G.neighborSet x.val) - (if x.val = u ∨ x.val = v then 1 else 0) := by
      rw [hR,hE]
    by_cases hxu : x.val = u
    · have hxroot : x = root := Subtype.ext hxu
      rw [if_pos hxroot]
      rw [if_pos (Or.inl hxu)] at hR'
      omega
    · have hxroot : x ≠ root := fun h => hxu (congrArg Subtype.val h)
      rw [if_neg hxroot]
      rw [if_neg (not_or.mpr ⟨hxu,hxv⟩)] at hR'
      omega
  have hcyc := not_acyclic_of_degree_defect_one C.toSimpleGraph root (by
    intro x
    have hh := hdeg x
    simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hh ⊢
    split_ifs with hx <;> simpa only [hx,if_pos,if_neg] using hh)
  obtain ⟨a,p,hp⟩ : ∃ a, ∃ p : C.toSimpleGraph.Walk a a, p.IsCycle := by
    simpa only [IsAcyclic,not_forall,not_not] using hcyc
  let q := (p.map C.toSimpleGraph_hom).mapLe hrle
  have hq : q.IsCycle := (hp.map Subtype.val_injective).mapLe hrle
  refine ⟨q.toSubgraph,cycle_subgraph_regular G hq,?_⟩
  intro x hx
  have hx' := q.mem_verts_toSubgraph.mp hx
  change x ∈ ((p.map C.toSimpleGraph_hom).mapLe hrle).support at hx'
  rw [Walk.support_mapLe_eq_support,Walk.support_map] at hx'
  obtain ⟨y,hy,hxy⟩ := List.mem_map.mp hx'
  exact hxy ▸ y.property

lemma no_bridges_of_min_degree_two {G : SimpleGraph V} (hG : NoTwoCycles G)
    (hmin : ∀ v ∈ G.support, 2 ≤ G.degree v) (e : Sym2 V) : ¬ G.IsBridge e := by
  induction e using Sym2.ind with
  | h u v =>
    intro hb
    obtain ⟨P,hp,hP⟩ := cycle_in_bridge_side G hmin hb
    have hb' : G.IsBridge s(v,u) := by simpa only [Sym2.eq_swap] using hb
    obtain ⟨Q,hq,hQ⟩ := cycle_in_bridge_side G hmin hb'
    have hQ' : Q.verts ⊆ ((G \ edge u v).connectedComponentMk v).supp := by
      rw [edge_comm v u] at hQ
      exact hQ
    apply hG P Q hp hq
    apply Set.disjoint_left.mpr
    intro e heP heQ
    induction e using Sym2.ind with
    | h x y =>
      let R := G \ edge u v
      have hxu := hP (P.edge_vert heP)
      have hxv := hQ' (Q.edge_vert heQ)
      have hux : R.Reachable u x := (R.connectedComponentMk u).reachable_of_mem_supp
        ConnectedComponent.connectedComponentMk_mem hxu
      have hxv' : R.Reachable x v := (R.connectedComponentMk v).reachable_of_mem_supp
        hxv ConnectedComponent.connectedComponentMk_mem
      exact (isBridge_iff.mp hb).2 (hux.trans hxv')

lemma core_eq_of_min_degree_two {G : SimpleGraph V} (hG : NoTwoCycles G)
    (hmin : ∀ v ∈ G.support, 2 ≤ G.degree v) : core G = G := by
  apply le_antisymm (core_le G)
  intro u v huv
  exact (core_adj_iff_not_bridge G u v).mpr
    ⟨huv,no_bridges_of_min_degree_two hG hmin s(u,v)⟩

lemma degree_le_three_of_min_degree_two {G : SimpleGraph V} (hG : NoTwoCycles G)
    (hmin : ∀ v ∈ G.support, 2 ≤ G.degree v) (v : V) : G.degree v ≤ 3 := by
  have hh := core_degree_le_three_of_no_two hG v
  simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hh ⊢
  rwa [core_eq_of_min_degree_two hG hmin] at hh

end Erdos184.NoTwoCyclesCore
