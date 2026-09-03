import Submission.FractionalEnvelope

/-! An optimal fractional cycle partition whose transition weights at one
vertex violate an odd-set perfect-matching inequality. This is an auxiliary
obstruction to direct local rounding, not a settlement of Erdős 184. -/
open SimpleGraph
open scoped BigOperators
namespace Erdos184.K4TransitionObstruction
open FractionalCycles FractionalEnvelope CycleNumberSubmodularity
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
abbrev V := Fin 10

def edges : Finset (Sym2 V) := {s(0,1),s(0,2),s(0,3),s(0,4),s(0,5),s(0,6),s(1,2),s(1,3),s(1,4),s(1,7),s(1,8),s(2,3),s(2,5),s(2,7),s(2,9),s(3,6),s(3,8),s(3,9)}
def G : SimpleGraph V := fromEdgeSet (edges : Set (Sym2 V))
instance : DecidableRel G.Adj := by unfold G; infer_instance
lemma G_even (v : V) : Even (G.degree v) := by revert v; decide
lemma degree_zero : G.degree 0 = 6 := by decide

def w0 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 1) <|
  .cons (by decide : G.Adj 1 2) <|
  .cons (by decide : G.Adj 2 3) <|
  .cons (by decide : G.Adj 3 0) .nil
lemma w0_cycle : w0.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w0],by decide⟩

def w1 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 1) <|
  .cons (by decide : G.Adj 1 3) <|
  .cons (by decide : G.Adj 3 2) <|
  .cons (by decide : G.Adj 2 0) .nil
lemma w1_cycle : w1.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w1],by decide⟩

def w2 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 2) <|
  .cons (by decide : G.Adj 2 1) <|
  .cons (by decide : G.Adj 1 3) <|
  .cons (by decide : G.Adj 3 0) .nil
lemma w2_cycle : w2.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w2],by decide⟩

def w3 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 4) <|
  .cons (by decide : G.Adj 4 1) <|
  .cons (by decide : G.Adj 1 7) <|
  .cons (by decide : G.Adj 7 2) <|
  .cons (by decide : G.Adj 2 9) <|
  .cons (by decide : G.Adj 9 3) <|
  .cons (by decide : G.Adj 3 6) <|
  .cons (by decide : G.Adj 6 0) .nil
lemma w3_cycle : w3.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w3],by decide⟩

def w4 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 4) <|
  .cons (by decide : G.Adj 4 1) <|
  .cons (by decide : G.Adj 1 8) <|
  .cons (by decide : G.Adj 8 3) <|
  .cons (by decide : G.Adj 3 9) <|
  .cons (by decide : G.Adj 9 2) <|
  .cons (by decide : G.Adj 2 5) <|
  .cons (by decide : G.Adj 5 0) .nil
lemma w4_cycle : w4.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w4],by decide⟩

def w5 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 5) <|
  .cons (by decide : G.Adj 5 2) <|
  .cons (by decide : G.Adj 2 7) <|
  .cons (by decide : G.Adj 7 1) <|
  .cons (by decide : G.Adj 1 8) <|
  .cons (by decide : G.Adj 8 3) <|
  .cons (by decide : G.Adj 3 6) <|
  .cons (by decide : G.Adj 6 0) .nil
lemma w5_cycle : w5.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w5],by decide⟩

def walk : Fin 6 → G.Walk 0 0 := ![w0,w1,w2,w3,w4,w5]
lemma walk_cycle (i : Fin 6) : (walk i).IsCycle := by
  fin_cases i
  · exact w0_cycle
  · exact w1_cycle
  · exact w2_cycle
  · exact w3_cycle
  · exact w4_cycle
  · exact w5_cycle

lemma walk_coverage (u v : V) :
    (∑ i : Fin 6, if s(u,v) ∈ (walk i).edges then (1 : ℕ) else 0) =
      if G.Adj u v then 2 else 0 := by revert u v; decide

open scoped Classical
attribute [local instance] cyclePieceFintype

noncomputable def C (i : Fin 6) : CyclePiece G :=
  ⟨(walk i).toSubgraph,cycle_subgraph_regular G (walk_cycle i)⟩

noncomputable def weight : CyclePiece G → ℝ := pushWeight C (fun _ => 1/2)

lemma weight_fractional : IsFractionalPartition G weight := by
  apply fractional_of_family G C (fun _ => 1/2) (by intro i; norm_num)
  intro e he
  induction e using Sym2.inductionOn with
  | _ u v =>
    have hn := walk_coverage u v
    rw [if_pos (show G.Adj u v from he)] at hn
    have hr : (∑ i : Fin 6, if s(u,v) ∈ (walk i).edges then (1 : ℝ) else 0) = 2 := by
      exact_mod_cast hn
    change (∑ i : Fin 6, if s(u,v) ∈ (walk i).toSubgraph.edgeSet then (1/2 : ℝ) else 0) = 1
    simp only [Walk.edgeSet_toSubgraph,Set.mem_setOf_eq]
    calc
      _ = (∑ i : Fin 6, if s(u,v) ∈ (walk i).edges then (1 : ℝ) else 0) / 2 := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i _
        split_ifs <;> norm_num
      _ = 1 := by rw [hr]; norm_num

lemma weight_cost : cost weight = 3 := by
  norm_num [cost,weight,pushWeight_sum]

lemma weight_optimal (t : CyclePiece G → ℝ) (ht : IsFractionalPartition G t) :
    cost weight ≤ cost t := by
  have hh := degree_lower G t ht 0
  simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hh
  have hd := degree_zero
  simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hd
  rw [hd] at hh
  rw [weight_cost]
  unfold cost
  norm_num at hh
  linarith

/-- Three of the six incident edges at vertex zero: the direct layer. -/
def ports : Finset V := {1,2,3}
noncomputable def aCount (H : G.Subgraph) : ℕ := (ports.filter (fun v => H.Adj 0 v)).card
def Crosses (H : G.Subgraph) : Prop := aCount H = 1

lemma aCount_le_degree (H : G.Subgraph) : aCount H ≤ H.spanningCoe.degree 0 := by
  rw [← card_neighborFinset_eq_degree]
  apply Finset.card_le_card
  intro v hv
  rw [mem_neighborFinset]
  exact (Finset.mem_filter.mp hv).2

lemma cycle_degree_le_two (H : G.Subgraph) (hr : H.coe.IsRegularOfDegree 2) :
    H.spanningCoe.degree 0 ≤ 2 := by
  rw [Subgraph.degree_spanningCoe]
  by_cases hv : (0 : V) ∈ H.verts
  · have hh := hr ⟨0,hv⟩
    rw [Subgraph.coe_degree] at hh
    simp only [Subgraph.degree,← Nat.card_eq_fintype_card] at hh ⊢
    exact hh.le
  · rw [Subgraph.degree_of_notMem_verts hv]
    omega

lemma cycle_aCount_even_of_not_crosses (H : G.Subgraph)
    (hr : H.coe.IsRegularOfDegree 2) (hn : ¬ Crosses H) : Even (aCount H) := by
  have hb := (aCount_le_degree H).trans (cycle_degree_le_two H hr)
  change aCount H ≠ 1 at hn
  have hh : aCount H = 0 ∨ aCount H = 2 := by omega
  rcases hh with h | h <;> rw [h] <;> decide

lemma edge_coverage_nat (D : Finset G.Subgraph) (hd : IsDecomposition G D)
    (e : Sym2 V) (he : e ∈ G.edgeSet) :
    (∑ H ∈ D, if e ∈ H.edgeSet then (1 : ℕ) else 0) = 1 := by
  obtain ⟨H,hH,heH⟩ := Set.mem_iUnion₂.mp (hd.2.symm ▸ he)
  rw [Finset.sum_eq_single H]
  · exact if_pos heH
  · intro K hK hne
    exact if_neg (fun heK => Set.disjoint_left.mp (hd.1 hK hH hne) heK heH)
  · simp [hH]

lemma decomposition_aCount (D : Finset G.Subgraph) (hd : IsDecomposition G D) :
    (∑ H ∈ D, aCount H) = 3 := by
  simp only [aCount,Finset.card_filter]
  rw [Finset.sum_comm]
  have hp : ∀ v ∈ ports, G.Adj 0 v := by decide
  calc
    _ = ∑ v ∈ ports, (1 : ℕ) := by
      apply Finset.sum_congr rfl
      intro v hv
      exact edge_coverage_nat D hd s(0,v) (hp v hv)
    _ = 3 := by decide

/-- An odd set of three ports forces a crossing pair in EVERY integral
cycle decomposition, not only in the displayed optimum. -/
lemma every_decomposition_crosses (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D) : ∃ H ∈ D, Crosses H := by
  by_contra hn
  push_neg at hn
  have he : Even (∑ H ∈ D, aCount H) :=
    Finset.even_sum _ (fun H hH => cycle_aCount_even_of_not_crosses H (hc H hH).2 (hn H hH))
  rw [decomposition_aCount D hd] at he
  norm_num at he

lemma family_not_crosses (i : Fin 6) : ¬ Crosses (C i).val := by
  unfold Crosses aCount C
  simp only [Walk.adj_toSubgraph_iff_mem_edges]
  revert i
  decide

lemma weight_zero_on_crosses (H : CyclePiece G) (hH : Crosses H.val) : weight H = 0 := by
  unfold weight pushWeight
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : C i = H
  · exact (family_not_crosses i (by simpa only [hi] using hH)).elim
  · exact if_neg hi

noncomputable def crossMass (t : CyclePiece G → ℝ) : ℝ :=
  ∑ H, if Crosses H.val then t H else 0

lemma weight_crossMass : crossMass weight = 0 := by
  apply Finset.sum_eq_zero
  intro H _
  by_cases hH : Crosses H.val
  · simp only [if_pos hH,weight_zero_on_crosses H hH]
  · exact if_neg hH

/-- Exact zero crossing mass in an OPTIMAL fractional partition, despite the
odd-set requirement for every integral partition. No rounding bound follows. -/
theorem optimal_fractional_local_obstruction :
    IsFractionalPartition G weight ∧ cost weight = 3 ∧
    (∀ t, IsFractionalPartition G t → cost weight ≤ cost t) ∧
    crossMass weight = 0 ∧
    ∀ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) →
      IsDecomposition G D → ∃ H ∈ D, Crosses H :=
  ⟨weight_fractional,weight_cost,weight_optimal,weight_crossMass,every_decomposition_crosses⟩

/-- The separating odd-set inequality also excludes ANY finite convex
mixture of genuine integral partitions, not just minimum partitions. -/
theorem not_convex_mixture {I : Type*} [Fintype I]
    (D : I → Finset G.Subgraph) (p : I → ℝ)
    (hc : ∀ i, ∀ H ∈ D i, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : ∀ i, IsDecomposition G (D i)) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) :
    ¬ ∀ H : CyclePiece G,
      weight H = ∑ i, if H.val ∈ D i then p i else 0 := by
  intro hrep
  have hpos : ∃ i, 0 < p i := by
    by_contra! hn
    have hz : ∀ i, p i = 0 := fun i => le_antisymm (hn i) (hp i)
    simp [hz] at hs
  obtain ⟨i,hi⟩ := hpos
  obtain ⟨H,hH,hcross⟩ := every_decomposition_crosses (D i) (hc i) (hd i)
  let J : CyclePiece G := ⟨H,(hc i H hH).1,by
    simpa only [IsRegularOfDegree,← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using (hc i H hH).2⟩
  have hz : weight J = 0 := weight_zero_on_crosses J hcross
  have hle : p i ≤ ∑ j, if J.val ∈ D j then p j else 0 := by
    have hh := Finset.single_le_sum (s := Finset.univ)
      (f := fun j => if J.val ∈ D j then p j else 0)
      (fun j _ => by dsimp only; split_ifs; exact hp j; exact le_rfl)
      (Finset.mem_univ i)
    simpa only [J,if_pos hH] using hh
  rw [← hrep J,hz] at hle
  linarith

/-- This obstruction does not require an integrality gap in the optimum:
the same graph also has an integral partition with three cycles. -/
def mixedWalk : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 4) <|
  .cons (by decide : G.Adj 4 1) <|
  .cons (by decide : G.Adj 1 3) <|
  .cons (by decide : G.Adj 3 9) <|
  .cons (by decide : G.Adj 9 2) <|
  .cons (by decide : G.Adj 2 0) .nil
lemma mixedWalk_cycle : mixedWalk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [mixedWalk],by decide⟩
def integralWalk : Fin 3 → G.Walk 0 0 := ![w0,mixedWalk,w5]
lemma integralWalk_cycle (i : Fin 3) : (integralWalk i).IsCycle := by
  fin_cases i
  · exact w0_cycle
  · exact mixedWalk_cycle
  · exact w5_cycle
lemma integralWalk_disjoint (i j : Fin 3) (hij : i ≠ j) :
    List.Disjoint (integralWalk i).edges (integralWalk j).edges := by
  have hh : ∀ i j : Fin 3, i ≠ j →
      Disjoint (integralWalk i).edges.toFinset (integralWalk j).edges.toFinset := by decide
  intro e he hf
  exact Finset.disjoint_left.mp (hh i j hij)
    (List.mem_toFinset.mpr he) (List.mem_toFinset.mpr hf)
lemma integralWalk_cover (u v : V) :
    G.Adj u v ↔ ∃ i : Fin 3, s(u,v) ∈ (integralWalk i).edges := by
  revert u v; decide

lemma integral_lower (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D) : 3 ≤ D.card := by
  have hh := cycle_decomposition_vertex_count G D (fun H hH => ⟨(hc H hH).1,by
    simpa only [IsRegularOfDegree,← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using (hc H hH).2⟩) hd 0
  have hb := Finset.card_filter_le (s := D) (p := fun H => (0 : V) ∈ H.verts)
  have hz := degree_zero
  simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hh hz
  omega

lemma exists_three_cycle_partition : ∃ D : Finset G.Subgraph,
    (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
    IsDecomposition G D ∧ D.card = 3 := by
  obtain ⟨D,hc,hd,hb⟩ := upper_of_walk_family G (fun i : Fin 3 => ⟨0,integralWalk i⟩)
    integralWalk_cycle integralWalk_disjoint integralWalk_cover
  have hc' : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2 := by
    simpa only [IsRegularOfDegree,← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using hc
  have hl := integral_lower D hc' hd
  refine ⟨D,hc',hd,?_⟩
  simpa only [Fintype.card_fin] using le_antisymm hb hl

lemma optimum_eq_three : optimum G = 3 := by
  obtain ⟨t,ht,he⟩ := optimum_attained G (by
    intro v
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using G_even v)
  have hl := weight_optimal t ht
  rw [weight_cost,he] at hl
  exact le_antisymm (by simpa only [weight_cost] using optimum_le_cost weight_fractional) hl

end Erdos184.K4TransitionObstruction
