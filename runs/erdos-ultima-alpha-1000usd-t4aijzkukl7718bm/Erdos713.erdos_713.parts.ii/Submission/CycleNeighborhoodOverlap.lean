import FormalConjecturesUtil
import Submission.CompactSymmRootsAudit

/-! Neighbourhood path exclusion controls codegrees on actual host edges.
The resulting exceptional-edge estimate is stronger than an o(n^2) pair
estimate, but does not by itself determine an extremal exponent. -/
open SimpleGraph Finset Filter
open scoped Classical
namespace Erdos713CycleNeighborhoodOverlap
variable {V : Type*}
set_option maxHeartbeats 2000000

lemma path_seven_tree : (pathGraph 7).IsTree := by
  letI : DecidableRel (pathGraph 7).Adj := fun u v =>
    decidable_of_iff (u.val+1=v.val ∨ v.val+1=u.val) pathGraph_adj.symm
  apply isTree_iff_connected_and_card.mpr
  refine ⟨pathGraph_connected 6,?_⟩
  rw [Nat.card_eq_fintype_card,← edgeFinset_card,Nat.card_eq_fintype_card,Fintype.card_fin]
  decide

lemma cycle_eight_of_neighborhood_path (G : SimpleGraph V) (v : V)
    (f : (pathGraph 7).Copy (G.induce (G.neighborSet v))) : cycleGraph 8 ⊑ G := by
  let g : Fin 8 → V := Fin.cons v (fun i => (f i).val)
  have hStep (i : Fin 8) : G.Adj (g i) (g (i+1)) := by
    fin_cases i
    · change G.Adj v (f 0).val
      exact (f 0).property
    · change G.Adj (f 0).val (f 1).val
      exact f.toHom.map_rel' (by simp [pathGraph_adj])
    · change G.Adj (f 1).val (f 2).val
      exact f.toHom.map_rel' (by simp [pathGraph_adj])
    · change G.Adj (f 2).val (f 3).val
      exact f.toHom.map_rel' (by simp [pathGraph_adj])
    · change G.Adj (f 3).val (f 4).val
      exact f.toHom.map_rel' (by simp [pathGraph_adj])
    · change G.Adj (f 4).val (f 5).val
      exact f.toHom.map_rel' (by simp [pathGraph_adj])
    · change G.Adj (f 5).val (f 6).val
      exact f.toHom.map_rel' (by simp [pathGraph_adj])
    · change G.Adj (f 6).val v
      exact (f 6).property.symm
  refine ⟨⟨⟨g,?_⟩,?_⟩⟩
  · intro u w huw
    rcases cycleGraph_adj.mp huw with h | h
    · rw [sub_eq_iff_eq_add'.mp h]
      exact (hStep w).symm
    · rw [sub_eq_iff_eq_add'.mp h]
      exact hStep u
  · apply Fin.cons_injective_of_injective
    · rintro ⟨i,hi⟩
      exact (f i).property.ne hi.symm
    · exact Subtype.val_injective.comp f.injective

lemma neighborhood_edge_bound [Fintype V] (G : SimpleGraph V)
    (hf : (cycleGraph 8).Free G) (v : V) :
    Nat.card (G.induce (G.neighborSet v)).edgeSet ≤ 7*Nat.card (G.neighborSet v) := by
  classical
  have hb := Erdos713Forest.free_tree_edge_bound (pathGraph 7) path_seven_tree
    (G.induce (G.neighborSet v)) (by
      rintro ⟨f⟩
      exact hf (cycle_eight_of_neighborhood_path G v f))
  simpa only [edgeFinset_card,Nat.card_eq_fintype_card,Fintype.card_fin] using hb

lemma neighborhood_degree [Fintype V] (G : SimpleGraph V) (v : V)
    (u : G.neighborSet v) :
    Nat.card ((G.induce (G.neighborSet v)).neighborSet u) =
      Nat.card (G.commonNeighbors v u.val) := by
  let e : ((G.induce (G.neighborSet v)).neighborSet u) ≃ G.commonNeighbors v u.val :=
    { toFun := fun z => ⟨z.val.val,z.val.property,z.property⟩
      invFun := fun z => ⟨⟨z.val,z.property.1⟩,z.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact Nat.card_congr e

lemma sum_adjacent_codegrees [Fintype V] (G : SimpleGraph V) :
    (∑ p : V × V, if G.Adj p.1 p.2 then Nat.card (G.commonNeighbors p.1 p.2) else 0) =
      2*∑ v : V, Nat.card (G.induce (G.neighborSet v)).edgeSet := by
  classical
  rw [Fintype.sum_prod_type,mul_sum]
  apply sum_congr rfl
  intro v _
  rw [← sum_filter,← neighborFinset_eq_filter]
  rw [sum_subtype (p := fun x => x ∈ G.neighborSet v) (G.neighborFinset v)
    (fun x => G.mem_neighborFinset v x)]
  dsimp only [Prod.fst,Prod.snd]
  simp_rw [← neighborhood_degree G v]
  simpa only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree,edgeFinset_card] using
    (G.induce (G.neighborSet v)).sum_degrees_eq_twice_card_edges

lemma adjacent_codegree_bound [Fintype V] (G : SimpleGraph V)
    (hf : (cycleGraph 8).Free G) :
    (∑ p : V × V, if G.Adj p.1 p.2 then Nat.card (G.commonNeighbors p.1 p.2) else 0) ≤
      28*Nat.card G.edgeSet := by
  classical
  rw [sum_adjacent_codegrees G]
  have hb := sum_le_sum (s := (univ : Finset V)) (fun v _ => neighborhood_edge_bound G hf v)
  have he : (∑ v : V, Nat.card (G.neighborSet v)) = 2*Nat.card G.edgeSet := by
    simpa only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree,edgeFinset_card] using
      G.sum_degrees_eq_twice_card_edges
  rw [← mul_sum,he] at hb
  omega

open scoped Classical in
noncomputable def badEdges [Fintype V] (G : SimpleGraph V) (t : ℝ) : Finset (V × V) :=
  univ.filter (fun p => G.Adj p.1 p.2 ∧ t < (Nat.card (G.commonNeighbors p.1 p.2) : ℝ))

lemma badEdges_bound [Fintype V] (G : SimpleGraph V)
    (hf : (cycleGraph 8).Free G) (t : ℝ) :
    t*(badEdges G t).card ≤ 28*(Nat.card G.edgeSet : ℝ) := by
  classical
  let w : V × V → ℝ := fun p =>
    if G.Adj p.1 p.2 then (Nat.card (G.commonNeighbors p.1 p.2) : ℝ) else 0
  have hb : (∑ p : V × V, w p) ≤ 28*(Nat.card G.edgeSet : ℝ) := by
    dsimp only [w]
    exact_mod_cast adjacent_codegree_bound G hf
  have hlow : ∀ p ∈ badEdges G t, t ≤ w p := by
    intro p hp
    obtain ⟨ha,ht⟩ := (mem_filter.mp hp).2
    simpa only [w,if_pos ha] using ht.le
  have hs := sum_le_sum hlow
  have hsub := sum_le_univ_sum_of_nonneg (s := badEdges G t) (f := w)
    (fun p => by dsimp [w]; split_ifs <;> positivity)
  simp only [sum_const,nsmul_eq_mul] at hs
  nlinarith only [hs,hsub,hb]

/-- The exception is o(e(G)) uniformly over C8-free graphs. No exactness
or extremal asymptotic is required for this finite local consequence. -/
theorem eventually_few_badEdges {a β ε : ℝ} (ha : 0 < a) (hβ : 0 < β) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      (cycleGraph 8).Free G →
      ((badEdges G (a*(n : ℝ)^β)).card : ℝ) ≤ ε*(Nat.card G.edgeSet : ℝ) := by
  have hgrow : Tendsto (fun n : ℕ => a*(n : ℝ)^β) atTop atTop :=
    ((tendsto_rpow_atTop hβ).comp tendsto_natCast_atTop_atTop).const_mul_atTop ha
  filter_upwards [hgrow.eventually_ge_atTop (28/ε)] with n hn
  intro V instV G hf
  have hb := badEdges_bound G hf (a*(n : ℝ)^β)
  have hprod : (28/ε)*((badEdges G (a*(n : ℝ)^β)).card : ℝ) ≤
      28*(Nat.card G.edgeSet : ℝ) :=
    (mul_le_mul_of_nonneg_right hn (Nat.cast_nonneg _)).trans hb
  have hmul := mul_le_mul_of_nonneg_left hprod hε.le
  have hne := hε.ne'
  field_simp at hmul
  nlinarith only [hmul]

#print axioms adjacent_codegree_bound
#print axioms badEdges_bound
#print axioms eventually_few_badEdges
end Erdos713CycleNeighborhoodOverlap
