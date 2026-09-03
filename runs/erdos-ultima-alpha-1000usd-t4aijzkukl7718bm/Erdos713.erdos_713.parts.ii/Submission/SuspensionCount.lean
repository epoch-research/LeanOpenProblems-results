import FormalConjecturesUtil
import Submission.SuspensionGraph

/-! Counting length-four closed walks for bipartite suspensions. -/
open Filter SimpleGraph Asymptotics Finset
namespace Erdos713Suspension
open Erdos713ConeFan
set_option maxHeartbeats 2000000

noncomputable def corners {V : Type*} [Fintype V] (G : SimpleGraph V) (u v : V) : Finset (V × V) := by
  classical
  exact (G.neighborFinset u ×ˢ G.neighborFinset v).filter (fun p => G.Adj p.1 p.2)

lemma mem_corners {V : Type*} [Fintype V] (G : SimpleGraph V) (u v x y : V) :
    (x,y) ∈ corners G u v ↔ G.Adj u x ∧ G.Adj v y ∧ G.Adj x y := by
  classical
  simp only [corners, mem_filter, mem_product, mem_neighborFinset, and_assoc]

noncomputable def localCount {V : Type*} [Fintype V] (G : SimpleGraph V) (u v : V) : ℕ :=
  (corners G u v).card

def Closed4 {V : Type*} (G : SimpleGraph V) (w u v z : V) : Prop :=
  G.Adj w u ∧ G.Adj w v ∧ G.Adj u z ∧ G.Adj v z

lemma quadCount_rotate {V : Type*} [Fintype V] (P : V → V → V → V → Prop) :
    quadCount (fun w u v z => P w v z u) = quadCount P := by
  calc
    _ = quadCount (fun w u v z => P w u z v) := quadCount_swap_uv _
    _ = _ := quadCount_swap_vz _

lemma closed4_count {V : Type*} [Fintype V] (G : SimpleGraph V) :
    quadCount (Closed4 G) = ∑ p : V × V, Nat.card (G.commonNeighbors p.1 p.2)^2 := by
  classical
  have hc (w u : V) : (∑ v : V, if G.Adj w v ∧ G.Adj u v then 1 else 0 : ℕ) =
      Nat.card (G.commonNeighbors w u) := by
    have hs : (univ.filter (fun v => G.Adj w v ∧ G.Adj u v)) =
        (G.commonNeighbors w u).toFinset := by ext v; simp [mem_commonNeighbors]
    rw [sum_boole, Nat.cast_id, hs, Set.toFinset_card, Fintype.card_eq_nat_card]
  rw [← quadCount_rotate]
  unfold quadCount
  have hbool (w u v z : V) [Decidable (Closed4 G w v z u)] :
      (if Closed4 G w v z u then 1 else 0 : ℕ) =
        (if G.Adj w v ∧ G.Adj u v then 1 else 0) *
        (if G.Adj w z ∧ G.Adj u z then 1 else 0) := by
    unfold Closed4
    by_cases h1 : G.Adj w v <;> by_cases h2 : G.Adj w z <;>
      by_cases h3 : G.Adj u v <;> by_cases h4 : G.Adj u z <;>
      simp [h1,h2,h3,h4,G.adj_comm]
  simp only [hbool, ← mul_sum, ← sum_mul, hc, ← pow_two, Fintype.sum_prod_type]

open scoped Classical in
lemma localCount_sum {V : Type*} [Fintype V] (G : SimpleGraph V) (u v : V) :
    localCount G u v = ∑ x : V, ∑ y : V,
      if G.Adj u x ∧ G.Adj v y ∧ G.Adj x y then 1 else 0 := by
  classical
  unfold localCount corners
  rw [card_eq_sum_ones, sum_filter, sum_product]
  simp only [neighborFinset_eq_filter, sum_filter]
  apply sum_congr rfl; intro x _
  by_cases h1 : G.Adj u x
  · simp only [h1, true_and, if_true]
    apply sum_congr rfl; intro y _
    by_cases h2 : G.Adj v y <;> by_cases h3 : G.Adj x y <;> simp [h2,h3]
  · simp [h1]

open scoped Classical in
lemma closed4_sum_local {V : Type*} [Fintype V] (G : SimpleGraph V) :
    quadCount (Closed4 G) = ∑ u : V, ∑ v : V,
      if G.Adj u v then localCount G u v else 0 := by
  classical
  have hbool (w u v z : V) [Decidable (Closed4 G w u v z)] :
      (if Closed4 G w u v z then 1 else 0 : ℕ) =
      if G.Adj w u then (if G.Adj w v ∧ G.Adj u z ∧ G.Adj v z then 1 else 0) else 0 := by
    unfold Closed4
    by_cases h1 : G.Adj w u <;> by_cases h2 : G.Adj w v <;>
      by_cases h3 : G.Adj u z <;> by_cases h4 : G.Adj v z <;> simp [h1,h2,h3,h4]
  unfold quadCount
  simp only [hbool, sum_ite_irrel, sum_const_zero, ← localCount_sum]


lemma localCount_le {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (u v : V) : localCount G u v ≤
      2 * Nat.card ((G.induce (localSet G u v)).edgeSet) + G.degree u + G.degree v := by
  classical
  let T := (corners G u v).filter (fun p => p.1 ≠ v ∧ p.2 ≠ u)
  have hT (p : T) : p.val.1 ∈ localSet G u v ∧ p.val.2 ∈ localSet G u v := by
    have hp := mem_filter.mp p.prop
    have hc := (mem_corners G u v p.val.1 p.val.2).mp hp.1
    exact ⟨⟨hc.1.ne.symm,hp.2.1,Or.inl hc.1⟩,
      hp.2.2,hc.2.1.ne.symm,Or.inr hc.2.1⟩
  let f : T → (G.induce (localSet G u v)).Dart := fun p =>
    ⟨(⟨p.val.1,(hT p).1⟩,⟨p.val.2,(hT p).2⟩),
      ((mem_corners G u v p.val.1 p.val.2).mp (mem_filter.mp p.prop).1).2.2⟩
  have hf : Function.Injective f := by
    intro p q he
    apply Subtype.ext
    exact Prod.ext (congrArg (fun d => d.fst.val) he) (congrArg (fun d => d.snd.val) he)
  have hTc : T.card ≤ 2 * Nat.card ((G.induce (localSet G u v)).edgeSet) := by
    have hh := Fintype.card_le_of_injective f hf
    have hD := (G.induce (localSet G u v)).dart_card_eq_twice_card_edges
    simp only [edgeFinset_card, Fintype.card_eq_nat_card] at hh hD
    rw [Nat.card_eq_finsetCard, hD] at hh
    exact hh
  have hsub : corners G u v ⊆
      T ∪ (G.neighborFinset u ×ˢ {u}) ∪ ({v} ×ˢ G.neighborFinset v) := by
    rintro ⟨x,y⟩ hp
    have hh := (mem_corners G u v x y).mp hp
    by_cases hx : x = v
    · exact mem_union_right _ (by simp [hx, hh.2.1])
    by_cases hy : y = u
    · exact mem_union_left _ (mem_union_right _ (by simp [hy, hh.1]))
    exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hp,hx,hy⟩))
  have hh := (card_le_card hsub).trans ((card_union_le _ _).trans
    (Nat.add_le_add_right (card_union_le _ _) _))
  simp only [card_product, card_singleton, mul_one, one_mul,
    card_neighborFinset_eq_degree] at hh
  exact hh.trans (by omega)

lemma closed4_lower {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : 0 < Fintype.card V) {d : ℝ} (hd : 0 ≤ d)
    (hdeg : ∀ v, d ≤ (G.degree v : ℝ)) : d^4 ≤ (quadCount (Closed4 G) : ℝ) := by
  classical
  have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
  have hsum : (∑ p : V × V, (Nat.card (G.commonNeighbors p.1 p.2) : ℝ)) =
      ∑ v : V, (G.degree v : ℝ)^2 := by
    have hh := Erdos713DRC.sum_common_eq_sum_degree_sq G
    simp only [Fintype.card_eq_nat_card] at hh
    exact_mod_cast hh
  have hlow : (Fintype.card V : ℝ)*d^2 ≤
      ∑ p : V × V, (Nat.card (G.commonNeighbors p.1 p.2) : ℝ) := by
    rw [hsum]
    simpa only [sum_const, card_univ, nsmul_eq_mul] using
      (sum_le_sum (s := (univ : Finset V)) (fun v _ => pow_le_pow_left₀ hd (hdeg v) 2))
  have hcs := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (V × V)))
    (f := fun p => (Nat.card (G.commonNeighbors p.1 p.2) : ℝ))
  have hcount : (quadCount (Closed4 G) : ℝ) =
      ∑ p : V × V, (Nat.card (G.commonNeighbors p.1 p.2) : ℝ)^2 := by
    exact_mod_cast closed4_count G
  simp only [card_univ, Fintype.card_prod, Nat.cast_mul, ← hcount] at hcs
  apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hnR)).mp
  calc
    (Fintype.card V : ℝ)^2 * d^4 = ((Fintype.card V : ℝ)*d^2)^2 := by ring
    _ ≤ (∑ p : V × V, (Nat.card (G.commonNeighbors p.1 p.2) : ℝ))^2 :=
      pow_le_pow_left₀ (by positivity) hlow 2
    _ ≤ _ := by simpa only [pow_two] using hcs

lemma closed4_upper {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : ℕ) (hD : ∀ v, G.degree v ≤ D) (L : ℝ) (hL : 0 ≤ L)
    (hlocal : ∀ u v, G.Adj u v → (localCount G u v : ℝ) ≤ L) :
    (quadCount (Closed4 G) : ℝ) ≤ (Fintype.card V : ℝ)*D*L := by
  classical
  have hrow (u : V) : (∑ v : V, if G.Adj u v then L else 0) = (G.degree u : ℝ)*L := by
    rw [← sum_filter]
    rw [← G.neighborFinset_eq_filter]
    simp only [sum_const, card_neighborFinset_eq_degree, nsmul_eq_mul]
  have hcount : (quadCount (Closed4 G) : ℝ) =
      ∑ u : V, ∑ v : V, if G.Adj u v then (localCount G u v : ℝ) else 0 := by
    rw [closed4_sum_local]
    push_cast
    rfl
  rw [hcount]
  calc
    _ ≤ ∑ u : V, ∑ v : V, if G.Adj u v then L else 0 := by
      apply sum_le_sum; intro u _
      apply sum_le_sum; intro v _
      split_ifs with h
      · exact hlocal u v h
      · rfl
    _ = (∑ u : V, (G.degree u : ℝ))*L := by simp only [hrow, sum_mul]
    _ ≤ ((Fintype.card V : ℝ)*D)*L := by
      apply mul_le_mul_of_nonneg_right _ hL
      simpa only [sum_const, card_univ, nsmul_eq_mul] using
        (sum_le_sum (s := (univ : Finset V)) (fun v _ => (Nat.cast_le.mpr (hD v) : (G.degree v : ℝ) ≤ D)))

end Erdos713Suspension
