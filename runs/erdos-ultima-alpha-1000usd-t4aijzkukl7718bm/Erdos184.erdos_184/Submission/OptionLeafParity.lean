import Submission.OptionPathProjection

/-! A one-leaf extension changes the number of even-degree vertices by one.
The degree statements use instance-independent neighbor-set cardinalities. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.OddPaths
set_option maxHeartbeats 1200000
variable {V : Type*} [Fintype V] (G : SimpleGraph V) (v : V)

noncomputable def optionLeaf : SimpleGraph (Option V) :=
  optionBase G ⊔ SimpleGraph.edge none (some v)

@[simp] lemma optionLeaf_none (x : Option V) :
    (optionLeaf G v).Adj none x ↔ x = some v := by
  cases x with
  | none => simp
  | some x => simp [optionLeaf,optionBase_adj,SimpleGraph.edge_adj,eq_comm]

@[simp] lemma optionLeaf_some_some (a b : V) :
    (optionLeaf G v).Adj (some a) (some b) ↔ G.Adj a b := by
  simp [optionLeaf,optionBase_adj,SimpleGraph.edge_adj]

lemma optionLeaf_delete : (optionLeaf G v).deleteEdges {s(none,some v)} = optionBase G := by
  ext a b
  cases a <;> cases b <;>
    simp [SimpleGraph.deleteEdges_adj,optionLeaf,optionBase_adj,SimpleGraph.edge_adj,
      Sym2.eq_iff]

lemma degree_nat_sum (G : SimpleGraph V) (v : V) :
    Nat.card (G.neighborSet v) = ∑ x : V, if G.Adj v x then 1 else 0 := by
  rw [Finset.sum_boole]
  rw [Nat.card_eq_fintype_card]
  change Fintype.card (G.neighborSet v) = _
  simp only [Fintype.card_ofFinset]
  congr 1

lemma optionLeaf_degree_none : Nat.card ((optionLeaf G v).neighborSet none) = 1 := by
  have h : (optionLeaf G v).neighborSet none = {some v} := by
    ext x
    exact optionLeaf_none G v x
  rw [h]
  simp

lemma optionLeaf_degree_some (x : V) :
    Nat.card ((optionLeaf G v).neighborSet (some x)) =
      Nat.card (G.neighborSet x) + if x = v then 1 else 0 := by
  rw [degree_nat_sum,Fintype.sum_option]
  have hn : (optionLeaf G v).Adj (some x) none ↔ x = v := by
    rw [adj_comm,optionLeaf_none]
    exact Option.some.injEq _ _ |> Iff.of_eq
  simp only [hn,optionLeaf_some_some,← degree_nat_sum]
  omega

noncomputable def evenCount (G : SimpleGraph V) : ℕ :=
  ∑ x : V, if Even (Nat.card (G.neighborSet x)) then 1 else 0

noncomputable def endpointCap (G : SimpleGraph V) (v : V) : ℕ :=
  if Even (Nat.card (G.neighborSet v)) then 2 else 1

lemma optionLeaf_evenCount (hv : Even (Nat.card (G.neighborSet v))) :
    evenCount (optionLeaf G v) + 1 = evenCount G := by
  have hp (x : V) :
      (if Even (Nat.card ((optionLeaf G v).neighborSet (some x))) then 1 else 0) +
        (if x = v then 1 else 0) =
      if Even (Nat.card (G.neighborSet x)) then 1 else 0 := by
    rw [optionLeaf_degree_some]
    by_cases hx : x = v
    · subst x
      have hn : ¬ Even (Nat.card (G.neighborSet v) + 1) := by
        rw [Nat.even_iff] at hv ⊢
        omega
      simp only [ite_true,eq_self]
      rw [if_neg hn,if_pos hv]
    · simp [hx]
  have hs := Finset.sum_congr (s₁ := Finset.univ) rfl (fun x _ => hp x)
  rw [Finset.sum_add_distrib] at hs
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true] at hs
  simpa only [evenCount,Fintype.sum_option,optionLeaf_degree_none,
    show ¬ Even (1 : ℕ) by decide,ite_false,zero_add] using hs

lemma odd_of_evenCount_zero (hz : evenCount G = 0) (x : V) :
    Odd (Nat.card (G.neighborSet x)) := by
  apply Nat.not_even_iff_odd.mp
  intro he
  have h := Finset.single_le_sum
    (s := Finset.univ) (f := fun y : V => if Even (Nat.card (G.neighborSet y)) then 1 else 0)
    (fun y _ => Nat.zero_le _) (Finset.mem_univ x)
  change _ ≤ evenCount G at h
  simp only [he,ite_true,hz] at h
  omega

lemma optionBase_edge_iff (e : Sym2 V) :
    Sym2.map some e ∈ (optionBase G).edgeSet ↔ e ∈ G.edgeSet := by
  induction e using Sym2.ind with | h a b =>
    change (optionBase G).Adj (some a) (some b) ↔ G.Adj a b
    simp [optionBase_adj]

end Erdos184Work.OddPaths
#print axioms Erdos184Work.OddPaths.optionLeaf_evenCount
