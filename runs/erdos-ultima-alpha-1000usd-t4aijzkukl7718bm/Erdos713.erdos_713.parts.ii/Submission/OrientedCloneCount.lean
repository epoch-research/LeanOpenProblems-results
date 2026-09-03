import FormalConjecturesUtil
import Submission.OrientedCloneC8

/-! Exact edge and vertex costs of an oriented batch of partial clones. -/
open SimpleGraph Finset
open scoped Classical
namespace Erdos713OrientedCloneCount
open Erdos713OrientedCloneC8
set_option maxHeartbeats 2000000
variable {V W : Type*}

lemma graph_edge_card [Fintype V] [Fintype W] (G : SimpleGraph V) (P : W → V → Prop) :
    Nat.card (graph G P).edgeSet = Nat.card G.edgeSet + Nat.card {p : W × V // P p.1 p.2} := by
  classical
  have h := (graph G P).two_mul_card_edgeFinset
  have hG := G.two_mul_card_edgeFinset
  simp only [card_filter,Fintype.sum_prod_type,Fintype.sum_sum_type,graph,
    sum_add_distrib,edgeFinset_card,
    ← Nat.card_eq_fintype_card] at h hG
  rw [sum_comm (f := fun u v => if P v u then 1 else 0)] at h
  have hP : (∑ u : W, ∑ v : V, if P u v then 1 else 0) =
      Nat.card {p : W × V // P p.1 p.2} := by
    simp only [Nat.card_eq_fintype_card,Fintype.card_subtype,card_filter,Fintype.sum_prod_type]
  rw [hP,← hG] at h
  change 2*Nat.card (graph G P).edgeSet = _ at h
  simp only [if_false,sum_const_zero,add_zero] at h
  omega

variable [LinearOrder V]

def selected (G : SimpleGraph V) (S : Finset V) : SimpleGraph (V ⊕ S) :=
  graph G (fun u v => G.Adj u.val v ∧ (v ∉ S ∨ u.val < v))

lemma selected_free {G : SimpleGraph V}
    (hG : ∀ T : Finset V, T.card ≤ 8 → (G.induce (T : Set V)).IsAcyclic) (S : Finset V) :
    (cycleGraph 8).Free (selected G S) := by
  let P : V → V → Prop := fun u v => u ∈ S ∧ G.Adj u v ∧ (v ∉ S ∨ u < v)
  have hP (u v : V) (h : P u v) : G.Adj u v := h.2.1
  have ha (u v : V) (h : P u v) (h' : P v u) : False := by
    have huv := h.2.2.resolve_left (not_not.mpr h'.1)
    have hvu := h'.2.2.resolve_left (not_not.mpr h.1)
    exact (lt_asymm huv hvu)
  have hc : selected G S ⊑ graph G P := by
    refine ⟨⟨⟨Sum.map id Subtype.val,?_⟩,?_⟩⟩
    · rintro (u|u) (v|v) h
      · exact h
      · exact ⟨v.property,h⟩
      · exact ⟨u.property,h⟩
      · exact h.elim
    · exact Sum.map_injective.mpr ⟨Function.injective_id,Subtype.val_injective⟩
  exact fun h => free_of_small_acyclic hG hP ha (h.trans hc)

lemma sum_on_subset [Fintype V] (S : Finset V) (f : V → ℕ) :
    (∑ u : S, f u.val) = ∑ u : V, if u ∈ S then f u else 0 := by
  classical
  rw [sum_coe_sort]
  simp only [← sum_filter,filter_mem_eq_inter,univ_inter]

lemma induced_twice_edges [Fintype V] (G : SimpleGraph V) (S : Finset V) :
    2*Nat.card (G.induce (S : Set V)).edgeSet =
      ∑ u : V, ∑ v : V, if u ∈ S ∧ v ∈ S ∧ G.Adj u v then 1 else 0 := by
  classical
  letI : Fintype {v // v ∈ (S : Set V)} := inferInstanceAs (Fintype S)
  have h := (G.induce (S : Set V)).two_mul_card_edgeFinset
  simp only [card_filter,Fintype.sum_prod_type,induce_adj,edgeFinset_card,← Nat.card_eq_fintype_card] at h
  change 2*Nat.card (G.induce (S : Set V)).edgeSet = _ at h
  rw [h]
  have hi (u : S) : (∑ v : S, if G.Adj u.val v.val then 1 else 0) =
      ∑ v : V, if v ∈ S then (if G.Adj u.val v then 1 else 0) else 0 :=
    sum_on_subset S (fun v => if G.Adj u.val v then 1 else 0)
  change (∑ u : S, ∑ v : S, if G.Adj u.val v.val then 1 else 0) = _
  conv_lhs => arg 2; ext u; rw [hi u]
  rw [sum_on_subset S (fun u => ∑ v : V, if v ∈ S then (if G.Adj u v then 1 else 0) else 0)]
  apply sum_congr rfl
  intro u _
  by_cases hu : u ∈ S
  · simp only [hu,true_and]
    apply sum_congr rfl
    intro v _
    by_cases hv : v ∈ S <;> simp [hv]
  · simp [hu]

/-- The added edges are in bijection with the base edges touched by S:
exactly one new edge is kept per touched edge. -/
theorem selected_edge_card [Fintype V] (G : SimpleGraph V) (S : Finset V) :
    Nat.card (selected G S).edgeSet + Nat.card (G.induce ((Sᶜ : Finset V) : Set V)).edgeSet =
      2*Nat.card G.edgeSet := by
  classical
  let P : V → V → Prop := fun u v => u ∈ S ∧ G.Adj u v ∧ (v ∉ S ∨ u < v)
  have hG := G.two_mul_card_edgeFinset
  simp only [card_filter,Fintype.sum_prod_type,edgeFinset_card,← Nat.card_eq_fintype_card] at hG
  have hsplit (u v : V) :
      (if G.Adj u v then 1 else 0 : ℕ) =
        (if P u v then 1 else 0)+(if P v u then 1 else 0)+
        (if u ∈ Sᶜ ∧ v ∈ Sᶜ ∧ G.Adj u v then 1 else 0) := by
    by_cases hadj : G.Adj u v
    · have hneq := hadj.ne
      have hadj' := hadj.symm
      rcases lt_or_gt_of_ne hneq with hlt|hgt
      · by_cases hu : u ∈ S <;> by_cases hv : v ∈ S <;>
          simp [P,hu,hv,hadj,hadj',hlt,not_lt_of_ge hlt.le]
      · by_cases hu : u ∈ S <;> by_cases hv : v ∈ S <;>
          simp [P,hu,hv,hadj,hadj',hgt,not_lt_of_ge hgt.le]
    · have hadj' : ¬ G.Adj v u := fun h => hadj h.symm
      simp [P,hadj,hadj']
  simp_rw [hsplit,sum_add_distrib] at hG
  rw [sum_comm (f := fun u v => if P v u then 1 else 0),
    ← induced_twice_edges G Sᶜ] at hG
  have he := graph_edge_card G (fun u : S => fun v => G.Adj u.val v ∧ (v ∉ S ∨ u.val < v))
  change Nat.card (selected G S).edgeSet = _ at he
  have hP : Nat.card {p : S × V // G.Adj p.1.val p.2 ∧ (p.2 ∉ S ∨ p.1.val < p.2)} =
      ∑ u : V, ∑ v : V, if P u v then 1 else 0 := by
    simp only [Nat.card_eq_fintype_card,Fintype.card_subtype,card_filter,Fintype.sum_prod_type]
    rw [sum_on_subset S (fun u => ∑ v : V, if G.Adj u v ∧ (v ∉ S ∨ u < v) then 1 else 0)]
    apply sum_congr rfl
    intro u _
    by_cases hu : u ∈ S <;> simp [P,hu]
  rw [hP] at he
  omega

/-- A finite extremal comparison obtained without any asymptotic assumption. -/
theorem extremal_comparison [Fintype V] (G : SimpleGraph V)
    (hG : ∀ T : Finset V, T.card ≤ 8 → (G.induce (T : Set V)).IsAcyclic) (S : Finset V) :
    2*Nat.card G.edgeSet ≤ extremalNumber (Fintype.card V+S.card) (cycleGraph 8) +
      Nat.card (G.induce ((Sᶜ : Finset V) : Set V)).edgeSet := by
  classical
  have h := card_edgeFinset_le_extremalNumber (selected_free hG S)
  have h' : Nat.card (selected G S).edgeSet ≤
      extremalNumber (Fintype.card V+S.card) (cycleGraph 8) := by
    simpa only [edgeFinset_card,Nat.card_eq_fintype_card,Fintype.card_sum,Fintype.card_coe] using h
  rw [← selected_edge_card G S]
  exact Nat.add_le_add_right h' _

#print axioms graph_edge_card
#print axioms selected_free
#print axioms selected_edge_card
#print axioms extremal_comparison
end Erdos713OrientedCloneCount
