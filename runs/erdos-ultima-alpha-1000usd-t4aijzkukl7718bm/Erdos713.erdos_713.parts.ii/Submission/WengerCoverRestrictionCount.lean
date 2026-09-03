import FormalConjecturesUtil
import Submission.WengerCoverRestrictionGeometry
import Submission.WengerCoverCount

/-! Edge restrictions of arbitrary permutation lifts of the linear Wenger graph.
The vertex count includes the full ambient cover, including isolated vertices.
This does not bound arbitrary C8-free graphs or settle Erdős 713. -/
open SimpleGraph Finset
open scoped Classical
namespace Erdos713WengerCoverRestriction
open Erdos713WengerRestriction
open Erdos713ThetaC4Deletion Erdos713ThetaHeavyShadow Erdos713ThetaAnchorBudget
open Erdos713ThetaAnchorPacking
variable {K S : Type*} [Field K] [Fintype K] [Fintype S]
set_option maxHeartbeats 2000000

noncomputable def size (A : (Point K × S) → K → Prop) : ℕ := ∑ p, (row A p).card

noncomputable def pairMass (A : (Point K × S) → K → Prop) (a b : K) : ℕ :=
  ∑ p, if A p a ∧ A p b then 1 else 0

lemma grid_edges (sigma : Point K → K → Equiv.Perm S) (A : (Point K × S) → K → Prop)
    (a b : K) (r : K × K) :
    edges (grid sigma A a b r) = ∑ u : K × S, ∑ v : K,
      if A (pointLift sigma a b r u v) a ∧ A (pointLift sigma a b r u v) b
        then 1 else 0 := by
  simp [edges,Nat.card_eq_fintype_card,Fintype.card_subtype,card_filter,
    Fintype.sum_prod_type,grid,ite_and]

lemma pairMass_grid_sum (sigma : Point K → K → Equiv.Perm S)
    (A : (Point K × S) → K → Prop) (a b : K) (hab : a ≠ b) :
    pairMass A a b = ∑ r : K × K, edges (grid sigma A a b r) := by
  have he := Fintype.sum_equiv (planeEquiv sigma a b hab).symm
    (fun z : (K × K) × ((K × S) × K) =>
      if A (pointLift sigma a b z.1 z.2.1 z.2.2) a ∧
          A (pointLift sigma a b z.1 z.2.1 z.2.2) b then (1 : ℕ) else 0)
    (fun p : Point K × S => if A p a ∧ A p b then (1 : ℕ) else 0)
    (fun _ => rfl)
  rw [pairMass,← he,Fintype.sum_prod_type]
  apply sum_congr rfl
  intro r _
  rw [grid_edges,Fintype.sum_prod_type]

lemma pairMass_bound (sigma : Point K → K → Equiv.Perm S)
    (A : (Point K × S) → K → Prop) (hf : (cycleGraph 8).Free (graph sigma A))
    (a b : K) (hab : a ≠ b) :
    pairMass A a b ≤ (Fintype.card K)^3*Fintype.card S*
      (Nat.sqrt (Fintype.card K*Fintype.card S)+2) := by
  rw [pairMass_grid_sum sigma A a b hab]
  have hh := sum_le_sum (s := (univ : Finset (K × K)))
    (fun r _ => four_free_edges_le_sqrt (grid_four_free sigma A hf a b hab r))
  simp only [Nat.card_eq_fintype_card,sum_const,card_univ,Fintype.card_prod,
    nsmul_eq_mul,Nat.cast_id] at hh
  convert hh using 1
  ring

omit [Field K] in
lemma size_le (A : (Point K × S) → K → Prop) :
    size A ≤ (Fintype.card K)^5*Fintype.card S := by
  have hp (p : Point K × S) : (row A p).card ≤ Fintype.card K :=
    (card_le_card (filter_subset _ _)).trans_eq card_univ
  have hh := sum_le_sum (s := univ) (fun p _ => hp p)
  simp only [sum_const,card_univ,Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,
    nsmul_eq_mul,Nat.cast_id] at hh
  change size A ≤ _ at hh
  convert hh using 1
  ring

lemma degree_square_bound (sigma : Point K → K → Equiv.Perm S)
    (A : (Point K × S) → K → Prop) (hf : (cycleGraph 8).Free (graph sigma A)) :
    (∑ p : Point K × S, (row A p).card^2) ≤
      (Fintype.card K)^5*Fintype.card S*(Nat.sqrt (Fintype.card K*Fintype.card S)+3) := by
  have hid : (∑ p : Point K × S, (row A p).card^2) = size A+
      ∑ ab ∈ (univ : Finset K).offDiag, pairMass A ab.1 ab.2 := by
    have hs := pair_incidence_sum A (univ : Finset (Point K × S))
    have hc (ab : K × K) : (commonRows A univ ab).card = pairMass A ab.1 ab.2 := by
      simp only [commonRows,card_filter,pairMass]
    simp_rw [hc] at hs
    rw [← hs,size,← sum_add_distrib]
    apply sum_congr rfl
    intro p _
    rw [offDiag_card,pow_two]
    have hle := Nat.le_mul_self (row A p).card
    omega
  rw [hid]
  have hb : (∑ ab ∈ (univ : Finset K).offDiag, pairMass A ab.1 ab.2) ≤
      (Fintype.card K)^5*Fintype.card S*(Nat.sqrt (Fintype.card K*Fintype.card S)+2) := by
    have hsum := sum_le_sum (s := (univ : Finset K).offDiag)
      (fun ab hab => pairMass_bound sigma A hf ab.1 ab.2 (mem_offDiag.mp hab).2.2)
    simp only [sum_const,nsmul_eq_mul] at hsum
    have hcard : (univ : Finset K).offDiag.card ≤ (Fintype.card K)^2 := by
      simp only [offDiag_card,card_univ,pow_two]
      exact Nat.sub_le _ _
    have hm := Nat.mul_le_mul_right ((Fintype.card K)^3*Fintype.card S*
      (Nat.sqrt (Fintype.card K*Fintype.card S)+2)) hcard
    have hh := hsum.trans hm
    convert hh using 1
    ring
  have he := size_le A
  nlinarith only [hb,he]

/-- A fourth-power edge bound, with the sheet factor retained explicitly. -/
theorem restriction_bound [Nonempty S] (sigma : Point K → K → Equiv.Perm S)
    (A : (Point K × S) → K → Prop) (hf : (cycleGraph 8).Free (graph sigma A)) :
    (size A)^4 ≤ 16*(Fintype.card K)^19*(Fintype.card S)^5 := by
  let q := Fintype.card K
  let s := Fintype.card S
  have hq : 1 ≤ q := Fintype.card_pos_iff.mpr ⟨0⟩
  have hs : 1 ≤ s := Fintype.card_pos_iff.mpr inferInstance
  have hqs : 1 ≤ q*s := by nlinarith
  have hs1 : 1 ≤ Nat.sqrt (q*s) := Nat.le_sqrt.mpr (by simpa using hqs)
  have hs2 : (Nat.sqrt (q*s))^2 ≤ q*s := by simpa only [pow_two] using Nat.sqrt_le (q*s)
  have hc := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Point K × S)))
    (f := fun p => (row A p).card)
  simp only [card_univ,Fintype.card_prod,Fintype.card_fun,Fintype.card_fin] at hc
  change (size A)^2 ≤ (q^4*s)*(∑ p, (row A p).card^2) at hc
  have hd := degree_square_bound sigma A hf
  change (∑ p, (row A p).card^2) ≤ q^5*s*(Nat.sqrt (q*s)+3) at hd
  have hh := hc.trans (Nat.mul_le_mul_left (q^4*s) hd)
  have hcoef : Nat.sqrt (q*s)+3 ≤ 4*Nat.sqrt (q*s) := by omega
  have he : (size A)^2 ≤ 4*q^9*s^2*Nat.sqrt (q*s) := by
    have hm := Nat.mul_le_mul_left (q^9*s^2) hcoef
    nlinarith only [hh,hm]
  have hsq := Nat.pow_le_pow_left he 2
  have hmul := Nat.mul_le_mul_left (16*q^18*s^4) hs2
  nlinarith only [hsq,hmul]

lemma graph_edges (sigma : Point K → K → Equiv.Perm S)
    (A : (Point K × S) → K → Prop) : Nat.card (graph sigma A).edgeSet = size A := by
  have hh := (graph sigma A).two_mul_card_edgeFinset
  simp only [card_filter] at hh
  rw [Fintype.sum_prod_type] at hh
  simp only [Fintype.sum_sum_type,graph,Erdos713C6.bipGraph,sum_add_distrib,
    edgeFinset_card,← Nat.card_eq_fintype_card] at hh
  have hflip : (∑ l : Point K × S, ∑ p : Point K × S, if Rel sigma A p l then 1 else 0) =
      ∑ p : Point K × S, ∑ l : Point K × S, if Rel sigma A p l then 1 else 0 := sum_comm
  rw [hflip] at hh
  have hrow (p : Point K × S) :
      (∑ l : Point K × S, if Rel sigma A p l then 1 else 0) = (row A p).card := by
    let f : {l : Point K × S // Rel sigma A p l} ≃ {a : K // A p a} :=
      { toFun := fun l => ⟨l.val.1 0,l.property.2⟩
        invFun := fun a => ⟨(lineThrough p.1 a.val,sigma p.1 a.val p.2),⟨rfl,rfl⟩,a.property⟩
        left_inv := fun l => Subtype.ext (Prod.ext l.property.1.1.symm l.property.1.2.symm)
        right_inv := fun _ => rfl }
    have hcard := Fintype.card_congr f
    simpa only [Fintype.card_subtype,card_filter,row] using hcard
  simp_rw [hrow] at hh
  have hh' : 2*Nat.card (graph sigma A).edgeSet = size A+size A := by
    simpa [size,graph,Nat.card_eq_fintype_card,Fintype.card_subtype] using hh
  omega

theorem graph_edge_fourth_bound [Nonempty S] (sigma : Point K → K → Equiv.Perm S)
    (A : (Point K × S) → K → Prop) (hf : (cycleGraph 8).Free (graph sigma A)) :
    (Nat.card (graph sigma A).edgeSet)^4 ≤ 16*(Fintype.card K)^19*(Fintype.card S)^5 := by
  rw [graph_edges]
  exact restriction_bound sigma A hf

/-- With the full ambient vertex count N, every C8-free selected cover
satisfies 4e^5 <= N^6, independently of its sheet permutations. -/
theorem graph_edge_fifth_bound [Nonempty S] (sigma : Point K → K → Equiv.Perm S)
    (A : (Point K × S) → K → Prop) (hf : (cycleGraph 8).Free (graph sigma A)) :
    4*(Nat.card (graph sigma A).edgeSet)^5 ≤
      (Nat.card ((Point K × S) ⊕ (Point K × S)))^6 := by
  rw [graph_edges,Erdos713WengerCover.vertices_card]
  have h := Nat.mul_le_mul (restriction_bound sigma A hf) (size_le A)
  have h' := Nat.mul_le_mul_left 4 h
  convert h' using 1
  ring

omit [Fintype K] [Fintype S] in
/-- Every spanning subgraph of a permutation lift is a selected cover. -/
lemma restriction_of_subgraph (sigma : Point K → K → Equiv.Perm S)
    (G : SimpleGraph ((Point K × S) ⊕ (Point K × S)))
    (hsub : G ≤ Erdos713WengerCover.graph sigma) :
    ∃ A : (Point K × S) → K → Prop, graph sigma A = G := by
  let A : (Point K × S) → K → Prop := fun p a =>
    G.Adj (.inl p) (.inr (lineThrough p.1 a,sigma p.1 a p.2))
  have he (p l : Point K × S) : Rel sigma A p l ↔ G.Adj (.inl p) (.inr l) := by
    constructor
    · intro h
      have hh := h.2
      change G.Adj (.inl p) (.inr (lineThrough p.1 (l.1 0),sigma p.1 (l.1 0) p.2)) at hh
      have hl : l = (lineThrough p.1 (l.1 0),sigma p.1 (l.1 0) p.2) :=
        Prod.ext h.1.1 h.1.2
      rwa [← hl] at hh
    · intro h
      have hl : Erdos713WengerCover.Rel sigma p l := hsub h
      refine ⟨hl,?_⟩
      change G.Adj (.inl p) (.inr (lineThrough p.1 (l.1 0),sigma p.1 (l.1 0) p.2))
      have heq : l = (lineThrough p.1 (l.1 0),sigma p.1 (l.1 0) p.2) :=
        Prod.ext hl.1 hl.2
      rwa [← heq]
  refine ⟨A,?_⟩
  ext u v
  cases u with
  | inl p =>
    cases v with
    | inl p' =>
      change False ↔ G.Adj (.inl p) (.inl p')
      exact ⟨False.elim,fun h => hsub h⟩
    | inr l => exact he p l
  | inr l =>
    cases v with
    | inl p => exact (he p l).trans (G.adj_comm _ _)
    | inr l' =>
      change False ↔ G.Adj (.inr l) (.inr l')
      exact ⟨False.elim,fun h => hsub h⟩

theorem subgraph_edge_fifth_bound [Nonempty S] (sigma : Point K → K → Equiv.Perm S)
    (G : SimpleGraph ((Point K × S) ⊕ (Point K × S)))
    (hsub : G ≤ Erdos713WengerCover.graph sigma) (hf : (cycleGraph 8).Free G) :
    4*(Nat.card G.edgeSet)^5 ≤ (Nat.card ((Point K × S) ⊕ (Point K × S)))^6 := by
  obtain ⟨A,rfl⟩ := restriction_of_subgraph sigma G hsub
  exact graph_edge_fifth_bound sigma A hf

end Erdos713WengerCoverRestriction
