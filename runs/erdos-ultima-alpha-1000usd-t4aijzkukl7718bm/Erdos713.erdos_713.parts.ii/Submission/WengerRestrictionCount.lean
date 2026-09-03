import FormalConjecturesUtil
import Submission.WengerRestrictionGeometry

/-! A power loss for every C8-free edge restriction of the four-coordinate
Wenger graph. The bound concerns this construction, not arbitrary C8-free graphs. -/
open SimpleGraph Finset
open scoped Classical
namespace Erdos713WengerRestriction
open Erdos713ThetaC4Deletion Erdos713ThetaHeavyShadow Erdos713ThetaAnchorBudget
open Erdos713ThetaAnchorPacking
variable {K : Type*} [Field K] [Fintype K]
set_option maxHeartbeats 2000000

noncomputable def size (A : Point K → K → Prop) : ℕ := ∑ p, (row A p).card

noncomputable def pairMass (A : Point K → K → Prop) (a b : K) : ℕ :=
  ∑ p, if A p a ∧ A p b then 1 else 0

lemma pairMass_grid_sum (A : Point K → K → Prop) (a b : K) (hab : a ≠ b) :
    pairMass A a b = ∑ r : K × K, edges (grid A a b r) := by
  have he := Fintype.sum_equiv (planeEquiv a b hab).symm
    (fun z : (K × K) × (K × K) => if grid A a b z.1 z.2.1 z.2.2 then (1 : ℕ) else 0)
    (fun p : Point K => if A p a ∧ A p b then (1 : ℕ) else 0)
    (fun z => by
      simp only [grid,planeEquiv,Equiv.coe_fn_symm_mk]
      split_ifs <;> rfl)
  rw [pairMass,← he,Fintype.sum_prod_type]
  apply sum_congr rfl
  intro r _
  simp only [edges,Nat.card_eq_fintype_card,Fintype.card_subtype,card_filter]

lemma pairMass_bound (A : Point K → K → Prop) (hf : (cycleGraph 8).Free (graph A))
    (a b : K) (hab : a ≠ b) :
    pairMass A a b ≤ (Fintype.card K)^3*(Nat.sqrt (Fintype.card K)+2) := by
  rw [pairMass_grid_sum A a b hab]
  have hh := sum_le_sum (s := (univ : Finset (K × K)))
    (fun r _ => four_free_edges_le_sqrt (grid_four_free A hf a b hab r))
  simp only [Nat.card_eq_fintype_card,sum_const,card_univ,Fintype.card_prod,nsmul_eq_mul,Nat.cast_id] at hh
  convert hh using 1
  ring

omit [Field K] in
lemma size_le (A : Point K → K → Prop) : size A ≤ (Fintype.card K)^5 := by
  have hp (p : Point K) : (row A p).card ≤ Fintype.card K :=
    (card_le_card (filter_subset _ _)).trans_eq (card_univ)
  have hh := sum_le_sum (s := univ) (fun p _ => hp p)
  simp only [sum_const,card_univ,Fintype.card_fun,Fintype.card_fin,nsmul_eq_mul] at hh
  change size A ≤ _ at hh
  simpa only [show (Fintype.card K)^4*Fintype.card K=(Fintype.card K)^5 by ring] using hh

lemma degree_square_bound (A : Point K → K → Prop) (hf : (cycleGraph 8).Free (graph A)) :
    (∑ p : Point K, (row A p).card^2) ≤
      (Fintype.card K)^5*(Nat.sqrt (Fintype.card K)+3) := by
  have hid : (∑ p : Point K, (row A p).card^2) = size A+
      ∑ ab ∈ (univ : Finset K).offDiag, pairMass A ab.1 ab.2 := by
    have hs := pair_incidence_sum A (univ : Finset (Point K))
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
      (Fintype.card K)^5*(Nat.sqrt (Fintype.card K)+2) := by
    have hsum := sum_le_sum (s := (univ : Finset K).offDiag)
      (fun ab hab => pairMass_bound A hf ab.1 ab.2 (mem_offDiag.mp hab).2.2)
    simp only [sum_const,nsmul_eq_mul] at hsum
    have hcard : (univ : Finset K).offDiag.card ≤ (Fintype.card K)^2 := by
      simp only [offDiag_card,card_univ,pow_two]
      exact Nat.sub_le _ _
    have hm := Nat.mul_le_mul_right ((Fintype.card K)^3*(Nat.sqrt (Fintype.card K)+2)) hcard
    have hh := hsum.trans hm
    convert hh using 1
    ring
  have he := size_le A
  nlinarith only [hb,he]

/-- The full graph has q^5 edges. Every C8-free edge restriction instead
satisfies e^4<=16*q^19, a fixed power loss, not just a constant loss. -/
theorem restriction_bound (A : Point K → K → Prop) (hf : (cycleGraph 8).Free (graph A)) :
    (size A)^4 ≤ 16*(Fintype.card K)^19 := by
  let q := Fintype.card K
  have hq : 1 ≤ q := Fintype.card_pos_iff.mpr ⟨0⟩
  have hs1 : 1 ≤ Nat.sqrt q := by
    exact (Nat.le_sqrt.mpr (by simpa using hq))
  have hs2 : (Nat.sqrt q)^2 ≤ q := by simpa only [pow_two] using Nat.sqrt_le q
  have hc := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Point K)))
    (f := fun p => (row A p).card)
  simp only [card_univ,Fintype.card_fun,Fintype.card_fin] at hc
  change (size A)^2 ≤ q^4*(∑ p, (row A p).card^2) at hc
  have hd := degree_square_bound A hf
  change (∑ p, (row A p).card^2) ≤ q^5*(Nat.sqrt q+3) at hd
  have hh := hc.trans (Nat.mul_le_mul_left (q^4) hd)
  have hcoef : Nat.sqrt q+3 ≤ 4*Nat.sqrt q := by omega
  have he : (size A)^2 ≤ 4*q^9*Nat.sqrt q := by
    have hm := Nat.mul_le_mul_left (q^9) hcoef
    nlinarith only [hh,hm]
  have hsq := Nat.pow_le_pow_left he 2
  have hmul := Nat.mul_le_mul_left (16*q^18) hs2
  nlinarith only [hsq,hmul]

lemma graph_edges (A : Point K → K → Prop) : Nat.card (graph A).edgeSet = size A := by
  have hh := (graph A).two_mul_card_edgeFinset
  simp only [card_filter,Fintype.sum_prod_type,Fintype.sum_sum_type,graph,
    Erdos713C6.bipGraph,sum_add_distrib,edgeFinset_card,← Nat.card_eq_fintype_card] at hh
  have hflip : (∑ l : Point K, ∑ p : Point K, if Rel A p l then 1 else 0) =
      ∑ p : Point K, ∑ l : Point K, if Rel A p l then 1 else 0 := sum_comm
  rw [hflip] at hh
  have hrow (p : Point K) : (∑ l : Point K, if Rel A p l then 1 else 0) = (row A p).card := by
    let f : {l : Point K // Rel A p l} ≃ {a : K // A p a} :=
      { toFun := fun l => ⟨l.val 0,l.property.2⟩
        invFun := fun a => ⟨lineThrough p a.val, rfl, a.property⟩
        left_inv := fun l => Subtype.ext l.property.1.symm
        right_inv := fun _ => rfl }
    have hcard := Fintype.card_congr f
    simpa only [Fintype.card_subtype,card_filter,row] using hcard
  simp_rw [hrow] at hh
  have hh' : 2*Nat.card (graph A).edgeSet = size A+size A := by
    simpa [size] using hh
  omega

/-- This statement counts graph edges, not merely selected parameter pairs. -/
theorem graph_edge_bound (A : Point K → K → Prop) (hf : (cycleGraph 8).Free (graph A)) :
    (Nat.card (graph A).edgeSet)^4 ≤ 16*(Fintype.card K)^19 := by
  rw [graph_edges]
  exact restriction_bound A hf

omit [Fintype K] in
/-- Every spanning subgraph of the full Wenger incidence graph is an edge
restriction of the parameterized form counted above. -/
lemma restriction_of_subgraph (G : SimpleGraph (Point K ⊕ Point K))
    (hsub : G ≤ graph (fun _ _ => True)) :
    ∃ A : Point K → K → Prop, graph A = G := by
  let A : Point K → K → Prop := fun p a => G.Adj (.inl p) (.inr (lineThrough p a))
  refine ⟨A,?_⟩
  ext u v
  cases u with
  | inl p =>
    cases v with
    | inl p' =>
      change False ↔ G.Adj (.inl p) (.inl p')
      exact ⟨False.elim,fun h => hsub h⟩
    | inr l =>
      change Rel A p l ↔ G.Adj (.inl p) (.inr l)
      constructor
      · intro h
        have hh := h.2
        change G.Adj (.inl p) (.inr (lineThrough p (l 0))) at hh
        rwa [← h.1] at hh
      · intro h
        have hl : l=lineThrough p (l 0) := (hsub h).1
        refine ⟨hl,?_⟩
        change G.Adj (.inl p) (.inr (lineThrough p (l 0)))
        rwa [← hl]
  | inr l =>
    cases v with
    | inl p =>
      change Rel A p l ↔ G.Adj (.inr l) (.inl p)
      constructor
      · intro h
        have hh := h.2
        change G.Adj (.inl p) (.inr (lineThrough p (l 0))) at hh
        rw [← h.1] at hh
        exact hh.symm
      · intro h
        have hl : l=lineThrough p (l 0) := (hsub h).1
        refine ⟨hl,?_⟩
        change G.Adj (.inl p) (.inr (lineThrough p (l 0)))
        rw [← hl]
        exact h.symm
    | inr l' =>
      change False ↔ G.Adj (.inr l) (.inr l')
      exact ⟨False.elim,fun h => hsub h⟩

theorem subgraph_edge_bound (G : SimpleGraph (Point K ⊕ Point K))
    (hsub : G ≤ graph (fun _ _ => True)) (hf : (cycleGraph 8).Free G) :
    (Nat.card G.edgeSet)^4 ≤ 16*(Fintype.card K)^19 := by
  obtain ⟨A,rfl⟩ := restriction_of_subgraph G hsub
  exact graph_edge_bound A hf

lemma full_graph_edges : Nat.card (graph (fun (_ : Point K) _ => True)).edgeSet = (Fintype.card K)^5 := by
  rw [graph_edges]
  simp only [size,row,filter_true,sum_const,card_univ,Fintype.card_fun,
    Fintype.card_fin,nsmul_eq_mul,Nat.cast_id]
  ring

/-- Retaining at least 1/t of the full edge count forces q<=16*t^4.
In particular no fixed positive fraction survives as q grows. -/
theorem retained_fraction_bound (G : SimpleGraph (Point K ⊕ Point K))
    (hsub : G ≤ graph (fun _ _ => True)) (hf : (cycleGraph 8).Free G) (t : ℕ)
    (hretain : (Fintype.card K)^5 ≤ t*Nat.card G.edgeSet) : Fintype.card K ≤ 16*t^4 := by
  let q := Fintype.card K
  have hq : 0 < q := Fintype.card_pos_iff.mpr ⟨0⟩
  have he := subgraph_edge_bound G hsub hf
  have hr := Nat.pow_le_pow_left hretain 4
  have hm := Nat.mul_le_mul_left (t^4) he
  have hh : q*q^19 ≤ (16*t^4)*q^19 := by
    change q^5 ≤ _ at hretain
    change (q^5)^4 ≤ _ at hr
    change t^4*(Nat.card G.edgeSet)^4 ≤ t^4*(16*q^19) at hm
    nlinarith only [hr,hm]
  exact (mul_le_mul_iff_left₀ (pow_pos hq 19)).mp hh

#print axioms restriction_bound
#print axioms graph_edge_bound
#print axioms retained_fraction_bound
end Erdos713WengerRestriction
