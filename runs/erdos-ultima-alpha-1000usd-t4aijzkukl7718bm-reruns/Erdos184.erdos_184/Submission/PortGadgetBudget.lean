import Submission.WeakProjection
import Submission.SingleFiberProjection

/-!
A local lower bound on cycles contained inside a port gadget. Contracting the
complement to one apex yields a small cycle partition unless the original
partition contains enough completely internal cycles. This is an auxiliary
projection theorem, not a solution of Erdos 184.
-/
open SimpleGraph
open scoped Classical
namespace Erdos184.PortGadgetBudget
open WeakProjection

variable {V W : Type*} [Fintype V] [Fintype W]
variable {G : SimpleGraph V} {K : SimpleGraph W}

noncomputable def internalPieces (D : Finset G.Subgraph) (S : Set V) : Finset G.Subgraph :=
  D.filter (fun H => H.verts ⊆ S)

lemma vertex_incidence_sum (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D) (S : Set V) :
    2 * (∑ H ∈ D, (H.verts ∩ S).ncard) = ∑ v ∈ S.toFinset, G.degree v := by
  have hcard (H : G.Subgraph) :
      (H.verts ∩ S).ncard = ∑ v ∈ S.toFinset, if v ∈ H.verts then 1 else 0 := by
    rw [← Finset.card_filter]
    have hs : S.toFinset.filter (fun v => v ∈ H.verts) = (H.verts ∩ S).toFinset := by
      ext v
      simp [and_comm]
    rw [hs,Set.ncard_eq_toFinset_card']
  simp_rw [hcard]
  rw [Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  rw [← Finset.card_filter]
  exact cycle_decomposition_vertex_count G D hc hd v

lemma image_card_collapse_complement (f : V → W) (w : W)
    (hi : Set.InjOn f (f ⁻¹' {w})ᶜ) (A : Set V) :
    (f '' A).ncard + (if A ⊆ (f ⁻¹' {w})ᶜ then 1 else 0) =
      (A ∩ (f ⁻¹' {w})ᶜ).ncard + 1 := by
  have hh := SingleFiberProjection.image_card_one_fiber f w hi A
  have hpart : (A ∩ (f ⁻¹' {w})ᶜ) ∪ (A ∩ f ⁻¹' {w}) = A := by
    ext v
    simp only [Set.mem_union,Set.mem_inter_iff,Set.mem_compl_iff]
    tauto
  have hdis : Disjoint (A ∩ (f ⁻¹' {w})ᶜ) (A ∩ f ⁻¹' {w}) := by
    apply Set.disjoint_left.mpr
    exact fun _ hx hy => hx.2 hy.2
  have hcard := Set.ncard_union_eq hdis
  rw [hpart] at hcard
  by_cases hA : A ⊆ (f ⁻¹' {w})ᶜ
  · have hn : ¬(A ∩ f ⁻¹' {w}).Nonempty := by
      rintro ⟨v,hv,hvw⟩
      exact hA hv hvw
    simp only [if_pos hA,if_neg hn] at hh ⊢
    omega
  · have hn : (A ∩ f ⁻¹' {w}).Nonempty := by
      obtain ⟨v,hv,hvw⟩ := Set.not_subset.mp hA
      exact ⟨v,hv,by simpa using hvw⟩
    simp only [if_neg hA,if_pos hn] at hh ⊢
    omega

lemma image_incidence_collapse_complement (f : V → W) (w : W)
    (hi : Set.InjOn f (f ⁻¹' {w})ᶜ) (D : Finset G.Subgraph) :
    (∑ H ∈ D, (f '' H.verts).ncard) + (internalPieces D (f ⁻¹' {w})ᶜ).card =
      (∑ H ∈ D, (H.verts ∩ (f ⁻¹' {w})ᶜ).ncard) + D.card := by
  have hh := Finset.sum_congr (s₁ := D) rfl
    (fun H _ => image_card_collapse_complement f w hi H.verts)
  simpa only [Finset.sum_add_distrib,← Finset.card_filter,Finset.sum_const,
    smul_eq_mul,mul_one,internalPieces] using hh

/-- The exact degree budget for a graph obtained by collapsing one outside
region. Cycles wholly inside the uncollapsed region are charged separately. -/
lemma project_complement_budget (f : V → W)
    (hf : IsWeakMap (G := G) (K := K) f)
    (hi : Set.InjOn (Sym2.map f) (survivingEdges G f))
    (hs : Set.SurjOn (Sym2.map f) (survivingEdges G f) K.edgeSet)
    (w : W) (hv : Set.InjOn f (f ⁻¹' {w})ᶜ)
    (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D) :
    ∃ E : Finset K.Subgraph,
      (∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition K E ∧
      2 * E.card + (∑ v ∈ ((f ⁻¹' {w})ᶜ).toFinset, G.degree v) ≤
        2 * K.edgeSet.ncard + 2 * (internalPieces D (f ⁻¹' {w})ᶜ).card := by
  obtain ⟨E,hcE,hdE,hbE⟩ := WeakProjection.project_decomposition f hf hi hs D hc hd
  have hinc := image_incidence_collapse_complement f w hv D
  have hdeg := vertex_incidence_sum D hc hd (f ⁻¹' {w})ᶜ
  refine ⟨E,hcE,hdE,?_⟩
  simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card,
    ← Set.toFinite_toFinset] at hdeg ⊢
  rw [← hdeg]
  omega

/-- If the contracted graph needs r+q cycles, and the boundary contributes
only r to the projection budget, at least q original pieces are internal. -/
lemma internal_pieces_lower (f : V → W)
    (hf : IsWeakMap (G := G) (K := K) f)
    (hi : Set.InjOn (Sym2.map f) (survivingEdges G f))
    (hs : Set.SurjOn (Sym2.map f) (survivingEdges G f) K.edgeSet)
    (w : W) (hv : Set.InjOn f (f ⁻¹' {w})ᶜ) (r q : ℕ)
    (hbudget : 2 * K.edgeSet.ncard ≤
      (∑ v ∈ ((f ⁻¹' {w})ᶜ).toFinset, G.degree v) + 2 * r)
    (hmin : ∀ E : Finset K.Subgraph,
      (∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) →
      IsDecomposition K E → r + q ≤ E.card)
    (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D) :
    q ≤ (internalPieces D (f ⁻¹' {w})ᶜ).card := by
  obtain ⟨E,hcE,hdE,hbE⟩ := project_complement_budget f hf hi hs w hv D hc hd
  have hlow := hmin E hcE hdE
  omega

lemma internal_piece_card_sum_le {I : Type*} [Fintype I]
    (S : I → Set V) (hS : Pairwise (fun i j => Disjoint (S i) (S j)))
    (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) :
    (∑ i, (internalPieces D (S i)).card) ≤ D.card := by
  have hdis : Set.PairwiseDisjoint (Finset.univ : Finset I)
      (fun i => internalPieces D (S i)) := by
    intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro H hHi hHj
    obtain ⟨hHD,hi⟩ := Finset.mem_filter.mp hHi
    obtain ⟨_,hj⟩ := Finset.mem_filter.mp hHj
    obtain ⟨v⟩ := (hc H hHD).1.nonempty
    exact Set.disjoint_left.mp (hS hij) (hi v.property) (hj v.property)
  rw [← Finset.card_biUnion hdis]
  apply Finset.card_le_card
  intro H hH
  obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hH
  exact (Finset.mem_filter.mp hi).1

lemma internal_piece_card_sum_add_one_le {I : Type*} [Fintype I]
    (S : I → Set V) (hS : Pairwise (fun i j => Disjoint (S i) (S j)))
    (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (H₀ : G.Subgraph) (hH₀ : H₀ ∈ D) (hexternal : ∀ i, ¬H₀.verts ⊆ S i) :
    (∑ i, (internalPieces D (S i)).card) + 1 ≤ D.card := by
  have heq (i : I) : internalPieces (D.erase H₀) (S i) = internalPieces D (S i) := by
    ext H
    simp only [internalPieces,Finset.mem_filter,Finset.mem_erase]
    constructor
    · exact fun h => ⟨h.1.2,h.2⟩
    · rintro ⟨hHD,hS⟩
      refine ⟨⟨?_,hHD⟩,hS⟩
      rintro rfl
      exact hexternal i hS
  have hb := internal_piece_card_sum_le S hS (D.erase H₀)
    (fun H hH => hc H (Finset.mem_of_mem_erase hH))
  simp_rw [heq] at hb
  have hn := Finset.card_erase_add_one hH₀
  omega

end Erdos184.PortGadgetBudget
