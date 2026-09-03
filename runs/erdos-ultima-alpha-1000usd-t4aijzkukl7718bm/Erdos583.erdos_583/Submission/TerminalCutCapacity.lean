import Submission.Work

/-! Elementary cut obstructions for a colour-constrained all-odd path
partition. The cut inequalities below do not assert their sufficiency. -/
namespace Erdos583TerminalCutCapacityDevelopment
open SimpleGraph Erdos583Work Erdos583Work.BridgeGlue
open scoped Classical
set_option maxHeartbeats 2000000
set_option Elab.async false

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

lemma boundary_sum_degrees (U : Finset V) :
    (∑ v ∈ U, (boundaryGraph G (U : Set V)).degree v)=
      (boundaryGraph G (U : Set V)).edgeSet.ncard := by
  classical
  have hb : (boundaryGraph G (U : Set V)).IsBipartiteWith (U : Set V) ((Uᶜ : Finset V) : Set V) := by
    refine ⟨by simpa only [Finset.coe_compl] using disjoint_compl_right,?_⟩
    intro v w h
    by_cases hv : v ∈ U
    · exact Or.inl ⟨hv,Finset.mem_compl.mpr (fun hw ↦ h.2 (propext (iff_of_true hv hw)))⟩
    · exact Or.inr ⟨Finset.mem_compl.mpr hv,by
        by_contra hw
        exact h.2 (propext (iff_of_false hv hw))⟩
  simpa only [←Set.ncard_coe_finset,coe_edgeFinset] using
    isBipartiteWith_sum_degrees_eq_card_edges hb

lemma degree_split_on_set (U : Finset V) (v : V) (hv : v ∈ U) :
    G.degree v=(within G (U : Set V)).degree v+
      (boundaryGraph G (U : Set V)).degree v := by
  classical
  let J := within G (U : Set V)
  let B := boundaryGraph G (U : Set V)
  change G.degree v=J.degree v+B.degree v
  have hJ : J.neighborSet v=G.neighborSet v ∩ (U : Set V) := by
    ext w
    simp only [J,within,mem_neighborSet,Set.mem_inter_iff,Finset.mem_coe]
    tauto
  have hB : B.neighborSet v=G.neighborSet v ∩ (U : Set V)ᶜ := by
    ext w
    simp only [B,boundaryGraph_adj,mem_neighborSet,Set.mem_inter_iff,Set.mem_compl_iff,Finset.mem_coe]
    constructor
    · rintro ⟨h,hn⟩
      exact ⟨h,fun hw ↦ hn (propext (iff_of_true hv hw))⟩
    · rintro ⟨h,hn⟩
      exact ⟨h,fun hh ↦ hn (hh ▸ hv)⟩
  simp only [←card_neighborSet_eq_degree,←Nat.card_eq_fintype_card,Nat.card_coe_set_eq]
  rw [hJ,hB,←Set.ncard_union_eq (Set.disjoint_left.mpr (fun w hw hw' ↦ hw'.2 hw.2)),
    ←Set.inter_union_distrib_left,Set.union_compl_self,Set.inter_univ]

lemma degree_sum_on_set (U : Finset V) :
    (∑ v ∈ U, G.degree v)=
      2*(within G (U : Set V)).edgeSet.ncard+(boundaryGraph G (U : Set V)).edgeSet.ncard := by
  classical
  let J := within G (U : Set V)
  let B := boundaryGraph G (U : Set V)
  have hJsum : (∑ v ∈ U, J.degree v)=2*J.edgeSet.ncard := by
    have hz (v : V) (hv : v ∉ U) : J.degree v=0 := by
      rw [degree_eq_zero_iff_notMem_support]
      rintro ⟨w,h⟩
      exact hv h.2.1
    have heq : (∑ v ∈ U,J.degree v)=∑ v,J.degree v :=
      Finset.sum_subset (Finset.subset_univ U) (fun v _ hv ↦ hz v hv)
    rw [heq,J.sum_degrees_eq_twice_card_edges]
    simp only [←Set.ncard_coe_finset,coe_edgeFinset]
  calc
    (∑ v ∈ U,G.degree v) = ∑ v ∈ U,(J.degree v+B.degree v) := Finset.sum_congr rfl (degree_split_on_set U)
    _ = _ := by rw [Finset.sum_add_distrib,hJsum]; rw [boundary_sum_degrees]

lemma boundary_parity_of_all_odd (ho : ∀ v, Odd (G.degree v)) (U : Finset V) :
    (boundaryGraph G (U : Set V)).edgeSet.ncard % 2=U.card % 2 := by
  classical
  have hp : Odd (∑ v ∈ U,G.degree v) ↔ Odd U.card := by
    rw [Finset.odd_sum_iff_odd_card_odd]
    simp only [ho,Finset.filter_true]
  rw [degree_sum_on_set] at hp
  simp only [Nat.odd_iff] at hp
  omega

noncomputable def cutCapacity (A U : Finset V) : ℕ :=
  (boundaryGraph G (U : Set V)).edgeSet.ncard+(A\U).card+(U\A).card

lemma cutCapacity_parity (ho : ∀ v, Odd (G.degree v)) (A U : Finset V) :
    cutCapacity (G := G) A U % 2=A.card % 2 := by
  have hp := boundary_parity_of_all_odd ho U
  have hA := Finset.card_sdiff_add_card_inter A U
  have hU := Finset.card_sdiff_add_card_inter U A
  rw [Finset.inter_comm U A] at hU
  dsimp only [cutCapacity]
  omega

lemma boundary_positive_of_connected (hG : G.Connected) (U : Finset V)
    (hne : U.Nonempty) (hproper : U ≠ Finset.univ) :
    0 < (boundaryGraph G (U : Set V)).edgeSet.ncard := by
  classical
  obtain ⟨a,ha⟩ := hne
  obtain ⟨b,hb⟩ : ∃ b, b ∉ U := by
    by_contra hn
    apply hproper
    ext b
    simp only [Finset.mem_univ,iff_true]
    exact not_not.mp (fun hb ↦ hn ⟨b,hb⟩)
  obtain ⟨P⟩ := hG.preconnected a b
  obtain ⟨e,_,he⟩ := walk_boundary_nonempty (U : Set V) P ha hb
  exact (Set.ncard_pos (Set.toFinite _)).mpr ⟨e,he⟩

lemma triangle_boundary_ge_three (ho : ∀ v, Odd (G.degree v))
    {a b c : V} (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c) :
    3 ≤ (boundaryGraph G ({a,b,c} : Set V)).edgeSet.ncard := by
  classical
  let U : Finset V := {a,b,c}
  have hdeg : ∀ v ∈ U, (within G (U : Set V)).degree v=2 := by
    intro v hv
    have hva : v=a ∨ v=b ∨ v=c := by simpa only [U,Finset.mem_insert,Finset.mem_singleton] using hv
    have hN : (within G (U : Set V)).neighborSet v=
        (U : Set V) \ {v} := by
      ext w
      simp only [mem_neighborSet,within,Set.mem_diff,Set.mem_singleton_iff]
      constructor
      · rintro ⟨h,_,hw⟩
        exact ⟨hw,h.ne.symm⟩
      · rintro ⟨hw,hwv⟩
        refine ⟨?_,hv,hw⟩
        have hw' : w=a ∨ w=b ∨ w=c := by
          simpa only [U,Finset.coe_insert,Finset.coe_singleton,Set.mem_insert_iff,Set.mem_singleton_iff] using hw
        rcases hva with rfl|rfl|rfl <;> rcases hw' with rfl|rfl|rfl
        all_goals first | exact (hwv rfl).elim | assumption | exact hab.symm | exact hac.symm | exact hbc.symm
    rw [←card_neighborSet_eq_degree,←Nat.card_eq_fintype_card,Nat.card_coe_set_eq,hN,
      Set.ncard_diff_singleton_of_mem (show v ∈ (U : Set V) from hv)]
    have hcU : (U : Set V).ncard=3 := by
      simp [U,Set.ncard_insert_of_notMem,hab.ne,hac.ne,hbc.ne]
    omega
  have hpos : ∀ v ∈ U, 1 ≤ (boundaryGraph G (U : Set V)).degree v := by
    intro v hv
    have hs := degree_split_on_set (G := G) U v hv
    rw [hdeg v hv] at hs
    have hp := ho v
    rw [Nat.odd_iff,hs] at hp
    omega
  have hsum := Finset.sum_le_sum hpos
  rw [boundary_sum_degrees] at hsum
  have hcU : U.card=3 := by simp [U,hab.ne,hac.ne,hbc.ne]
  simpa only [Finset.sum_const,smul_eq_mul,mul_one,hcU,U,Finset.coe_insert,Finset.coe_singleton] using hsum

lemma triangle_cutCapacity_ge_three (hG : G.Connected) (ho : ∀ v, Odd (G.degree v))
    (hn : 6 ≤ Fintype.card V) {a b c : V}
    (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c) (U : Finset V) :
    3 ≤ cutCapacity (G := G) {a,b,c} U := by
  classical
  let A : Finset V := {a,b,c}
  have hA : A.card=3 := by simp [A,hab.ne,hac.ne,hbc.ne]
  change 3 ≤ cutCapacity (G := G) A U
  have hp := cutCapacity_parity ho A U
  rw [hA] at hp
  by_cases he : U=∅
  · subst U
    simp only [cutCapacity,Finset.sdiff_empty,Finset.empty_sdiff,Finset.card_empty,hA]
    omega
  by_cases hu : U=Finset.univ
  · subst U
    have hc := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ A)
    rw [Finset.card_univ,hA] at hc
    dsimp only [cutCapacity]
    omega
  have hb := boundary_positive_of_connected hG U (Finset.nonempty_iff_ne_empty.mpr he) hu
  by_contra hlt
  have hone : cutCapacity (G := G) A U=1 := by omega
  have hAU : (A\U).card=0 := by dsimp only [cutCapacity] at hone; omega
  have hUA : (U\A).card=0 := by dsimp only [cutCapacity] at hone; omega
  have heq : U=A := Finset.Subset.antisymm
    (Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp hUA))
    (Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp hAU))
  subst U
  have hb3 := triangle_boundary_ge_three ho hab hac hbc
  have hcA : (A : Set V)=({a,b,c} : Set V) := by simp only [A,Finset.coe_insert,Finset.coe_singleton]
  dsimp only [cutCapacity] at hone
  rw [hcA] at hone
  omega

end Erdos583TerminalCutCapacityDevelopment
