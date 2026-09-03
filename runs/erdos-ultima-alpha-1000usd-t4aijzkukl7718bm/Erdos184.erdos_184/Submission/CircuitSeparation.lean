import Submission.SerialMinimum

/-! Exact circuit-partition counts across a disjoint separation of supports.
These statements concern finite circuit codes, not a graphical rigidity
hypothesis or a uniform cycle bound. -/
open scoped Classical
namespace Erdos184Serial
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false
variable {E : Type*} [DecidableEq E] {C : Code E} {s t : Finset E}

/-- Validity splits independently across the two disjoint coordinate sets. -/
structure Separation (C : Code E) (s t : Finset E) : Prop where
  disjoint : Disjoint s t
  valid_iff : ∀ u ⊆ s ∪ t, C.valid u ↔ C.valid (u ∩ s) ∧ C.valid (u ∩ t)

namespace Separation
variable (h : Separation C s t)
include h

lemma symm : Separation C t s := by
  refine ⟨h.disjoint.symm,?_⟩
  intro u hu
  simpa only [Finset.union_comm,and_comm] using h.valid_iff u (by simpa only [Finset.union_comm] using hu)

lemma circuit_side {a : Finset E} (ha : Circuit C a) (has : a ⊆ s ∪ t) :
    a ⊆ s ∨ a ⊆ t := by
  have hav := ((h.valid_iff a has).mp ha.1).1
  by_cases hn : (a ∩ s).Nonempty
  · have he := ha.2.2 (a ∩ s) Finset.inter_subset_left hav hn
    exact Or.inl (he ▸ Finset.inter_subset_right)
  · right
    intro x hx
    rcases Finset.mem_union.mp (has hx) with hs | ht
    · exact (hn ⟨x,Finset.mem_inter.mpr ⟨hx,hs⟩⟩).elim
    · exact ht

lemma circuit_right_iff {a : Finset E} (ha : Circuit C a) (has : a ⊆ s ∪ t) :
    a ⊆ t ↔ ¬ a ⊆ s := by
  constructor
  · intro ht hs
    obtain ⟨x,hx⟩ := ha.2.1
    exact Finset.disjoint_left.mp h.disjoint (hs hx) (ht hx)
  · intro hn
    exact (h.circuit_side ha has).resolve_left hn

lemma partition_filter {u : Finset E} {D : Finset (Finset E)}
    (hu : u ⊆ s ∪ t) (hD : Partition C u D) :
    Partition C (u ∩ s) (D.filter (fun a => a ⊆ s)) := by
  refine ⟨fun a ha => hD.1 a (Finset.mem_filter.mp ha).1,?_,?_⟩
  · intro a ha b hb hn
    exact hD.2.1 (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hb).1 hn
  · ext x
    simp only [Finset.mem_biUnion,Finset.mem_filter,Finset.mem_inter,id_eq]
    constructor
    · rintro ⟨a,⟨ha,hs⟩,hx⟩
      exact ⟨hD.piece_subset ha hx,hs hx⟩
    · rintro ⟨hxu,hxs⟩
      have hx : x ∈ D.biUnion id := hD.2.2.symm ▸ hxu
      obtain ⟨a,ha,hxa⟩ := Finset.mem_biUnion.mp hx
      have has : a ⊆ s := by
        rcases h.circuit_side (hD.1 a ha) ((hD.piece_subset ha).trans hu) with hs | ht
        · exact hs
        · exact (Finset.disjoint_left.mp h.disjoint hxs (ht hxa)).elim
      exact ⟨a,⟨ha,has⟩,hxa⟩

lemma split_card {u : Finset E} {D : Finset (Finset E)}
    (hu : u ⊆ s ∪ t) (hD : Partition C u D) :
    (D.filter (fun a => a ⊆ s)).card + (D.filter (fun a => a ⊆ t)).card = D.card := by
  have he : D.filter (fun a => a ⊆ t) = D.filter (fun a => ¬ a ⊆ s) := by
    apply Finset.filter_congr
    intro a ha
    exact h.circuit_right_iff (hD.1 a ha) ((hD.piece_subset ha).trans hu)
  rw [he]
  exact Finset.card_filter_add_card_filter_not _

lemma partition_split {u : Finset E} {D : Finset (Finset E)}
    (hu : u ⊆ s ∪ t) (hD : Partition C u D) :
    ∃ A B, Partition C (u ∩ s) A ∧ Partition C (u ∩ t) B ∧ A.card + B.card = D.card := by
  refine ⟨D.filter (fun a => a ⊆ s),D.filter (fun a => a ⊆ t),
    h.partition_filter hu hD,?_,h.split_card hu hD⟩
  exact h.symm.partition_filter (by simpa only [Finset.union_comm] using hu) hD

lemma hasNumber_add {k l : ℕ} (hs : HasNumber C s k) (ht : HasNumber C t l) :
    HasNumber C (s ∪ t) (k + l) := by
  obtain ⟨A,hA,hk⟩ := hs.1
  obtain ⟨B,hB,hl⟩ := ht.1
  obtain ⟨hAB,hcard⟩ := hA.join hB h.disjoint
  refine ⟨⟨A ∪ B,hAB,by omega⟩,?_⟩
  intro D hD
  obtain ⟨A',B',hA',hB',hc⟩ := h.partition_split (Finset.Subset.refl _) hD
  have hs' : (s ∪ t) ∩ s = s := Finset.inter_eq_right.mpr Finset.subset_union_left
  have ht' : (s ∪ t) ∩ t = t := Finset.inter_eq_right.mpr Finset.subset_union_right
  rw [hs'] at hA'
  rw [ht'] at hB'
  have hlo := hs.2 A' hA'
  have hro := ht.2 B' hB'
  omega

lemma split_union {u : Finset E} (hu : u ⊆ s ∪ t) :
    (u ∩ s) ∪ (u ∩ t) = u := by
  rw [← Finset.inter_union_distrib_left,Finset.inter_eq_left.mpr hu]

lemma left_union_inter {u : Finset E} (hu : u ⊆ s) : (u ∪ t) ∩ s = u := by
  ext x
  simp only [Finset.mem_inter,Finset.mem_union]
  constructor
  · rintro ⟨hx,hs⟩
    rcases hx with hu | ht
    · exact hu
    · exact (Finset.disjoint_left.mp h.disjoint hs ht).elim
  · intro hx
    exact ⟨Or.inl hx,hu hx⟩

lemma left_union_valid {u : Finset E} (hu : u ⊆ s) (hv : C.valid u) (ht : C.valid t) :
    C.valid (u ∪ t) := by
  apply (h.valid_iff (u ∪ t) (Finset.union_subset_union hu (Finset.Subset.refl _))).mpr
  rw [h.left_union_inter hu,Finset.inter_eq_right.mpr Finset.subset_union_right]
  exact ⟨hv,ht⟩

lemma left_union_ssubset {u : Finset E} (hu : u ⊂ s) : u ∪ t ⊂ s ∪ t := by
  refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.union_subset_union hu.1 (Finset.Subset.refl _),?_⟩
  intro he
  have hi := congrArg (fun a => a ∩ s) he
  dsimp only at hi
  rw [h.left_union_inter hu.1,Finset.inter_eq_right.mpr Finset.subset_union_left] at hi
  exact hu.ne hi

lemma minimalCore_left {k l : ℕ} (hs : HasNumber C s k) (ht : HasNumber C t l)
    (hvt : C.valid t) (hm : MinimalCore C (s ∪ t) (k + l)) : MinimalCore C s k := by
  refine ⟨hs,?_⟩
  intro u hus hu
  obtain ⟨D,hD,hlt⟩ := hm.2 (u ∪ t) (h.left_union_ssubset hus) (h.left_union_valid hus.1 hu hvt)
  obtain ⟨A,B,hA,hB,hcard⟩ := h.partition_split
    (Finset.union_subset_union hus.1 (Finset.Subset.refl _)) hD
  rw [h.left_union_inter hus.1] at hA
  rw [Finset.inter_eq_right.mpr Finset.subset_union_right] at hB
  have hlo := ht.2 B hB
  exact ⟨A,hA,by omega⟩

lemma minimalCore_add {k l : ℕ} (hs : MinimalCore C s k) (ht : MinimalCore C t l) :
    MinimalCore C (s ∪ t) (k + l) := by
  refine ⟨h.hasNumber_add hs.1 ht.1,?_⟩
  intro u hus hu
  obtain ⟨hvL,hvR⟩ := (h.valid_iff u hus.1).mp hu
  obtain ⟨A,hA,hAle,hAlt⟩ := hs.partition_le Finset.inter_subset_right hvL
  obtain ⟨B,hB,hBle,hBlt⟩ := ht.partition_le Finset.inter_subset_right hvR
  have hd : Disjoint (u ∩ s) (u ∩ t) :=
    h.disjoint.mono Finset.inter_subset_right Finset.inter_subset_right
  obtain ⟨hAB,hcard⟩ := hA.join hB hd
  rw [h.split_union hus.1] at hAB
  have hne : u ∩ s ≠ s ∨ u ∩ t ≠ t := by
    by_contra hn
    push_neg at hn
    have he := h.split_union hus.1
    rw [hn.1,hn.2] at he
    exact hus.ne he.symm
  refine ⟨A ∪ B,hAB,?_⟩
  rcases hne with hn | hn
  · have hlt := hAlt hn
    omega
  · have hlt := hBlt hn
    omega

lemma minimalCore_iff {k l : ℕ} (hvs : C.valid s) (hvt : C.valid t)
    (hs : HasNumber C s k) (ht : HasNumber C t l) :
    MinimalCore C (s ∪ t) (k + l) ↔ MinimalCore C s k ∧ MinimalCore C t l := by
  constructor
  · intro hm
    refine ⟨h.minimalCore_left hs ht hvt hm,?_⟩
    apply h.symm.minimalCore_left ht hs hvs
    simpa only [Finset.union_comm,Nat.add_comm] using hm
  · rintro ⟨hmL,hmR⟩
    exact h.minimalCore_add hmL hmR

lemma rigid_add {k l : ℕ} (hs : Rigid C s k) (ht : Rigid C t l) :
    Rigid C (s ∪ t) (k + l) := by
  intro D hD
  obtain ⟨A,B,hA,hB,hcard⟩ := h.partition_split (Finset.Subset.refl _) hD
  rw [Finset.inter_eq_right.mpr Finset.subset_union_left] at hA
  rw [Finset.inter_eq_right.mpr Finset.subset_union_right] at hB
  have hk := hs A hA
  have hl := ht B hB
  omega

lemma rigid_iff {k l : ℕ} (hs : HasNumber C s k) (ht : HasNumber C t l) :
    Rigid C (s ∪ t) (k + l) ↔ Rigid C s k ∧ Rigid C t l := by
  constructor
  · intro hr
    constructor
    · intro A hA
      obtain ⟨B,hB,hBl⟩ := ht.1
      obtain ⟨hAB,hcard⟩ := hA.join hB h.disjoint
      have hh := hr (A ∪ B) hAB
      omega
    · intro B hB
      obtain ⟨A,hA,hAk⟩ := hs.1
      obtain ⟨hAB,hcard⟩ := hA.join hB h.disjoint
      have hh := hr (A ∪ B) hAB
      omega
  · rintro ⟨hL,hR⟩
    exact h.rigid_add hL hR

lemma nonrigid_minimal_factor {k l : ℕ} (hvs : C.valid s) (hvt : C.valid t)
    (hs : HasNumber C s k) (ht : HasNumber C t l)
    (hm : MinimalCore C (s ∪ t) (k + l)) (hn : ¬ Rigid C (s ∪ t) (k + l)) :
    (MinimalCore C s k ∧ ¬ Rigid C s k) ∨ (MinimalCore C t l ∧ ¬ Rigid C t l) := by
  obtain ⟨hL,hR⟩ := (h.minimalCore_iff hvs hvt hs ht).mp hm
  by_cases hr : Rigid C s k
  · exact Or.inr ⟨hR,fun ht => hn (h.rigid_add hr ht)⟩
  · exact Or.inl ⟨hL,hr⟩

#print axioms hasNumber_add
#print axioms minimalCore_iff
#print axioms rigid_iff
#print axioms nonrigid_minimal_factor
end Separation
end Erdos184Serial
