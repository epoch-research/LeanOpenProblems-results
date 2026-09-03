import Submission.GraphSerialEdges

/-! Exact cycle counts, minimality, and rigidity for a graphical serial switch.
These are cut-reduction lemmas, not a solution of the remaining core problem. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.GraphSerial
open Erdos184Serial Critical EvenCore Rigidity GraphCircuitCode
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

lemma graph_of_edgeFinset_subset (G : SimpleGraph V) {s : Finset (Sym2 V)}
    (hs : s ⊆ G.edgeFinset) : ∃ R : SimpleGraph V, R ≤ G ∧ R.edgeFinset = s := by
  let R : SimpleGraph V := .fromEdgeSet (s : Set (Sym2 V))
  have hRG : R ≤ G := by
    intro x y hxy
    exact SimpleGraph.mem_edgeFinset.mp (hs hxy.1)
  refine ⟨R,hRG,?_⟩
  ext e
  induction e using Sym2.ind with | h x y =>
  simp only [SimpleGraph.mem_edgeFinset]
  change (s(x,y) ∈ s ∧ x ≠ y) ↔ s(x,y) ∈ s
  exact ⟨And.left,fun h => ⟨h,(SimpleGraph.mem_edgeFinset.mp (hs h)).ne⟩⟩

lemma switch_mono {G R : SimpleGraph V} {H S : SimpleGraph W} {a b : V} {c d : W}
    (hab : a ≠ b) (hRG : R ≤ G) (hSH : S ≤ H) :
    switch R S a b c d ≤ switch G H a b c d := by
  apply SimpleGraph.edgeFinset_subset_edgeFinset.mp
  rw [edgeFinset_switch R S hab,edgeFinset_switch G H hab]
  exact Finset.map_subset_map.mpr (Finset.disjSum_mono (SimpleGraph.edgeFinset_mono hRG)
    (SimpleGraph.edgeFinset_mono hSH))

/-- The abstract retained-port serial code is exactly the cycle code of the
switched graph, after the explicit injective edge relabeling. -/
lemma serial_valid_iff (G : SimpleGraph V) (H : SimpleGraph W) {a b : V} {c d : W}
    (hab : a ≠ b) (hcd : c ≠ d) (s : Finset (Sym2 V ⊕ Sym2 W)) :
    (serial (code G) (code H) s(a,b) s(c,d)).valid s ↔
      (code (switch G H a b c d)).valid (s.map (edgeEmbedding (c := c) (d := d) hab)) := by
  constructor
  · intro hs
    obtain ⟨R,hRG,hR,hRe⟩ := hs.1
    obtain ⟨S,hSH,hS,hSe⟩ := hs.2.1
    have hm : R.Adj a b ↔ S.Adj c d := by
      simpa only [← hRe,← hSe,SimpleGraph.mem_edgeFinset] using hs.2.2
    have heven := (even_switch_iff R S hab hcd).mpr ⟨hR,hS,hm⟩
    refine ⟨switch R S a b c d,switch_mono hab hRG hSH,?_,?_⟩
    · simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using heven
    · rw [edgeFinset_switch R S hab,hRe,hSe,Finset.toLeft_disjSum_toRight]
  · rintro ⟨T,hTG,hT,hTe⟩
    have hmap : s.map (edgeEmbedding (c := c) (d := d) hab) ⊆
        (G.edgeFinset.disjSum H.edgeFinset).map (edgeEmbedding (c := c) (d := d) hab) := by
      rw [← hTe,← edgeFinset_switch G H hab]
      exact SimpleGraph.edgeFinset_mono hTG
    have hsub := Finset.map_subset_map.mp hmap
    have hL : s.toLeft ⊆ G.edgeFinset := by
      simpa only [Finset.toLeft_disjSum] using Finset.toLeft_subset_toLeft hsub
    have hR : s.toRight ⊆ H.edgeFinset := by
      simpa only [Finset.toRight_disjSum] using Finset.toRight_subset_toRight hsub
    obtain ⟨R,hRG,hRe⟩ := graph_of_edgeFinset_subset G hL
    obtain ⟨S,hSH,hSe⟩ := graph_of_edgeFinset_subset H hR
    have heq : switch R S a b c d = T := by
      apply SimpleGraph.edgeFinset_inj.mp
      rw [edgeFinset_switch R S hab,hRe,hSe,Finset.toLeft_disjSum_toRight,hTe]
    have heven : ∀ x, Even ((switch R S a b c d).degree x) := by
      simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hT ⊢
      rw [heq]
      exact hT
    obtain ⟨hR,hS,hm⟩ := (even_switch_iff R S hab hcd).mp heven
    refine ⟨⟨R,hRG,hR,hRe⟩,⟨S,hSH,hS,hSe⟩,?_⟩
    simpa only [← hRe,← hSe,SimpleGraph.mem_edgeFinset] using hm

lemma number_switch (G : SimpleGraph V) (H : SimpleGraph W) {a b : V} {c d : W}
    (hG : ∀ x, Even (G.degree x)) (hH : ∀ y, Even (H.degree y))
    (hp : G.Adj a b) (hq : H.Adj c d) :
    number (switch G H a b c d) = number G + number H - 1 := by
  have hn := serial_hasNumber (p := s(a,b)) (q := s(c,d)) (hasNumber (G := G) le_rfl hG) (hasNumber (G := H) le_rfl hH)
    (SimpleGraph.mem_edgeFinset.mpr hp) (SimpleGraph.mem_edgeFinset.mpr hq)
  have ht := (hasNumber_map_iff (edgeEmbedding (c := c) (d := d) hp.ne)
    (serial_valid_iff G H hp.ne hq.ne) (G.edgeFinset.disjSum H.edgeFinset) (number G + number H - 1)).mpr hn
  rw [← edgeFinset_switch G H hp.ne] at ht
  have heven := (even_switch_iff G H hp.ne hq.ne).mpr ⟨hG,hH,iff_of_true hp hq⟩
  exact (hasNumber_iff le_rfl heven _).mp ht

lemma minimal_switch_iff (G : SimpleGraph V) (H : SimpleGraph W) {a b : V} {c d : W}
    (hG : ∀ x, Even (G.degree x)) (hH : ∀ y, Even (H.degree y))
    (hp : G.Adj a b) (hq : H.Adj c d) :
    EvenMinimal (switch G H a b c d) ↔ EvenMinimal G ∧ EvenMinimal H := by
  have heven := (even_switch_iff G H hp.ne hq.ne).mpr ⟨hG,hH,iff_of_true hp hq⟩
  have hnum := number_switch G H hG hH hp hq
  have ht := minimalCore_map_iff (edgeEmbedding (c := c) (d := d) hp.ne)
    (serial_valid_iff G H hp.ne hq.ne) (G.edgeFinset.disjSum H.edgeFinset) (number G + number H - 1)
  rw [← edgeFinset_switch G H hp.ne] at ht
  have hs := serial_minimalCore_iff (p := s(a,b)) (q := s(c,d)) (valid_edgeFinset (G := G) le_rfl hG)
    (valid_edgeFinset (G := H) le_rfl hH) (hasNumber (G := G) le_rfl hG) (hasNumber (G := H) le_rfl hH)
    (SimpleGraph.mem_edgeFinset.mpr hp) (SimpleGraph.mem_edgeFinset.mpr hq)
  calc
    EvenMinimal (switch G H a b c d) ↔
        MinimalCore (code (switch G H a b c d)) (switch G H a b c d).edgeFinset (number G + number H - 1) := by
      simpa only [hnum,and_true] using (minimalCore_iff le_rfl heven (number G + number H - 1)).symm
    _ ↔ MinimalCore (serial (code G) (code H) s(a,b) s(c,d))
        (G.edgeFinset.disjSum H.edgeFinset) (number G + number H - 1) := ht
    _ ↔ MinimalCore (code G) G.edgeFinset (number G) ∧ MinimalCore (code H) H.edgeFinset (number H) := hs
    _ ↔ EvenMinimal G ∧ EvenMinimal H := by
      rw [minimalCore_iff le_rfl hG,minimalCore_iff le_rfl hH]
      simp

lemma rigid_switch_iff (G : SimpleGraph V) (H : SimpleGraph W) {a b : V} {c d : W}
    (hG : ∀ x, Even (G.degree x)) (hH : ∀ y, Even (H.degree y))
    (hp : G.Adj a b) (hq : H.Adj c d) :
    CycleRigid (switch G H a b c d) ↔ CycleRigid G ∧ CycleRigid H := by
  have heven := (even_switch_iff G H hp.ne hq.ne).mpr ⟨hG,hH,iff_of_true hp hq⟩
  have hnum := number_switch G H hG hH hp hq
  have ht := rigid_map_iff (edgeEmbedding (c := c) (d := d) hp.ne)
    (serial_valid_iff G H hp.ne hq.ne) (G.edgeFinset.disjSum H.edgeFinset) (number G + number H - 1)
  rw [← edgeFinset_switch G H hp.ne] at ht
  have hs := serial_rigid_iff (p := s(a,b)) (q := s(c,d)) (hasNumber (G := G) le_rfl hG) (hasNumber (G := H) le_rfl hH)
    (SimpleGraph.mem_edgeFinset.mpr hp) (SimpleGraph.mem_edgeFinset.mpr hq)
  calc
    CycleRigid (switch G H a b c d) ↔
        Rigid (code (switch G H a b c d)) (switch G H a b c d).edgeFinset (number G + number H - 1) := by
      simpa only [hnum] using (GraphCircuitCode.rigid_iff le_rfl heven).symm
    _ ↔ Rigid (serial (code G) (code H) s(a,b) s(c,d))
        (G.edgeFinset.disjSum H.edgeFinset) (number G + number H - 1) := ht
    _ ↔ Rigid (code G) G.edgeFinset (number G) ∧ Rigid (code H) H.edgeFinset (number H) := hs
    _ ↔ CycleRigid G ∧ CycleRigid H := by
      rw [GraphCircuitCode.rigid_iff le_rfl hG,GraphCircuitCode.rigid_iff le_rfl hH]

lemma nonrigid_minimal_switch_factor (G : SimpleGraph V) (H : SimpleGraph W) {a b : V} {c d : W}
    (hG : ∀ x, Even (G.degree x)) (hH : ∀ y, Even (H.degree y))
    (hp : G.Adj a b) (hq : H.Adj c d)
    (hm : EvenMinimal (switch G H a b c d)) (hn : ¬ CycleRigid (switch G H a b c d)) :
    (EvenMinimal G ∧ ¬ CycleRigid G) ∨ (EvenMinimal H ∧ ¬ CycleRigid H) := by
  obtain ⟨hmG,hmH⟩ := (minimal_switch_iff G H hG hH hp hq).mp hm
  by_cases hrG : CycleRigid G
  · exact Or.inr ⟨hmH,fun hrH => hn ((rigid_switch_iff G H hG hH hp hq).mpr ⟨hrG,hrH⟩)⟩
  · exact Or.inl ⟨hmG,hrG⟩

lemma nonrigid_minimal_switch_smaller (G : SimpleGraph V) (H : SimpleGraph W) {a b : V} {c d : W}
    (hG : ∀ x, Even (G.degree x)) (hH : ∀ y, Even (H.degree y))
    (hp : G.Adj a b) (hq : H.Adj c d)
    (hm : EvenMinimal (switch G H a b c d)) (hn : ¬ CycleRigid (switch G H a b c d)) :
    (EvenMinimal G ∧ ¬ CycleRigid G ∧ Fintype.card V < Fintype.card (V ⊕ W)) ∨
      (EvenMinimal H ∧ ¬ CycleRigid H ∧ Fintype.card W < Fintype.card (V ⊕ W)) := by
  have hv : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨a⟩
  have hw : 0 < Fintype.card W := Fintype.card_pos_iff.mpr ⟨c⟩
  have hc := Fintype.card_sum (α := V) (β := W)
  rcases nonrigid_minimal_switch_factor G H hG hH hp hq hm hn with h | h
  · exact Or.inl ⟨h.1,h.2,by omega⟩
  · exact Or.inr ⟨h.1,h.2,by omega⟩

#print axioms serial_valid_iff
#print axioms number_switch
#print axioms minimal_switch_iff
#print axioms rigid_switch_iff
#print axioms nonrigid_minimal_switch_factor
#print axioms nonrigid_minimal_switch_smaller
end Erdos184Work.GraphSerial
