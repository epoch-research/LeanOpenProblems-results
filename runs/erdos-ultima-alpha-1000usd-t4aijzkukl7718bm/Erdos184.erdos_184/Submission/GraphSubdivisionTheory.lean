import Submission.GraphSubdivisionEdges

/-! Exact invariance under subdivision for even graphs.
No rigidity or linear bound for arbitrary minimal cores is assumed. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.GraphSubdivision
open Erdos184Serial Critical EvenCore Rigidity GraphCircuitCode
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Subdivide the edge `ab` once. If it is absent, just add an isolated vertex. -/
noncomputable def subdivide (G : SimpleGraph V) (a b : V) : SimpleGraph (V ⊕ Unit) :=
  split G (if G.Adj a b then {()} else ∅) a b

lemma subdivide_eq_split (G : SimpleGraph V) {a b : V} (hp : G.Adj a b) :
    subdivide G a b = split G {()} a b := by
  unfold subdivide
  rw [if_pos hp]

lemma even_subdivide_iff (G : SimpleGraph V) {a b : V} (hab : a ≠ b) :
    (∀ x, Even ((subdivide G a b).degree x)) ↔ (∀ x, Even (G.degree x)) := by
  rw [subdivide,even_split_iff G _ hab]
  have hm : G.Adj a b ↔ () ∈ (if G.Adj a b then ({()} : Finset Unit) else ∅) := by
    by_cases hp : G.Adj a b <;> simp [hp]
  exact and_iff_left hm

lemma split_mono {G R : SimpleGraph V} {s t : Finset Unit} {a b : V}
    (hab : a ≠ b) (hRG : R ≤ G) (hst : s ⊆ t) : split R s a b ≤ split G t a b := by
  apply SimpleGraph.edgeFinset_subset_edgeFinset.mp
  rw [edgeFinset_split R s hab,edgeFinset_split G t hab]
  exact Finset.map_subset_map.mpr (Finset.disjSum_mono (SimpleGraph.edgeFinset_mono hRG) hst)

lemma serial_valid_iff (G : SimpleGraph V) {a b : V} (hab : a ≠ b)
    (s : Finset (Sym2 V ⊕ Unit)) :
    (serial (code G) pointCode s(a,b) ()).valid s ↔
      (code (subdivide G a b)).valid (s.map (edgeEmbedding hab)) := by
  constructor
  · intro hs
    obtain ⟨R,hRG,hR,hRe⟩ := hs.1
    have hm : R.Adj a b ↔ () ∈ s.toRight := by
      simpa only [← hRe,SimpleGraph.mem_edgeFinset] using hs.2.2
    have ht : s.toRight ⊆ (if G.Adj a b then {()} else ∅) := by
      intro u hu
      cases u
      have hp := hRG (hm.mpr hu)
      simp [hp]
    have heven := (even_split_iff R s.toRight hab).mpr ⟨hR,hm⟩
    refine ⟨split R s.toRight a b,split_mono hab hRG ht,?_,?_⟩
    · simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using heven
    · rw [edgeFinset_split R s.toRight hab,hRe,Finset.toLeft_disjSum_toRight]
  · rintro ⟨T,hTG,hT,hTe⟩
    have hmap : s.map (edgeEmbedding hab) ⊆
        (G.edgeFinset.disjSum (if G.Adj a b then {()} else ∅)).map (edgeEmbedding hab) := by
      rw [← hTe,← edgeFinset_split G _ hab]
      exact SimpleGraph.edgeFinset_mono hTG
    have hsub := Finset.map_subset_map.mp hmap
    have hL : s.toLeft ⊆ G.edgeFinset := by
      simpa only [Finset.toLeft_disjSum] using Finset.toLeft_subset_toLeft hsub
    obtain ⟨R,hRG,hRe⟩ := GraphSerial.graph_of_edgeFinset_subset G hL
    have heq : split R s.toRight a b = T := by
      apply SimpleGraph.edgeFinset_inj.mp
      rw [edgeFinset_split R s.toRight hab,hRe,Finset.toLeft_disjSum_toRight,hTe]
    have heven : ∀ x, Even ((split R s.toRight a b).degree x) := by
      simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hT ⊢
      rw [heq]
      exact hT
    obtain ⟨hR,hm⟩ := (even_split_iff R s.toRight hab).mp heven
    refine ⟨⟨R,hRG,hR,hRe⟩,trivial,?_⟩
    simpa only [← hRe,SimpleGraph.mem_edgeFinset] using hm

lemma edgeFinset_subdivide (G : SimpleGraph V) {a b : V} (hp : G.Adj a b) :
    (subdivide G a b).edgeFinset = (G.edgeFinset.disjSum {()}).map (edgeEmbedding hp.ne) := by
  rw [subdivide,edgeFinset_split G _ hp.ne]
  congr 2
  exact if_pos hp

lemma number_subdivide (G : SimpleGraph V) {a b : V}
    (hG : ∀ x, Even (G.degree x)) (hp : G.Adj a b) :
    number (subdivide G a b) = number G := by
  have hn := serial_hasNumber (p := s(a,b)) (q := ()) (hasNumber (G := G) le_rfl hG)
    point_hasNumber (SimpleGraph.mem_edgeFinset.mpr hp) (by simp)
  have ht := (hasNumber_map_iff (edgeEmbedding hp.ne) (serial_valid_iff G hp.ne)
    (G.edgeFinset.disjSum {()}) (number G)).mpr (by simpa using hn)
  rw [← edgeFinset_subdivide G hp] at ht
  exact (hasNumber_iff le_rfl ((even_subdivide_iff G hp.ne).mpr hG) _).mp ht

lemma minimal_subdivide_iff (G : SimpleGraph V) {a b : V}
    (hG : ∀ x, Even (G.degree x)) (hp : G.Adj a b) :
    EvenMinimal (subdivide G a b) ↔ EvenMinimal G := by
  have heven := (even_subdivide_iff G hp.ne).mpr hG
  have hnum := number_subdivide G hG hp
  have ht := minimalCore_map_iff (edgeEmbedding hp.ne) (serial_valid_iff G hp.ne)
    (G.edgeFinset.disjSum {()}) (number G)
  rw [← edgeFinset_subdivide G hp] at ht
  have hs := serial_minimalCore_iff (p := s(a,b)) (q := ())
    (valid_edgeFinset (G := G) le_rfl hG) (show pointCode.valid {()} from trivial)
    (hasNumber (G := G) le_rfl hG) point_hasNumber (SimpleGraph.mem_edgeFinset.mpr hp) (by simp)
  calc
    EvenMinimal (subdivide G a b) ↔ MinimalCore (code (subdivide G a b))
        (subdivide G a b).edgeFinset (number G) := by
      simpa only [hnum,and_true] using (minimalCore_iff le_rfl heven (number G)).symm
    _ ↔ MinimalCore (serial (code G) pointCode s(a,b) ()) (G.edgeFinset.disjSum {()}) (number G) := ht
    _ ↔ MinimalCore (code G) G.edgeFinset (number G) := by
      simpa only [Nat.add_sub_cancel,point_minimalCore,and_true] using hs
    _ ↔ EvenMinimal G := by
      rw [minimalCore_iff le_rfl hG]
      simp

lemma rigid_subdivide_iff (G : SimpleGraph V) {a b : V}
    (hG : ∀ x, Even (G.degree x)) (hp : G.Adj a b) :
    CycleRigid (subdivide G a b) ↔ CycleRigid G := by
  have heven := (even_subdivide_iff G hp.ne).mpr hG
  have hnum := number_subdivide G hG hp
  have ht := rigid_map_iff (edgeEmbedding hp.ne) (serial_valid_iff G hp.ne)
    (G.edgeFinset.disjSum {()}) (number G)
  rw [← edgeFinset_subdivide G hp] at ht
  have hs := serial_rigid_iff (p := s(a,b)) (q := ())
    (hasNumber (G := G) le_rfl hG) point_hasNumber (SimpleGraph.mem_edgeFinset.mpr hp) (by simp)
  calc
    CycleRigid (subdivide G a b) ↔ Rigid (code (subdivide G a b))
        (subdivide G a b).edgeFinset (number G) := by
      simpa only [hnum] using (GraphCircuitCode.rigid_iff le_rfl heven).symm
    _ ↔ Rigid (serial (code G) pointCode s(a,b) ()) (G.edgeFinset.disjSum {()}) (number G) := ht
    _ ↔ Rigid (code G) G.edgeFinset (number G) := by
      simpa only [Nat.add_sub_cancel,point_rigid,and_true] using hs
    _ ↔ CycleRigid G := GraphCircuitCode.rigid_iff le_rfl hG

lemma degree_subdivide_old (G : SimpleGraph V) {a b : V} (hab : a ≠ b) (x : V) :
    (subdivide G a b).degree (.inl x) = G.degree x := by
  apply degree_old_of_match G _ hab
  by_cases hp : G.Adj a b <;> simp [hp]

lemma degree_subdivide_new (G : SimpleGraph V) {a b : V} (hp : G.Adj a b) :
    (subdivide G a b).degree (.inr ()) = 2 := by
  have hN : (subdivide G a b).neighborFinset (.inr ()) = {Sum.inl a,Sum.inl b} := by
    ext x
    cases x with
    | inl x => simp [SimpleGraph.mem_neighborFinset,subdivide,split,hp]
    | inr u => simp [SimpleGraph.mem_neighborFinset,subdivide,split]
  rw [← SimpleGraph.card_neighborFinset_eq_degree,hN]
  simp [hp.ne]

lemma card_edges_subdivide (G : SimpleGraph V) {a b : V} (hp : G.Adj a b) :
    (subdivide G a b).edgeFinset.card = G.edgeFinset.card + 1 := by
  rw [edgeFinset_subdivide G hp,Finset.card_map,Finset.card_disjSum,Finset.card_singleton]

#print axioms serial_valid_iff
#print axioms number_subdivide
#print axioms minimal_subdivide_iff
#print axioms rigid_subdivide_iff
#print axioms degree_subdivide_new
end Erdos184Work.GraphSubdivision
