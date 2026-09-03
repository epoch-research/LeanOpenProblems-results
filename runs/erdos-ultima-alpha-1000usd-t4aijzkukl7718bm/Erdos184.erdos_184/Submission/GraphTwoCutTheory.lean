import Submission.GraphTwoCut

/-! Exact count, minimality and rigidity across a two-edge cut, using fresh
closure paths. This does not address the irreducible high-connectivity case. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.GraphTwoCut
open GraphSubdivision GraphIsoCore Critical EvenCore Rigidity
set_option maxHeartbeats 2400000
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

lemma split_even_iff (G : SimpleGraph V) {a b : V} (hp : G.Adj a b) :
    (∀ x, Even ((split G {()} a b).degree x)) ↔ (∀ x, Even (G.degree x)) := by
  rw [even_split_iff G _ hp.ne]
  exact and_iff_left (by simp [hp])

lemma split_number (G : SimpleGraph V) {a b : V}
    (hG : ∀ x, Even (G.degree x)) (hp : G.Adj a b) :
    number (split G {()} a b) = number G := by
  have h := number_subdivide G hG hp
  rwa [subdivide_eq_split G hp] at h

lemma split_minimal_iff (G : SimpleGraph V) {a b : V}
    (hG : ∀ x, Even (G.degree x)) (hp : G.Adj a b) :
    EvenMinimal (split G {()} a b) ↔ EvenMinimal G := by
  have h := minimal_subdivide_iff G hG hp
  rwa [subdivide_eq_split G hp] at h

lemma split_rigid_iff (G : SimpleGraph V) {a b : V}
    (hG : ∀ x, Even (G.degree x)) (hp : G.Adj a b) :
    CycleRigid (split G {()} a b) ↔ CycleRigid G := by
  have h := rigid_subdivide_iff G hG hp
  rwa [subdivide_eq_split G hp] at h

lemma even_expanded_iff (G : SimpleGraph V) (H : SimpleGraph W) {a b : V} {c d : W}
    (hsep : a ≠ b ∨ c ≠ d) :
    (∀ x, Even ((expanded G H a b c d).degree x)) ↔
      (∀ x, Even ((join G H a b c d).degree x)) := by
  exact (split_even_iff _ (port₄ G H a b c d)).trans
    ((split_even_iff _ (port₃ G H hsep)).trans
      ((split_even_iff _ (port₂ G H a b c d)).trans (split_even_iff _ (port₁ G H a b c d))))

lemma number_expanded (G : SimpleGraph V) (H : SimpleGraph W) {a b : V} {c d : W}
    (hsep : a ≠ b ∨ c ≠ d) (he : ∀ x, Even ((join G H a b c d).degree x)) :
    number (expanded G H a b c d) = number (join G H a b c d) := by
  have he₁ := (split_even_iff _ (port₁ G H a b c d)).mpr he
  have he₂ := (split_even_iff _ (port₂ G H a b c d)).mpr he₁
  have he₃ := (split_even_iff _ (port₃ G H hsep)).mpr he₂
  exact (split_number _ he₃ (port₄ G H a b c d)).trans
    ((split_number _ he₂ (port₃ G H hsep)).trans
      ((split_number _ he₁ (port₂ G H a b c d)).trans (split_number _ he (port₁ G H a b c d))))

lemma minimal_expanded_iff (G : SimpleGraph V) (H : SimpleGraph W) {a b : V} {c d : W}
    (hsep : a ≠ b ∨ c ≠ d) (he : ∀ x, Even ((join G H a b c d).degree x)) :
    EvenMinimal (expanded G H a b c d) ↔ EvenMinimal (join G H a b c d) := by
  have he₁ := (split_even_iff _ (port₁ G H a b c d)).mpr he
  have he₂ := (split_even_iff _ (port₂ G H a b c d)).mpr he₁
  have he₃ := (split_even_iff _ (port₃ G H hsep)).mpr he₂
  exact (split_minimal_iff _ he₃ (port₄ G H a b c d)).trans
    ((split_minimal_iff _ he₂ (port₃ G H hsep)).trans
      ((split_minimal_iff _ he₁ (port₂ G H a b c d)).trans (split_minimal_iff _ he (port₁ G H a b c d))))

lemma rigid_expanded_iff (G : SimpleGraph V) (H : SimpleGraph W) {a b : V} {c d : W}
    (hsep : a ≠ b ∨ c ≠ d) (he : ∀ x, Even ((join G H a b c d).degree x)) :
    CycleRigid (expanded G H a b c d) ↔ CycleRigid (join G H a b c d) := by
  have he₁ := (split_even_iff _ (port₁ G H a b c d)).mpr he
  have he₂ := (split_even_iff _ (port₂ G H a b c d)).mpr he₁
  have he₃ := (split_even_iff _ (port₃ G H hsep)).mpr he₂
  exact (split_rigid_iff _ he₃ (port₄ G H a b c d)).trans
    ((split_rigid_iff _ he₂ (port₃ G H hsep)).trans
      ((split_rigid_iff _ he₁ (port₂ G H a b c d)).trans (split_rigid_iff _ he (port₁ G H a b c d))))

lemma closures_even (G : SimpleGraph V) (H : SimpleGraph W) {a b : V} {c d : W}
    (hsep : a ≠ b ∨ c ≠ d) (he : ∀ x, Even ((join G H a b c d).degree x)) :
    (∀ x, Even ((closure G a b).degree x)) ∧ (∀ x, Even ((closure H c d).degree x)) := by
  have hex := (even_expanded_iff G H hsep).mpr he
  have hsw := even_iso (expansionIso G H hsep) hex
  have hs := (GraphSerial.even_switch_iff (closure G a b) (closure H c d)
    (closure_port G a b).ne (closure_port H c d).ne).mp hsw
  exact ⟨hs.1,hs.2.1⟩

lemma number_join (G : SimpleGraph V) (H : SimpleGraph W) {a b : V} {c d : W}
    (hsep : a ≠ b ∨ c ≠ d) (he : ∀ x, Even ((join G H a b c d).degree x)) :
    number (join G H a b c d) = number (closure G a b) + number (closure H c d) - 1 := by
  obtain ⟨hG,hH⟩ := closures_even G H hsep he
  calc
    _ = number (expanded G H a b c d) := (number_expanded G H hsep he).symm
    _ = number (switched G H a b c d) := BlockRestriction.number_eq_of_iso (expansionIso G H hsep)
    _ = _ := GraphSerial.number_switch _ _ hG hH (closure_port G a b) (closure_port H c d)

lemma minimal_join_iff (G : SimpleGraph V) (H : SimpleGraph W) {a b : V} {c d : W}
    (hsep : a ≠ b ∨ c ≠ d) (he : ∀ x, Even ((join G H a b c d).degree x)) :
    EvenMinimal (join G H a b c d) ↔ EvenMinimal (closure G a b) ∧ EvenMinimal (closure H c d) := by
  obtain ⟨hG,hH⟩ := closures_even G H hsep he
  exact (minimal_expanded_iff G H hsep he).symm.trans
    ((minimal_iso_iff (expansionIso G H hsep)).trans
      (GraphSerial.minimal_switch_iff _ _ hG hH (closure_port G a b) (closure_port H c d)))

lemma rigid_join_iff (G : SimpleGraph V) (H : SimpleGraph W) {a b : V} {c d : W}
    (hsep : a ≠ b ∨ c ≠ d) (he : ∀ x, Even ((join G H a b c d).degree x)) :
    CycleRigid (join G H a b c d) ↔ CycleRigid (closure G a b) ∧ CycleRigid (closure H c d) := by
  obtain ⟨hG,hH⟩ := closures_even G H hsep he
  have hex := (even_expanded_iff G H hsep).mpr he
  exact (rigid_expanded_iff G H hsep he).symm.trans
    ((rigid_iso_iff (expansionIso G H hsep) hex).trans
      (GraphSerial.rigid_switch_iff _ _ hG hH (closure_port G a b) (closure_port H c d)))

lemma nonrigid_minimal_join_factor (G : SimpleGraph V) (H : SimpleGraph W) {a b : V} {c d : W}
    (hsep : a ≠ b ∨ c ≠ d) (he : ∀ x, Even ((join G H a b c d).degree x))
    (hm : EvenMinimal (join G H a b c d)) (hn : ¬ CycleRigid (join G H a b c d)) :
    (EvenMinimal (closure G a b) ∧ ¬ CycleRigid (closure G a b)) ∨
      (EvenMinimal (closure H c d) ∧ ¬ CycleRigid (closure H c d)) := by
  obtain ⟨hmG,hmH⟩ := (minimal_join_iff G H hsep he).mp hm
  by_cases hrG : CycleRigid (closure G a b)
  · exact Or.inr ⟨hmH,fun hrH => hn ((rigid_join_iff G H hsep he).mpr ⟨hrG,hrH⟩)⟩
  · exact Or.inl ⟨hmG,hrG⟩

#print axioms number_join
#print axioms minimal_join_iff
#print axioms rigid_join_iff
#print axioms nonrigid_minimal_join_factor
end Erdos184Work.GraphTwoCut
