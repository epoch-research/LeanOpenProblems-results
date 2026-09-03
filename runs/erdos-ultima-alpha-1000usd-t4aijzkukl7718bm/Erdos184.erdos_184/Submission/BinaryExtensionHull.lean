import Submission.SerialMinimum

/-!
A one-generator extension preserves the circuit-partition hull up to one when
it breaks a series pair. This is a restricted case, not the arbitrary extension
inequality and not a settlement of Erdős 184.
-/
open scoped Classical symmDiff
namespace Erdos184Serial.BinaryExtension

set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false

variable {E : Type*} [DecidableEq E]

/-- A uniform bound on the minimum partition number of every valid support. -/
def HullBound (C : Code E) (n : ℕ) : Prop :=
  ∀ s, C.valid s → ∃ D, Partition C s D ∧ D.card ≤ n

/-- Source coordinates which agree on every codeword. -/
def SeriesPair (C : Code E) (a b : E) : Prop :=
  ∀ s, C.valid s → (a ∈ s ↔ b ∈ s)

/-- The word set obtained by adjoining the coset of `z`. -/
def ExtensionBy (C B : Code E) (z : Finset E) : Prop :=
  ∀ s, B.valid s ↔ C.valid s ∨ C.valid (s ∆ z)

/-- Binary closure, stronger than the difference closure of `Code`. -/
def XorClosed (C : Code E) : Prop :=
  ∀ s t, C.valid s → C.valid t → C.valid (s ∆ t)

/-- An actual code extension when the source is XOR-closed. -/
def extend (C : Code E) (hC : XorClosed C) (z : Finset E) : Code E where
  valid s := C.valid s ∨ C.valid (s ∆ z)
  empty := Or.inl C.empty
  diff := by
    intro s t hs ht hts
    have h1 : s ∆ (t ∆ z) = (s \ t) ∆ z := by
      ext x
      have hh : x ∈ t → x ∈ s := fun hx => hts hx
      simp only [Finset.mem_symmDiff, Finset.mem_sdiff]
      tauto
    have h2 : (s ∆ z) ∆ t = (s \ t) ∆ z := by
      ext x
      have hh : x ∈ t → x ∈ s := fun hx => hts hx
      simp only [Finset.mem_symmDiff, Finset.mem_sdiff]
      tauto
    have h3 : (s ∆ z) ∆ (t ∆ z) = s \ t := by
      ext x
      have hh : x ∈ t → x ∈ s := fun hx => hts hx
      simp only [Finset.mem_symmDiff, Finset.mem_sdiff]
      tauto
    rcases hs with hs | hs <;> rcases ht with ht | ht
    · exact Or.inl (C.diff hs ht hts)
    · exact Or.inr (h1 ▸ hC _ _ hs ht)
    · exact Or.inr (h2 ▸ hC _ _ hs ht)
    · exact Or.inl (h3 ▸ hC _ _ hs ht)

lemma extend_extensionBy (C : Code E) (hC : XorClosed C) (z : Finset E) :
    ExtensionBy C (extend C hC z) z := fun _ => Iff.rfl

/-- Equality of the two word sets restricted to a specified support. -/
def AgreeOn (C B : Code E) (s : Finset E) : Prop :=
  ∀ t ⊆ s, C.valid t ↔ B.valid t

lemma AgreeOn.circuit_iff {C B : Code E} {s t : Finset E}
    (h : AgreeOn C B s) (ht : t ⊆ s) : Circuit C t ↔ Circuit B t := by
  constructor
  · rintro ⟨hc, hn, hm⟩
    refine ⟨(h t ht).mp hc, hn, ?_⟩
    intro u hut hu hun
    exact hm u hut ((h u (hut.trans ht)).mpr hu) hun
  · rintro ⟨hc, hn, hm⟩
    refine ⟨(h t ht).mpr hc, hn, ?_⟩
    intro u hut hu hun
    exact hm u hut ((h u (hut.trans ht)).mp hu) hun

lemma AgreeOn.partition_iff {C B : Code E} {s : Finset E}
    (h : AgreeOn C B s) (D : Finset (Finset E)) :
    Partition C s D ↔ Partition B s D := by
  constructor
  · intro hD
    exact ⟨fun t ht => (h.circuit_iff (hD.piece_subset ht)).mp (hD.1 t ht), hD.2⟩
  · intro hD
    exact ⟨fun t ht => (h.circuit_iff (hD.piece_subset ht)).mpr (hD.1 t ht), hD.2⟩

lemma AgreeOn.hasNumber_iff {C B : Code E} {s : Finset E}
    (h : AgreeOn C B s) (n : ℕ) : HasNumber C s n ↔ HasNumber B s n := by
  simp only [HasNumber, h.partition_iff]

lemma ExtensionBy.source_valid {C B : Code E} {z s : Finset E}
    (h : ExtensionBy C B z) (hs : C.valid s) : B.valid s :=
  (h s).mpr (Or.inl hs)

/-- A new word cannot avoid both coordinates of a broken source series pair. -/
lemma ExtensionBy.agreeOn_of_avoids {C B : Code E} {z s : Finset E} {a b : E}
    (h : ExtensionBy C B z) (hp : SeriesPair C a b)
    (hz : ¬ (a ∈ z ↔ b ∈ z)) (ha : a ∉ s) (hb : b ∉ s) :
    AgreeOn C B s := by
  intro t hts
  constructor
  · exact h.source_valid
  · intro ht
    rcases (h t).mp ht with ht | ht
    · exact ht
    · have hat : a ∉ t := fun hm => ha (hts hm)
      have hbt : b ∉ t := fun hm => hb (hts hm)
      have he := hp (t ∆ z) ht
      have : a ∈ z ↔ b ∈ z := by
        simpa only [Finset.mem_symmDiff, hat, hbt, false_and, not_false_eq_true,
          and_true, false_or] using he
      exact (hz this).elim

/-- The one-generator hull inequality whenever a source series pair is broken. -/
theorem hullBound_of_broken_seriesPair {C B : Code E} {z : Finset E} {a b : E}
    (h : ExtensionBy C B z) (hp : SeriesPair C a b)
    (hz : ¬ (a ∈ z ↔ b ∈ z)) {n : ℕ} (hB : HullBound B n) :
    HullBound C (n + 1) := by
  intro s hs
  by_cases ha : a ∈ s
  · obtain ⟨D, hD⟩ := exists_partition C hs
    have ha' := ha
    rw [← hD.2.2] at ha'
    obtain ⟨A, hAD, haA⟩ := Finset.mem_biUnion.mp ha'
    change a ∈ A at haA
    have hbA : b ∈ A := (hp A (hD.1 A hAD).1).mp haA
    have hrest : C.valid (s \ A) := C.diff hs (hD.1 A hAD).1 (hD.piece_subset hAD)
    have hagree : AgreeOn C B (s \ A) := h.agreeOn_of_avoids hp hz
      (by simp [haA]) (by simp [hbA])
    obtain ⟨R, hR, hn⟩ := hB (s \ A) (h.source_valid hrest)
    have hR' := (hagree.partition_iff R).mpr hR
    have hd : Disjoint A (s \ A) := by
      apply Finset.disjoint_left.mpr
      intro x hx hy
      exact (Finset.mem_sdiff.mp hy).2 hx
    obtain ⟨hP, hcard⟩ := (partition_singleton (hD.1 A hAD)).join hR' hd
    rw [Finset.union_sdiff_of_subset (hD.piece_subset hAD)] at hP
    refine ⟨_, hP, ?_⟩
    simp only [Finset.card_singleton] at hcard
    omega
  · have hb : b ∉ s := fun hbs => ha ((hp s hs).mpr hbs)
    have hagree := h.agreeOn_of_avoids hp hz ha hb
    obtain ⟨D, hD, hn⟩ := hB s (h.source_valid hs)
    exact ⟨D, (hagree.partition_iff D).mpr hD, by omega⟩

/-- Any failure of the unrestricted inequality must preserve all source series
pairs. This excludes broken series extensions, not the remaining cosimple case. -/
theorem preserves_seriesPairs_of_failure {C B : Code E} {z : Finset E}
    (h : ExtensionBy C B z) {n : ℕ} (hB : HullBound B n)
    (hC : ¬ HullBound C (n + 1)) :
    ∀ a b, SeriesPair C a b → (a ∈ z ↔ b ∈ z) := by
  intro a b hp
  by_contra hz
  exact hC (hullBound_of_broken_seriesPair h hp hz hB)

#print axioms extend
#print axioms hullBound_of_broken_seriesPair
#print axioms preserves_seriesPairs_of_failure

end Erdos184Serial.BinaryExtension
