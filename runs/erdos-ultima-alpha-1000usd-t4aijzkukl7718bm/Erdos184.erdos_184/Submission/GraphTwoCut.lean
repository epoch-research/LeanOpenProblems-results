import Submission.GraphIsoCore

/-! A two-edge cut with fresh closure vertices. Endpoints on either side may
coincide, and an internal edge between the endpoints is allowed. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.GraphTwoCut
open GraphSubdivision
set_option maxHeartbeats 2400000
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

/-- Join two graphs by the cross-edges `ac` and `bd`. -/
def join (G : SimpleGraph V) (H : SimpleGraph W) (a b : V) (c d : W) : SimpleGraph (V ⊕ W) where
  Adj
    | .inl x, .inl y => G.Adj x y
    | .inr x, .inr y => H.Adj x y
    | .inl x, .inr y => (x = a ∧ y = c) ∨ (x = b ∧ y = d)
    | .inr y, .inl x => (x = a ∧ y = c) ∨ (x = b ∧ y = d)
  symm := by
    intro x y h
    cases x <;> cases y
    · exact h.symm
    · exact h
    · exact h
    · exact h.symm
  loopless := by
    intro x
    cases x
    · exact G.loopless _
    · exact H.loopless _

/-- Close a side by the new path `a--false--true--b`.
If `a = b`, this path closes to a triangle. -/
def closure (G : SimpleGraph V) (a b : V) : SimpleGraph (V ⊕ Bool) where
  Adj
    | .inl x, .inl y => G.Adj x y
    | .inr x, .inr y => x ≠ y
    | .inl x, .inr y => (x = a ∧ y = false) ∨ (x = b ∧ y = true)
    | .inr y, .inl x => (x = a ∧ y = false) ∨ (x = b ∧ y = true)
  symm := by
    intro x y h
    cases x <;> cases y
    · exact h.symm
    · exact h
    · exact h
    · exact h.symm
  loopless := by
    intro x
    cases x
    · exact G.loopless _
    · exact fun h => h rfl

noncomputable instance (G : SimpleGraph V) (H : SimpleGraph W) (a b : V) (c d : W) :
    DecidableRel (join G H a b c d).Adj := Classical.decRel _
noncomputable instance (G : SimpleGraph V) (a b : V) : DecidableRel (closure G a b).Adj := Classical.decRel _

lemma closure_port (G : SimpleGraph V) (a b : V) :
    (closure G a b).Adj (.inr false) (.inr true) := Bool.false_ne_true

abbrev X₀ := V ⊕ W
abbrev X₁ := X₀ (V := V) (W := W) ⊕ Unit
abbrev X₂ := X₁ (V := V) (W := W) ⊕ Unit
abbrev X₃ := X₂ (V := V) (W := W) ⊕ Unit
abbrev X₄ := X₃ (V := V) (W := W) ⊕ Unit

abbrev step₁ (G : SimpleGraph V) (H : SimpleGraph W) (a b : V) (c d : W) : SimpleGraph (X₁ (V := V) (W := W)) :=
  split (join G H a b c d) {()} (.inl a) (.inr c)
abbrev step₂ (G : SimpleGraph V) (H : SimpleGraph W) (a b : V) (c d : W) : SimpleGraph (X₂ (V := V) (W := W)) :=
  split (step₁ G H a b c d) {()} (.inr ()) (.inl (.inr c))
abbrev step₃ (G : SimpleGraph V) (H : SimpleGraph W) (a b : V) (c d : W) : SimpleGraph (X₃ (V := V) (W := W)) :=
  split (step₂ G H a b c d) {()} (.inl (.inl (.inl b))) (.inl (.inl (.inr d)))
abbrev expanded (G : SimpleGraph V) (H : SimpleGraph W) (a b : V) (c d : W) : SimpleGraph (X₄ (V := V) (W := W)) :=
  split (step₃ G H a b c d) {()} (.inr ()) (.inl (.inl (.inl (.inr d))))

lemma port₁ (G : SimpleGraph V) (H : SimpleGraph W) (a b : V) (c d : W) :
    (join G H a b c d).Adj (.inl a) (.inr c) := Or.inl ⟨rfl,rfl⟩
lemma port₂ (G : SimpleGraph V) (H : SimpleGraph W) (a b : V) (c d : W) :
    (step₁ G H a b c d).Adj (.inr ()) (.inl (.inr c)) := by
  exact Or.inr ⟨rfl,by simp⟩
lemma port₃ (G : SimpleGraph V) (H : SimpleGraph W) {a b : V} {c d : W}
    (hsep : a ≠ b ∨ c ≠ d) :
    (step₂ G H a b c d).Adj (.inl (.inl (.inl b))) (.inl (.inl (.inr d))) := by
  change ((join G H a b c d).Adj (.inl b) (.inr d) ∧
      s(Sum.inl b,Sum.inr d) ≠ s(Sum.inl a,Sum.inr c)) ∧ _
  refine ⟨⟨Or.inr ⟨rfl,rfl⟩,?_⟩,?_⟩
  · intro he
    have he' : b = a ∧ d = c := by simpa [Sym2.eq_iff] using he
    rcases hsep with h | h
    · exact h he'.1.symm
    · exact h he'.2.symm
  · simp [Sym2.eq_iff]
lemma port₄ (G : SimpleGraph V) (H : SimpleGraph W) (a b : V) (c d : W) :
    (step₃ G H a b c d).Adj (.inr ()) (.inl (.inl (.inl (.inr d)))) := by
  exact Or.inr ⟨rfl,by simp⟩

def flatten : X₄ (V := V) (W := W) ≃ (V ⊕ Bool) ⊕ (W ⊕ Bool) where
  toFun
    | .inl (.inl (.inl (.inl (.inl v)))) => .inl (.inl v)
    | .inl (.inl (.inl (.inl (.inr w)))) => .inr (.inl w)
    | .inl (.inl (.inl (.inr _))) => .inl (.inr false)
    | .inl (.inl (.inr _)) => .inr (.inr false)
    | .inl (.inr _) => .inl (.inr true)
    | .inr _ => .inr (.inr true)
  invFun
    | .inl (.inl v) => .inl (.inl (.inl (.inl (.inl v))))
    | .inr (.inl w) => .inl (.inl (.inl (.inl (.inr w))))
    | .inl (.inr false) => .inl (.inl (.inl (.inr ())))
    | .inr (.inr false) => .inl (.inl (.inr ()))
    | .inl (.inr true) => .inl (.inr ())
    | .inr (.inr true) => .inr ()
  left_inv := by
    intro x
    rcases x with (((((v|w)|⟨⟩)|⟨⟩)|⟨⟩)|⟨⟩) <;> rfl
  right_inv := by
    intro x
    rcases x with (v|(_|_)) | (w|(_|_)) <;> rfl

abbrev switched (G : SimpleGraph V) (H : SimpleGraph W) (a b : V) (c d : W) :=
  GraphSerial.switch (closure G a b) (closure H c d) (.inr false) (.inr true) (.inr false) (.inr true)

noncomputable def expansionIso (G : SimpleGraph V) (H : SimpleGraph W) {a b : V} {c d : W}
    (hsep : a ≠ b ∨ c ≠ d) : expanded G H a b c d ≃g switched G H a b c d where
  toEquiv := flatten
  map_rel_iff' := by
    intro x y
    have hport : (step₂ G H a b c d).Adj (.inl (.inl (.inl b))) (.inl (.inl (.inr d))) := port₃ G H hsep
    have hfirst := port₁ G H a b c d
    rcases x with (((((x|x)|⟨⟩)|⟨⟩)|⟨⟩)|⟨⟩) <;>
      rcases y with (((((y|y)|⟨⟩)|⟨⟩)|⟨⟩)|⟨⟩) <;>
      simp [flatten,switched,GraphSerial.switch,closure,expanded,step₃,step₂,step₁,split,join,
        Sym2.eq_iff] <;> tauto

#print axioms expansionIso
end Erdos184Work.GraphTwoCut
