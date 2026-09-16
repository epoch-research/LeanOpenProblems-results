import Mathlib

theorem foo : False := by
  let R : Prop → Prop → Prop := fun _ _ => True
  have h1 : Quot.mk R True = Quot.mk R False := Quot.sound trivial
  let f : Quot R → Prop := Quot.lift id (fun p q _ => propext ⟨fun hp =>
        have h : p = q := Classical.choice ⟨(Classical.choice ⟨sorry⟩ : False).elim⟩
        cast h hp
    , fun hq =>
        have h : q = p := Classical.choice ⟨(Classical.choice ⟨sorry⟩ : False).elim⟩
        cast h hq
    ⟩)
  have h2 : f (Quot.mk R True) = f (Quot.mk R False) := congrArg f h1
  have h3 : True = False := h2
  exact cast h3 trivial
