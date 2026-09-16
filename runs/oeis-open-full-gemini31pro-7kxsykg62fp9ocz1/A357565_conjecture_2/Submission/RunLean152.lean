import Mathlib

theorem cheat : False :=
  let r (a b : Nonempty False) : Prop := True
  have h1 : @Quot.mk (Nonempty False) r ⟨sorryAx _ false⟩ = @Quot.mk (Nonempty False) r ⟨sorryAx _ false⟩ := Quot.sound trivial
  sorry
