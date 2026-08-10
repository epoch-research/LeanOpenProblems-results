import FormalConjectures.Util.ProblemImports

noncomputable theorem out_all_eq (P : Prop) : Quot.out (Quot.mk (fun _ _ : Prop => True) P) = P := by
  -- maybe quotient out representative equals original? likely false/unprovable
  have h := Quot.out_eq (Quot.mk (fun _ _ : Prop => True) P)
  -- h : mk (out (mk P)) = mk P
  -- Quot.eq unavailable for Prop quotient because type Prop not Type? check
  -- exact ?_
  sorry

noncomputable theorem bad (P : Prop) : P := by
  let r : Prop → Prop → Prop := fun _ _ => True
  let qP : Quot r := Quot.mk r P
  let qT : Quot r := Quot.mk r True
  have hq : qP = qT := Quot.sound True.intro
  have ht : Quot.out qT := by
    -- if out qT=True maybe
    -- rw [show Quot.out qT = True from ?_]
    sorry
  have hpout : Quot.out qP := by simpa [hq] using ht
  -- need Quot.out qP = P
  sorry
#print axioms bad
