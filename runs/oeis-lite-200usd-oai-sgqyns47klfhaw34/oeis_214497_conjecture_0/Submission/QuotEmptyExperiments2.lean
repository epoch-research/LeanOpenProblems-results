import FormalConjectures.Util.ProblemImports

inductive EmptyRel : Empty → Empty → Prop
abbrev QE := Quot EmptyRel

example : ¬ Nonempty QE := by
  rintro ⟨q⟩
  exact Quot.ind (motive := fun _ => False) (fun e => Empty.elim e) q

example (P : Prop) : QE → P := by
  intro q
  exact Quot.ind (motive := fun _ => P) (fun e => Empty.elim e) q

example (P : Prop) : P := by
  have hne : ¬ Nonempty QE := by
    rintro ⟨q⟩
    exact Quot.ind (motive := fun _ => False) (fun e => Empty.elim e) q
  exact? 
