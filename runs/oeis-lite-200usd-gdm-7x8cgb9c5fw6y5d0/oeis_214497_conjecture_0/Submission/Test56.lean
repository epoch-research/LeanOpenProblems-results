import FormalConjectures.Util.ProblemImports

noncomputable instance (P : Prop) : Nonempty (PLift P) :=
  have : Decidable (Nonempty (PLift P)) := Classical.propDecidable _
  if h : Nonempty (PLift P) then h else ⟨unsafeCast ()⟩
