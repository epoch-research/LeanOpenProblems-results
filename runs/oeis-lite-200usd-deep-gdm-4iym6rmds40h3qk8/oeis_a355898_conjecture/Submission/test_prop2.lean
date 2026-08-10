def MyProp : Prop := False

partial def get_nonempty_spec (u : Unit) : Nonempty MyProp :=
  get_nonempty_spec u
