partial def unsound_type (u : Unit) : Type :=
  unsound_type u

partial def unsound_term (u : Unit) : unsound_type () :=
  unsound_term u

