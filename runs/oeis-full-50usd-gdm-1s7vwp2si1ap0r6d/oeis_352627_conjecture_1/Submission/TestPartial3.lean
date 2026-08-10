partial def unsound_type (u : Unit) : Type :=
  unsound_type u

partial def unsound_instance (u : Unit) : Inhabited (unsound_type ()) :=
  unsound_instance u

instance : Inhabited (unsound_type ()) := unsound_instance ()

partial def unsound_term (u : Unit) : unsound_type () :=
  unsound_term u

-- unsound_term () has type unsound_type ()
