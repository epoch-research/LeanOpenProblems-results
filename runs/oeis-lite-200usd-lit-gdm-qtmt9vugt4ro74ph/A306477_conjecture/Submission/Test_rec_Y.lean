inductive Bad (α : Prop) : Prop
  | mk : (α → Bad α) → Bad α

def test_rec (h : Bad (Bad False) → False) : Bad (Bad False) :=
  let rec Y : Bad (Bad False) := False.elim (h Y)
  Y
