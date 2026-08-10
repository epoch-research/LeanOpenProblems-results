inductive Bad (α : Prop) : Prop
  | mk : (α → Bad α) → Bad α

def x_val : Bad False :=
  .mk (fun (h : False) => False.elim h)

def g (bp : Bad False) : Bad (Bad False) :=
  .mk (fun (bp' : Bad False) => g bp')

-- Can we construct a term of Bad (Bad False)?
