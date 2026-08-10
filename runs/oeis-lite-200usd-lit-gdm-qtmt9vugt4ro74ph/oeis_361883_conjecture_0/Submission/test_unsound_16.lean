inductive Bad : Type → Type 1
  | mk1 : α → Bad α
  | mk2 : Bad (α → PEmpty) → Bad α

def val : (α : Type) → Bad α → Type
  | α, mk1 g => (α → PEmpty) → PEmpty
  | α, mk2 z => val (α → PEmpty) z

def prove_val : (α : Type) → (t : Bad α) → val α t
  | α, mk1 g => fun h => h g
  | α, mk2 z => prove_val (α → PEmpty) z
