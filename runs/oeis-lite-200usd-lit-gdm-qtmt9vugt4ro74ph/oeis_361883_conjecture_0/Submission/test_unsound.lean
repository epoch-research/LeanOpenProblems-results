inductive Bad : Type u → Type (u+1)
  | mk1 {α : Type u} : α → Bad α
  | mk2 {α : Type u} : Bad α → Bad (α → PEmpty.{u+1})

def val {α : Type u} (t : Bad α) : Type u :=
  match t with
  | @Bad.mk1 _ g => (α → PEmpty.{u+1}) → PEmpty.{u+1}
  | @Bad.mk2 β z => (val z → PEmpty.{u+1}) → PEmpty.{u+1}

def prove_val : (α : Type u) → (t : Bad α) → val t
  | α, @Bad.mk1 _ g => fun h => h g
  | _, @Bad.mk2 β z => fun h => h (prove_val β z)

def unsound (α : Type u) : α :=
  let h1 : Bad (α → PEmpty.{u+1}) := Bad.mk2 (Bad.mk1 (fun _ => PEmpty.elim (unsound PEmpty)))
  let h2 : val h1 := prove_val _ h1
  let h3 : (val (Bad.mk1 (fun _ => PEmpty.elim (unsound PEmpty))) → PEmpty.{u+1}) → PEmpty.{u+1} := h2
  let h4 : val (Bad.mk1 (fun _ => PEmpty.elim (unsound PEmpty))) := prove_val _ (Bad.mk1 (fun _ => PEmpty.elim (unsound PEmpty)))
  let h6 : PEmpty.{u+1} := h3 h4
  PEmpty.elim h6
