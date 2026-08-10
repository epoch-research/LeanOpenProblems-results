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

def unsound : PEmpty :=
  let t1 : Bad (PEmpty → PEmpty) := Bad.mk1 (fun x => x)
  let t2 : Bad ((PEmpty → PEmpty) → PEmpty) := Bad.mk2 t1
  let h1 : val t1 := prove_val _ t1
  let h2 : val t2 := prove_val _ t2
  let rec f : val t1 → PEmpty := fun g =>
    g (fun x => g (fun y => x (y (f g))))
  h2 f
