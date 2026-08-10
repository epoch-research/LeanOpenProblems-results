def r (A B : Type 1) : Prop := A = B

def MyCast (q : Quot r) : Type 1 :=
  Quot.lift (fun T => T) (fun A B h => h) q

inductive G : (α : Type 1) → (β : Type) → Prop where
  | mk (α : Type 1) (β : Type) (x : α) (eq : Quot.mk r α = Quot.mk r Type) (z : cast (congrArg MyCast eq) x) : G α β

inductive Unsound : Prop where
  | mk : G (Unsound → Type) Empty → Unsound
