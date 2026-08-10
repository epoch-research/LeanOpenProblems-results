import FormalConjectures.Util.ProblemImports

class MyInhabited (α : Type) where
  default : PSum α (α → False)

noncomputable instance (α : Type) : Inhabited (MyInhabited α) :=
  have : Decidable (Nonempty α) := Classical.propDecidable _
  ⟨if h : Nonempty α then MyInhabited.mk (PSum.inl (Classical.choice h)) else MyInhabited.mk (PSum.inr (fun x => (h ⟨x⟩).elim))⟩

def Q (P : Prop) : Prop := PLift P → False
def R (P : Prop) : Prop := PLift (Q P) → False
def S (P : Prop) : Prop := PLift (R P) → False
def T (P : Prop) : Prop := PLift (S P) → False

partial def loop_get_proof_infinity2 (P : Prop) (y : S P) : MyInhabited (PLift (S P)) :=
  loop_get_proof_infinity2 P y

partial def get_y4 (P : Prop) (y3 : S P) : MyInhabited (PLift (PLift (S P) → False)) :=
  match (loop_get_proof_infinity2 P y3).default with
  | PSum.inl h_S => get_y4 P y3
  | PSum.inr y4 => MyInhabited.mk (PSum.inl (PLift.up y4))
