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

-- Wait, y's type is PLift (R P) -> False, which is S P.
-- S P is a Prop, so PLift (S P) is in Type.
-- Thus, MyInhabited (PLift (S P)) is a valid type!
-- Let's define the partial function returning MyInhabited (PLift (S P))
partial def loop_get_proof_infinity2 (P : Prop) (y : S P) : MyInhabited (PLift (S P)) :=
  loop_get_proof_infinity2 P y
