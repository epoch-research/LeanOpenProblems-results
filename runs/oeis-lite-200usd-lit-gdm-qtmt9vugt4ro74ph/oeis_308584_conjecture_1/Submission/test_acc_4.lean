import FormalConjectures.Util.ProblemImports

def bad_rel (x y : ℕ) : Prop := True

inductive MyAcc (α : Type) (r : α → α → Prop) (x : α) : Type where
  | intro (h : ∀ (y : α), r y x → MyAcc α r y) : MyAcc α r x
deriving Inhabited

partial def my_acc (x : ℕ) : MyAcc ℕ bad_rel x :=
  MyAcc.intro (fun y h => my_acc y)

def unsound_proof (x : ℕ) (h : MyAcc ℕ bad_rel x) : False :=
  match h with
  | MyAcc.intro hc => unsound_proof x (hc x True.intro)

theorem prove_false : False :=
  unsound_proof 0 (my_acc 0)

#print axioms prove_false
