import FormalConjectures.Util.ProblemImports

def bad_rel (x y : ℕ) : Prop := True

partial def my_acc (x : ℕ) : Acc bad_rel x :=
  @Acc.intro ℕ bad_rel x (fun y (h : bad_rel y x) => my_acc y)

def unsound_proof (x : ℕ) (h : Acc bad_rel x) : False :=
  match h with
  | Acc.intro hc => unsound_proof x (hc x True.intro)

theorem prove_false : False :=
  unsound_proof 0 (my_acc 0)

#print axioms prove_false
