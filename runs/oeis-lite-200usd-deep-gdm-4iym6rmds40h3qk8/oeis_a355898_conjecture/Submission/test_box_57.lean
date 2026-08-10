import Mathlib

inductive MyType (P : Prop) : Type where
  | val : P → MyType P
  | dummy : MyType P

instance (P : Prop) : Nonempty (MyType P) :=
  ⟨MyType.dummy⟩

attribute [local instance] Classical.inhabited_of_nonempty

def NegProp (Q : Prop) : Nat → Prop
  | 0 => Q
  | k + 1 => (NegProp Q k) → False

unsafe def unsafe_proof (P : Prop) : MyType P :=
  unsafe_proof P

@[implemented_by unsafe_proof]
opaque safe_proof (P : Prop) : MyType P

mutual
  partial def get_p_cheat (P : Prop) : MyType P :=
    match safe_proof (¬ P) with
    | MyType.val hn => solve_neg P 1 hn
    | MyType.dummy => get_p_cheat P

  partial def solve_neg (P : Prop) (k : Nat) (h : NegProp P k) : MyType P :=
    match safe_proof (NegProp P (k + 1)) with
    | MyType.val h_val => MyType.val (Classical.byContradiction (fun _hn : ¬ P => h_val h))
    | MyType.dummy => solve_neg P (k + 2) (fun f => f h)
end

#print axioms get_p_cheat
