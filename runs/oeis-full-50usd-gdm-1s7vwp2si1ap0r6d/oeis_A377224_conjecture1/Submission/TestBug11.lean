def U : Type 1 := Type

def Power (A : Type 1) : Type 1 := A → Prop

def i (P : Power (Power U)) : U :=
  ∀ (p : Prop), (∀ (x : U), P x → x) → p
