import Mathlib

variable (P : Prop)

def r (a b : Bool) : Prop := P

def S : Prop := ∃ q : Quot (r P), q = Quot.mk (r P) true ∨ q = Quot.mk (r P) false

def proof1 : S P := ⟨Quot.mk (r P) true, Or.inl rfl⟩
def proof2 : S P := ⟨Quot.mk (r P) false, Or.inr rfl⟩

theorem proof_eq : proof1 P = proof2 P := rfl

