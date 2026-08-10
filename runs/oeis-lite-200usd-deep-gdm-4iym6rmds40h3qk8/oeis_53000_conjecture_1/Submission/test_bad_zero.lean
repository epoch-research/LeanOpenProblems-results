inductive Bad_zero : Type 1
| mk : (Bad_zero → Type 0) → Bad_zero
| base : Bad_zero

def decomp : Bad_zero → (Bad_zero → Type 0)
| Bad_zero.base => fun _ => PLift True
| Bad_zero.mk f => f

def lam (f : Bad_zero → Type 0) : Bad_zero := Bad_zero.mk f

def app (u : Bad_zero) : Bad_zero → Type 0 := decomp u

theorem beta (f : Bad_zero → Type 0) : app (lam f) = f := rfl
