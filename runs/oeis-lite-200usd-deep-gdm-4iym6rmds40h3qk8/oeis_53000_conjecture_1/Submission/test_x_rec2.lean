inductive Bad4 : Type 1
| mk1 : (Type 0 → Bad4) → Bad4
| base : Bad4

def X : Bad4 → Type 0
| Bad4.base => PLift True
| Bad4.mk1 f => PLift (¬ Nonempty (X (f (X (Bad4.mk1 f)))))
