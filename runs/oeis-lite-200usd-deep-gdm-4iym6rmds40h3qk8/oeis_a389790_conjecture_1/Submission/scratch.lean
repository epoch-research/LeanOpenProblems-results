import FormalConjectures.Util.ProblemImports

set_option autoImplicit false

def R (x y : Unit) : Prop := True

inductive Bad : Prop where
  | mk : {x : Prop} → (x = (True = False)) → {y : Prop} → Quot R → Bad

inductive Bad_pred : Bad → Prop → Prop where
  | mk : ∀ {x : Prop} (heq : x = (True = False)) {y : Prop} (q : Quot R), Bad_pred (@Bad.mk x heq y q) y

theorem bad_pred_functional {b : Bad} {p1 p2 : Prop} (h1 : Bad_pred b p1) (h2 : Bad_pred b p2) : p1 = p2 := by
  cases h1
  cases h2
  rfl

def b0 : Bad := @Bad.mk (True = False) rfl True (Quot.mk _ ())
def b1 : Bad := @Bad.mk (True = False) rfl False (Quot.mk _ ())

theorem unsound_false : False := by
  have h1 : Bad_pred b0 True := Bad_pred.mk rfl (Quot.mk _ ())
  have h2 : Bad_pred b1 False := Bad_pred.mk rfl (Quot.mk _ ())
  have h_eq : True = False := bad_pred_functional h1 h2
  exact h_eq.mp trivial


