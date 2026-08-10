import FormalConjectures.Util.ProblemImports

namespace QuotTypeFamily

def Q := Quot (fun (_ _ : Type) => True)

inductive Fam : Q → Type where
| mk (α : Type) (a : α) : Fam (Quot.mk _ α)

def famEmpty : Fam (Quot.mk _ Empty) := by
  have hq : Quot.mk (fun (_ _ : Type) => True) PUnit = Quot.mk _ Empty := Quot.sound trivial
  exact hq ▸ Fam.mk PUnit PUnit.unit

-- Try extraction.
def extract (α : Type) : Fam (Quot.mk _ α) → α := by
  intro f
  cases f with
  | mk β b => exact b

example : Empty := extract Empty famEmpty
example : False := nomatch (extract Empty famEmpty)

#print axioms famEmpty
#print axioms extract
end QuotTypeFamily
