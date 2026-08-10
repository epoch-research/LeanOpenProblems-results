import FormalConjectures.Util.ProblemImports

def N0 (α : Type) := α
def N1 (α : Type) := N0 α → Empty
def N2 (α : Type) := N1 α → Empty

inductive Bad : Type → Type where
| base {α : Type} : N1 α → Bad α
| mk {α : Type} : Bad (N2 α) → Bad α

-- Since Bad α is inhabited (for any α for which we can construct N1 α, or generally),
-- we can prove it is nonempty/inhabited.
instance {α : Type} [Inhabited (N1 α)] : Inhabited (Bad α) where
  default := Bad.base default

-- Wait, can we compile partial def g?
partial def g (α : Type) : Bad α :=
  Bad.mk (g (N2 α))

open Classical

noncomputable def f : (α : Type) → Bad α → N1 α
| _, Bad.base ha => ha
| _, @Bad.mk α' h =>
  let recurse := f (N2 α') h
  fun (h0 : α') =>
    -- recurse has type N1 (N2 α') which is N2 α' → Empty.
    -- h0 has type α'.
    -- We can construct a term of type N2 α' (which is N1 α' → Empty):
    let p_n2 : N2 α' := fun (h_n1 : N1 α') => h_n1 h0
    -- So recurse p_n2 has type Empty!
    recurse p_n2

theorem false_proof : False := by
  have bad_empty : Bad Empty := g Empty
  have f_res : N1 Empty := f Empty bad_empty
  -- N1 Empty is Empty → Empty.
  -- To get Empty, we need a term of type Empty.
  -- Wait!
  -- How do we get a term of type Empty from f_res?
  -- We still need an Empty to apply f_res to!
  sorry

#print axioms false_proof
