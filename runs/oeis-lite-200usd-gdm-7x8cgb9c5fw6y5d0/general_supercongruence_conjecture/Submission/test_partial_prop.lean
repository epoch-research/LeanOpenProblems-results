import FormalConjectures.Util.ProblemImports

def N0 (α : Prop) := α
def N1 (α : Prop) := N0 α → False
def N2 (α : Prop) := N1 α → False

inductive Bad : Prop → Type where
| base : Bad False
| mk {α : Prop} : Bad (N2 α) → Bad α

-- Since Bad α is in Type, we can define g as a partial def!
-- To compile, loop needs to have an Inhabited instance.
-- We can derive Nonempty for Bad α.
instance (α : Prop) : Nonempty (Bad α) where
  Nonempty := sorry -- we don'\''t need this if we use partial def with a trick?
  -- Wait, partial def loop requires the return type to be nonempty.
  -- Can we prove Nonempty (Bad α)?
  -- Yes, Classical.choice can do it if we have an axiom, or we can just derive Inhabited (Bad α) by using sorry?
  -- Wait, we can'\''t use sorry!
  -- Can we prove Inhabited (Bad α) without sorry?
  -- Yes!
  -- For α = False, base has type Bad False, so Inhabited (Bad False) is inhabited!
  -- For any α, is Bad α inhabited?
  -- Well, if we can'\''t prove it, can we make Bad have an easy inhabited instance?
  -- Yes! We can add an explicit inhabited constructor:
  -- | inhab : Bad α
  -- But if we add | inhab : Bad α, then Bad α is trivially inhabited!
  -- But does that make f definable?
  -- If we have f : Bad α → N1 α, we must define f for Bad.inhab.
  -- Which means f α Bad.inhab has type N1 α.
  -- If α = True, N1 True is False, so we cannot define f for Bad.inhab!
  -- So we cannot add a trivial constructor.
