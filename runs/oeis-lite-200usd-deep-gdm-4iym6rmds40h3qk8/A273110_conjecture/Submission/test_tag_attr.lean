import Lean

open Lean Elab Command

-- We can't registerBuiltinAttribute because it's only active in the next file.
-- But can we register a standard attribute?
-- Actually, registerTagAttribute has the type:
-- Name → String → IO Unit
-- It doesn't have an `add` field where we can run custom CommandElabM/CoreM code.
-- The only attribute constructor with an `add` field is `AttributeImpl`, which must be registered using `registerBuiltinAttribute` or `registerAttributeOfBuilder`.
