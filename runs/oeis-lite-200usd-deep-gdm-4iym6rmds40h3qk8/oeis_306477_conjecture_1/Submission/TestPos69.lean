open Classical

def U : Prop := ∀ p : Prop, ((p → Prop) → Prop) → p

-- Let's define the projection map
-- app : U → ((U → Prop) → Prop)
noncomputable def app (u : U) : ((U → Prop) → Prop) :=
  -- u is ∀ p, ((p → Prop) → Prop) → p
  -- We want to return a term of ((U → Prop) → Prop).
  -- This is a function of type (U → Prop) → Prop.
  -- Let's take `H : U → Prop`. We want to return a Prop.
  -- Can we return `u Prop (fun (g : (Prop → Prop) → Prop) => ...)` ?
  -- If we instantiate `u` with `U`, we get:
  --   u U : ((U → Prop) → Prop) → U
  -- Wait! `u U` takes a term of ((U → Prop) → Prop) and returns U!
  -- This doesn't help us get a Prop from `H : U → Prop`.
  -- Wait! What if we instantiate `u` with `Prop`?
  --   u Prop : ((Prop → Prop) → Prop) → Prop
  -- Let's see: if we take `H : U → Prop`. We can define a map `U_to_Prop : U → Prop`? No, H is `U → Prop`.
  -- Can we define `app u H : Prop`?
  -- Yes! We can define:
  --   app u H := u Prop (fun (g : Prop → Prop) => H (fun p f => f (fun h => g (h p f))))
  -- Let's check if this is type correct!
  fun H => u Prop (fun (g : Prop → Prop) => H (fun p f => f (fun h => g (h p f))))
