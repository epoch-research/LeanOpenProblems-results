inductive Unsound : Prop
| mk : (Prop → Unsound) → Unsound

theorem unsound_eq : Unsound ↔ (Prop → Unsound) := by
  constructor
  · intro u
    cases u with
    | mk f => exact f
  · exact Unsound.mk

open Classical

theorem unsound_eq_prop : Unsound = (Prop → Unsound) :=
  propext unsound_eq

def f_up : Unsound → (Prop → Unsound) := cast unsound_eq_prop
def f_down : (Prop → Unsound) → Unsound := cast unsound_eq_prop.symm

theorem f_up_down (x : Prop → Unsound) : f_up (f_down x) = x := rfl

-- Now we can construct Hurkens' paradox on Prop!
-- Let's define the retraction on Prop:
-- U = Unsound, sb = Prop → Prop
-- Since U is a Prop, and Prop → Unsound is also a Prop, they are equal.
-- We want a retraction between sb (Prop → Prop) and U (Unsound).
-- Let's define:
-- inj : Prop → Unsound
-- proj : Unsound → Prop
-- Actually, since Unsound = (Prop → Unsound), we can define:
-- decomp : Unsound → (Prop → Unsound) := f_up
-- lam : (Prop → Unsound) → Unsound := f_down
--
-- Now we want a retraction between Prop and Unsound!
-- Can we define:
-- inj (p : Prop) : Unsound := f_down (fun _ => f_down (fun _ => f_down (fun _ => ...))) -- no, we need it to be a retraction!
-- Wait! In test_retraction3.lean, we defined:
-- inj (p : Prop) : Unsound := if p then Unsound.mk (fun _ => Unsound.mk (fun _ => Unsound.base)) else Unsound.base
-- But that Unsound was in Type 0. Here, Unsound is in Prop.
-- Since Unsound is in Prop, we cannot do large elimination!
-- But wait! We don't need large elimination to define inj!
-- inj : Prop → Unsound. Since Unsound is in Prop, inj is a function from Prop to Prop.
-- So we can define inj using normal logic, if-then-else, etc.!
-- Let's see:
-- inj (p : Prop) : Unsound := f_down (fun _ => if p then f_down (fun _ => f_down (fun _ => ...)) else ...) -- wait, if p is Prop, then "if p then ... else ..." is just a Prop!
-- Wait, "if p then A else B" has type Unsound (which is a Prop) if A and B have type Unsound!
-- Since Unsound is a Prop, "if p then A else B" is just a Prop, which is perfectly valid!
-- And since Unsound has constructors, can we define a base term of Unsound?
-- Actually, since Unsound doesn't have a base constructor (it only has mk : (Prop → Unsound) → Unsound),
-- we can still define Unsound terms!
-- For example, `f_down (fun _ => f_down (fun _ => ...))`? No, we don't have a base case.
27	-- Wait, is Unsound inhabited? We don't need it to be inhabited statically, we can define inj and proj!
28	-- But wait, to define inj:
29	-- inj (p : Prop) : Unsound := if p then f_down (fun _ => f_down (fun _ => ...)) else ...
30	-- Wait, can we define inj using a parameter?
31	-- Let's try!
