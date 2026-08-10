open Classical

inductive T : Type 1 where
  | base : T
  | mk : ((Type → Prop) → Prop) → T

-- Since T is in Type 1, any subtype of T is in Type 1.
-- But wait!
-- Can we define a subtype of ULift T?
-- ULift T is in Type!
-- So { x : ULift T // x = ULift.up t } is in Type!
-- Let's check!
def encode (t : T) : Type := { x : ULift T // x = ULift.up t }
