open Classical

inductive T : Type 1 where
  | base : T

def MyType (t : T) : Type := ULift ({ x : T // x = t })
