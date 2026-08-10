inductive Unsound : Prop
| mk : (Type 0 → Unsound) → Unsound

class InhabitedUnsound where
  val : Unsound

instance inst : InhabitedUnsound where
  val := Unsound.mk (fun X => inst.val)


