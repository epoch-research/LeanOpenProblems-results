inductive Unsound : Prop
| mk : (Prop → Unsound) → Unsound

def val : Unsound → False
| Unsound.mk f => val (f (val (f True) = val (f True)))

partial def unsound_plift (u : Unit) : PLift Unsound :=
  PLift.up (Unsound.mk (fun p => unsound_plift u |>.down))

theorem unsound : False :=
  val (unsound_plift ()).down
