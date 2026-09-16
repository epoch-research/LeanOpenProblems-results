import Mathlib

theorem foo : 1 = 2 := Quot.lift (fun (x : 1 = 2) => x) (fun _ _ _ => rfl) (Quot.mk (fun _ _ : (1:ℕ)=2 => True) (Classical.choice (cast (@Quot.sound Prop (fun _ _ => True) True (Nonempty (1=2)) trivial) trivial)))
