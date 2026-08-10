inductive Bad7 : Type 1
| mk : (∀ (T : Type 0), T → Bad7) → Bad7
| base : Bad7

def decomp7 : Bad7 → (∀ (T : Type 0), T → Bad7)
| Bad7.base => fun _ _ => Bad7.base
| Bad7.mk f => f

theorem decomp7_mk (f : ∀ (T : Type 0), T → Bad7) : decomp7 (Bad7.mk f) = f := rfl

open Classical

def Y : Type 0 := ULift Bad7

def up (b : Bad7) : Y := ULift.up b
def down (y : Y) : Bad7 := ULift.down y

def f (y : Y) (y2 : Y) : Bad7 :=
  decomp7 (down y) Y y2

noncomputable def g (h : Y → Bad7) : Y :=
  up (Bad7.mk (fun (T : Type 0) (t : T) =>
    if h_eq : T = Y then
      h (h_eq ▸ t)
    else
      Bad7.base))

theorem fg_eq (h : Y → Bad7) : f (g h) = h := by
  funext y
  dsimp [f, g, up, down, decomp7_mk]
  have h_eq : Y = Y := rfl
  rw [dif_pos h_eq]
  rfl
