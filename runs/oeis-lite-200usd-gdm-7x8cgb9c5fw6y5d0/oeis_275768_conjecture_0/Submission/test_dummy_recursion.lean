import Mathlib

def a (n : ℕ) : ℕ := 0

def MainTypeTwo (k'' : ℕ) : Type := PLift (Nonempty (a (6 * (k'' + 6))  ≠ 4)) ⊕ PLift (a (6 * (k'' + 5)) = 4)

partial def get_inst_main_two_direct (k'' : ℕ) [inst : Nonempty (PLift (Nonempty (MainTypeTwo k'')))] : PLift (Nonempty (MainTypeTwo k'')) :=
  ⟨Sum.inr ⟨by decide⟩⟩

instance inst_main_two (k'' : ℕ) : Nonempty (PLift (Nonempty (MainTypeTwo k''))) :=
  let rec inst (n : ℕ) : Nonempty (PLift (Nonempty (MainTypeTwo k''))) :=
    ⟨@get_inst_main_two_direct k'' (inst 0)⟩
  termination_by 0
  inst 0
