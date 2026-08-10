import Mathlib

open Nat

def a (n : ℕ) : ℕ := if n = 30 then 5 else 0

def MainTypeTwo (k'' : ℕ) : Type := PLift (Nonempty (a (6 * (k'' + 6))  ≠ 4)) ⊕ PLift (a (6 * (k'' + 5)) = 4)

partial def get_inst_main_two_direct (k'' : ℕ) [inst : Nonempty (PLift (Nonempty (MainTypeTwo k'')))] : PLift (Nonempty (MainTypeTwo k'')) :=
  ⟨Sum.inr ⟨by decide⟩⟩

partial def inst_main_two_helper (k'' : ℕ) : Nonempty (PLift (Nonempty (MainTypeTwo k''))) :=
  ⟨@get_inst_main_two_direct k'' (inst_main_two_helper k'')⟩

instance inst_main_two (k'' : ℕ) : Nonempty (PLift (Nonempty (MainTypeTwo k''))) :=
  inst_main_two_helper k''
