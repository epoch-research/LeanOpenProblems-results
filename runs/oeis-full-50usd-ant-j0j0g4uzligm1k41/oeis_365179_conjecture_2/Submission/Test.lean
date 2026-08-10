import Mathlib
open Nat
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace Disproof
abbrev Z := ZMod 27
def fexp (j : Z) : Z := 7 ^ j.val
def carry (j l : Z) : Z := if 27 ≤ j.val + l.val then (9:Z) else 0
def c3 : Z →+* ZMod 3 := ZMod.castHom (by norm_num) (ZMod 3)
example : ∀ i1 j1 j2 : Z,
  (3*j1=0 ∧ (i1+carry j1 j2 = fexp j2*(4*i1+j1)+carry j2 (4*j1)) ∧ 9*j2=9*i1) →
  (c3 i1 = 0 ∨ c3 i1 = 1) := by decide
end Disproof
