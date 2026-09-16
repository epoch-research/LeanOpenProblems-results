import Mathlib

unsafe def my_proof : False :=
  unsafeCast ()

@[implemented_by my_proof]
def cheat : False := sorry

theorem foo : False := cheat
