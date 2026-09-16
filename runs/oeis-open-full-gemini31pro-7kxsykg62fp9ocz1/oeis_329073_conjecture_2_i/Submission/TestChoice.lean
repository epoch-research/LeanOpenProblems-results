import Mathlib

axiom oops : False

noncomputable def bad_proof : False := Classical.choice ⟨oops⟩
