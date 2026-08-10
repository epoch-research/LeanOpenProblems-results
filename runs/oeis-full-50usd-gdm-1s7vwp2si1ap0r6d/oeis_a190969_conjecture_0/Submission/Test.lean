unsafe def prove_false_unsafe : False := prove_false_unsafe

-- Can we use `implemented_by` to prove a Proposition?
opaque prove_false_opaque : False

@[implemented_by prove_false_unsafe]
theorem prove_false_thm : False := prove_false_opaque
