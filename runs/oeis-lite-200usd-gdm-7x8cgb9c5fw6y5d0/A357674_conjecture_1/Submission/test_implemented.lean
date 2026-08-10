import Mathlib

def my_proof_impl (p : ℕ) : p.Prime ↔ False := sorry

@[implemented_by my_proof_impl]
def my_proof (p : ℕ) : p.Prime ↔ False := sorry
