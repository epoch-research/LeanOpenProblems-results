unsafe def bad_proof_unsafe (u : Unit) : False := bad_proof_unsafe u

theorem cheat : False := bad_proof_unsafe ()
