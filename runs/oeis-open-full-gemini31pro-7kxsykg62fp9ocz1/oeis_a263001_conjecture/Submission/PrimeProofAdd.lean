import Submission.PrimeProof

@[simp] lemma my_pi_chunk_succ (start l : ℕ) :
  my_pi_chunk start (l + 1) = my_pi_chunk start l + if my_prime (start + l) then 1 else 0 := rfl

lemma my_pi_chunk_add (start len1 len2 : ℕ) :
  my_pi_chunk start (len1 + len2) = my_pi_chunk start len1 + my_pi_chunk (start + len1) len2 := by
  induction len2 with
  | zero =>
    simp [my_pi_chunk]
  | succ l ih =>
    have h_add : len1 + (l + 1) = (len1 + l) + 1 := by omega
    rw [h_add]
    rw [my_pi_chunk_succ]
    rw [ih]
    rw [my_pi_chunk_succ]
    have h_add2 : start + len1 + l = start + (len1 + l) := by omega
    rw [h_add2]
    omega
