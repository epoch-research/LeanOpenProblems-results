import Submission.PrimeProofAdd

lemma my_pi_chunk_mono (start len1 len2 : ℕ) (h : len1 ≤ len2) :
  my_pi_chunk start len1 ≤ my_pi_chunk start len2 := by
  have h_add : len2 = len1 + (len2 - len1) := by omega
  rw [h_add, my_pi_chunk_add]
  omega

lemma my_pi_mono {a b : ℕ} (h : a ≤ b) : my_pi a ≤ my_pi b := by
  unfold my_pi
  apply my_pi_chunk_mono
  exact h

inductive BTree
  | leaf (val : ℕ)
  | branch (left right : BTree)

def BTree.get (t : BTree) (idx : ℕ) (depth : ℕ) : ℕ :=
  match depth, t with
  | 0, leaf v => v
  | d + 1, branch l r =>
    let bit := idx % 2
    if bit = 0 then l.get (idx / 2) d else r.get (idx / 2) d
  | _, _ => 0
