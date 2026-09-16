import Mathlib
import Submission.Spec
import Submission.S303
import Submission.TestS303_tree

def f_int (x : ℤ) : ℤ := if x % 2 = 0 then x / 2 else x

def F_seq (n : ℕ) : ℤ := f_int (A120424 n)

-- We need to prove that F_seq never reaches S303.
-- Actually, it's easier to define the state sequence (F_seq n, C_seq n) directly!
