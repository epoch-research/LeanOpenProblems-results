import Mathlib
import Submission.Test5

open Nat

def liftList (m M k P : ℕ) : List ℕ :=
  (makeListAsc m M k).enum.map (fun (i, y) => y + i * P)

lemma liftList_length (m M k P : ℕ) (hm : m > 0) : (liftList m M k P).length = m + 9 * k := by
  unfold liftList
  simp [length_makeListAsc m M k hm]

