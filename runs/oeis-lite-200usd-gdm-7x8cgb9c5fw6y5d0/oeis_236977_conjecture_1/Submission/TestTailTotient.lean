import FormalConjectures.Util.ProblemImports

open Nat Finset

def totient_fast_loop (n : Nat) : Nat → Nat → Nat
  | 0, acc => acc
  | i + 1, acc =>
    if (i + 1).Coprime n then
      totient_fast_loop n i (acc + 1)
    else
      totient_fast_loop n i acc

def totient_fast (n : Nat) : Nat :=
  if n = 0 then 0
  else totient_fast_loop n (n - 1) 0

lemma totient_fast_loop_eq (n : Nat) (i : Nat) (acc : Nat) :
    totient_fast_loop n i acc = acc + ((Ico 1 (i + 1)).filter (·.Coprime n)).card := by
  induction i generalizing acc with
  | zero =>
    dsimp [totient_fast_loop]
    rw [show Ico 1 1 = ∅ by rfl]
    simp
  | succ i ih =>
    dsimp [totient_fast_loop]
    by_cases h : (i + 1).Coprime n
    · rw [if_pos h]
      rw [ih]
      have h_insert : Ico 1 (i + 2) = insert (i + 1) (Ico 1 (i + 1)) := by
        ext x
        simp only [mem_Ico, mem_insert]
        omega
      rw [h_insert, filter_insert]
      rw [if_pos h]
      rw [card_insert_of_notMem]
      · omega
      · simp only [mem_filter, mem_Ico]
        omega
    · rw [if_neg h]
      rw [ih]
      have h_insert : Ico 1 (i + 2) = insert (i + 1) (Ico 1 (i + 1)) := by
        ext x
        simp only [mem_Ico, mem_insert]
        omega
      rw [h_insert, filter_insert]
      rw [if_neg h]
