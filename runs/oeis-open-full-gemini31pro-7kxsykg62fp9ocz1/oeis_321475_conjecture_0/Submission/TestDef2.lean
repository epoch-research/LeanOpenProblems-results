import Mathlib

open Nat List

noncomputable def A321475_test (n : ℕ) : ℕ :=
  if n = 0 then 1
  else
    let noz (k : ℕ) : ℕ :=
      ofDigits 10 (filter (fun d : ℕ => d ≠ 0) (digits 10 k))
    let rec loop (i : ℕ) (P : ℕ) : ℕ :=
      if i = 0 then P
      else loop (i - 1) (noz (i * P))
    loop (n - 1) n

theorem loop_eq : ∀ i P, A321475_test.loop (fun k => ofDigits 10 (filter (fun d => d ≠ 0) (digits 10 k))) (i + 1) P = A321475_test.loop (fun k => ofDigits 10 (filter (fun d => d ≠ 0) (digits 10 k))) i (ofDigits 10 (filter (fun d => d ≠ 0) (digits 10 ((i + 1) * P)))) := by
  intros
  unfold A321475_test.loop
  sorry
