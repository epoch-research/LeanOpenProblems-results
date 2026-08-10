import FormalConjectures.Util.ProblemImports

open List Nat Function Set

lemma exists_replicate_dropWhile_eq (L : List ℕ) :
  ∃ k, replicate k 0 ++ L.dropWhile (fun x => x = 0) = L := by
  induction L with
  | nil =>
    use 0
    rfl
  | cons x xs ih =>
    have hx : x = 0 ∨ x ≠ 0 := by omega
    rcases hx with rfl | hx
    · -- x = 0
      dsimp [dropWhile]
      rcases ih with ⟨k, hk⟩
      use k + 1
      simp [replicate_succ, hk]
    · -- x ≠ 0
      have h_drop : (x :: xs).dropWhile (fun x => x = 0) = x :: xs := by
        dsimp [dropWhile]
        simp [hx]
      use 0
      simp [h_drop]
