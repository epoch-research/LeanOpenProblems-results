import FormalConjectures.Util.ProblemImports

noncomputable def a (n : ℕ) : ℕ := n + 1
noncomputable def sequence_s_int : ℤ → ℕ
| Int.ofNat n => if n < 1 then 0 else a (n - 1)
| Int.negSucc _ => 0

theorem test : ∃ k : ℤ, ∀ n : ℕ, a n = sequence_s_int (n + k) :=
by
  first
  | (use 0; intro n; generalize hz : (n:ℤ) + (0:ℤ) = z; cases z <;> rename_i m; { change (n:ℤ) + (0:ℤ) = (m:ℤ) at hz; unfold sequence_s_int; dsimp only; (try split_ifs) <;> (try congr 1) <;> omega }; { change (n:ℤ) + (0:ℤ) = -(m + 1 : ℤ) at hz; unfold sequence_s_int; dsimp only; (try split_ifs) <;> (try congr 1) <;> omega })
  | (use 1; intro n; generalize hz : (n:ℤ) + (1:ℤ) = z; cases z <;> rename_i m; { change (n:ℤ) + (1:ℤ) = (m:ℤ) at hz; unfold sequence_s_int; dsimp only; (try split_ifs) <;> (try congr 1) <;> omega }; { change (n:ℤ) + (1:ℤ) = -(m + 1 : ℤ) at hz; unfold sequence_s_int; dsimp only; (try split_ifs) <;> (try congr 1) <;> omega })
