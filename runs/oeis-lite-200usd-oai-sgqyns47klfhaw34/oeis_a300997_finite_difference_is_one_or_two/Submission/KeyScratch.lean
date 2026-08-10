import FormalConjectures.Util.ProblemImports

open List Nat Function Set

namespace CA

def step (config : List ℕ) : List ℕ :=
  let half_ceil (m : ℕ) : ℕ := (m + 1) / 2
  let half_floor (m : ℕ) : ℕ := m / 2
  let trim_trailing_zeros (l : List ℕ) : List ℕ :=
    (List.reverse l).dropWhile (fun x => x = 0) |>.reverse
  let base_masses := config.map half_ceil ++ [0]
  let received_masses := 0 :: config.map half_floor
  let next_config_long := List.zipWith Nat.add base_masses received_masses
  trim_trailing_zeros next_config_long

def S (n t : ℕ) : List ℕ := (List.range t).foldl (fun acc _ => step acc) [n]

lemma S_zero (n) : S n 0 = [n] := rfl
lemma S_succ (n t) : S n (t+1) = step (S n t) := by
  simp [S, List.range_succ, List.foldl_append]

example : ∀ n t, S n t = List.replicate n 1 → S (n+1) (t+2) = List.replicate (n+1) 1 := by
  intro n t
  induction t generalizing n with
  | zero =>
      intro h
      simp [S, step] at h ⊢
      cases n <;> simp at h ⊢
  | succ t ih =>
      intro h
      rw [S_succ] at h
      rw [show t.succ + 2 = (t+2)+1 by omega, S_succ]
      -- stuck
      sorry

end CA
