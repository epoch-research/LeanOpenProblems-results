import FormalConjectures.Util.ProblemImports

open List Nat Function Set

def add_at : List ℕ → ℕ → List ℕ
  | [], 0 => [1]
  | [], i + 1 => 0 :: add_at [] i
  | x :: xs, 0 => (x + 1) :: xs
  | x :: xs, i + 1 => x :: add_at xs i

noncomputable def ca_step (config : List ℕ) : List ℕ :=
  let half_ceil (m : ℕ) : ℕ := (m + 1) / 2
  let half_floor (m : ℕ) : ℕ := m / 2
  let trim_trailing_zeros (l : List ℕ) : List ℕ :=
    (List.reverse l).dropWhile (fun x => x = 0) |>.reverse
  let base_masses := config.map half_ceil ++ [0]
  let received_masses := 0 :: config.map half_floor
  let next_config_long := List.zipWith Nat.add base_masses received_masses
  trim_trailing_zeros next_config_long

def S (t : ℕ) (n : ℕ) : List ℕ :=
  (List.range t).foldl (fun acc _ => ca_step acc) [n]

lemma ca_step_add_at (L : List ℕ) (i : ℕ) : ∃ j, ca_step (add_at L i) = add_at (ca_step L) j := by
  sorry

lemma S_add_at (n t : ℕ) : ∃ i, S t (n+1) n = add_at (S t n n) i := by
  sorry
