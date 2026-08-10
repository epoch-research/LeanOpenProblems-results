import FormalConjectures.Util.ProblemImports
open List Nat Function Set

noncomputable def a (n : ℕ) : ℕ :=
  let half_ceil (m : ℕ) : ℕ := (m + 1) / 2
  let half_floor (m : ℕ) : ℕ := m / 2
  let trim_trailing_zeros (l : List ℕ) : List ℕ :=
    (List.reverse l).dropWhile (fun x => x = 0) |>.reverse
  let ca_step (config : List ℕ) : List ℕ :=
    let base_masses := config.map half_ceil ++ [0]
    let received_masses := 0 :: config.map half_floor
    let next_config_long := List.zipWith Nat.add base_masses received_masses
    trim_trailing_zeros next_config_long
  if n = 0 then 0 else
    let initial_config : List ℕ := [n]
    let target_config : List ℕ := List.replicate n 1
    let S (t : ℕ) : List ℕ := (List.range t).foldl (fun acc _ => ca_step acc) initial_config
    let stable_steps : Set ℕ := {k | S k = target_config}
    sInf stable_steps

def half_ceil (m : ℕ) : ℕ := (m + 1) / 2
def half_floor (m : ℕ) : ℕ := m / 2
def trim_trailing_zeros (l : List ℕ) : List ℕ :=
  (List.reverse l).dropWhile (fun x => x = 0) |>.reverse
def ca_step (config : List ℕ) : List ℕ :=
  let base_masses := config.map half_ceil ++ [0]
  let received_masses := 0 :: config.map half_floor
  let next_config_long := List.zipWith Nat.add base_masses received_masses
  trim_trailing_zeros next_config_long
def S (n t : ℕ) : List ℕ := (List.range t).foldl (fun acc _ => ca_step acc) [n]
noncomputable def A (n : ℕ) := if n=0 then 0 else sInf {k | S n k = List.replicate n 1}

example (n) : a n = A n := by
  unfold a A S ca_step trim_trailing_zeros half_ceil half_floor
  rfl
