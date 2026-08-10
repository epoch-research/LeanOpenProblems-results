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

  if n = 0 then
    0
  else
    let initial_config : List ℕ := [n]
    let target_config : List ℕ := List.replicate n 1

    let S (t : ℕ) : List ℕ := (List.range t).foldl (fun acc _ => ca_step acc) initial_config

    let stable_steps : Set ℕ := {k | S k = target_config}

    sInf stable_steps

lemma a_one : a 1 = 0 := by
  dsimp [a]
  -- stable_steps with n = 1: S t = [1]
  -- S 0 = [1]
  have h0 : (0 : ℕ) ∈ {k | ((range k).foldl (fun acc _ =>
    let base_masses := acc.map (fun m => (m + 1) / 2) ++ [0]
    let received_masses := 0 :: acc.map (fun m => m / 2)
    let next_config_long := zipWith HAdd.hAdd base_masses received_masses
    (reverse next_config_long).dropWhile (fun x => x = 0) |>.reverse
  ) [1]) = replicate 1 1} := by
    simp
  have h_le : sInf {k | ((range k).foldl (fun acc _ =>
    let base_masses := acc.map (fun m => (m + 1) / 2) ++ [0]
    let received_masses := 0 :: acc.map (fun m => m / 2)
    let next_config_long := zipWith HAdd.hAdd base_masses received_masses
    (reverse next_config_long).dropWhile (fun x => x = 0) |>.reverse
  ) [1]) = replicate 1 1} ≤ 0 := by
    apply Nat.sInf_le h0
  exact Nat.eq_zero_of_nonpos_iff.mpr h_le
