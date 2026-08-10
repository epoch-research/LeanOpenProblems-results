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

lemma S_zero_two : (List.range 0).foldl (fun acc _ =>
    let half_ceil (m : ℕ) : ℕ := (m + 1) / 2
    let half_floor (m : ℕ) : ℕ := m / 2
    let trim_trailing_zeros (l : List ℕ) : List ℕ :=
      (List.reverse l).dropWhile (fun x => x = 0) |>.reverse
    let base_masses := acc.map half_ceil ++ [0]
    let received_masses := 0 :: acc.map half_floor
    let next_config_long := List.zipWith Nat.add base_masses received_masses
    trim_trailing_zeros next_config_long
  ) [2] = [2] := by
  rfl

lemma S_one_two : (List.range 1).foldl (fun acc _ =>
    let half_ceil (m : ℕ) : ℕ := (m + 1) / 2
    let half_floor (m : ℕ) : ℕ := m / 2
    let trim_trailing_zeros (l : List ℕ) : List ℕ :=
      (List.reverse l).dropWhile (fun x => x = 0) |>.reverse
    let base_masses := acc.map half_ceil ++ [0]
    let received_masses := 0 :: acc.map half_floor
    let next_config_long := List.zipWith Nat.add base_masses received_masses
    trim_trailing_zeros next_config_long
  ) [2] = [1, 1] := by
  decide

lemma a_two : a 2 = 1 := by
  dsimp [a]
  set S := {k | ((range k).foldl (fun acc _ =>
    let base_masses := acc.map (fun m => (m + 1) / 2) ++ [0]
    let received_masses := 0 :: acc.map (fun m => m / 2)
    let next_config_long := zipWith HAdd.hAdd base_masses received_masses
    (reverse next_config_long).dropWhile (fun x => x = 0) |>.reverse
  ) [2]) = replicate 2 1}
  have h1 : (1 : ℕ) ∈ S := by
    simp [S, S_one_two]
  have h_le : sInf S ≤ 1 := by
    apply Nat.sInf_le h1
  have h_nonempty : S.Nonempty := ⟨1, h1⟩
  have h_mem := Nat.sInf_mem h_nonempty
  have h0 : (0 : ℕ) ∉ S := by
    intro h
    simp [S, S_zero_two] at h
  have h_ne : sInf S ≠ 0 := by
    intro h
    rw [h] at h_mem
    exact h0 h_mem
  have : sInf S = 1 := by omega
  exact this
