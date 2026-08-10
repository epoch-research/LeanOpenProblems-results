import FormalConjectures.Util.ProblemImports
open List Nat Function Set

noncomputable def origStep (config : List ℕ) : List ℕ :=
  let half_ceil (m : ℕ) : ℕ := (m + 1) / 2
  let half_floor (m : ℕ) : ℕ := m / 2
  let trim_trailing_zeros (l : List ℕ) : List ℕ :=
    (List.reverse l).dropWhile (fun x => x = 0) |>.reverse
  let base_masses := config.map half_ceil ++ [0]
  let received_masses := 0 :: config.map half_floor
  let next_config_long := List.zipWith Nat.add base_masses received_masses
  trim_trailing_zeros next_config_long

def stepAux : ℕ → List ℕ → List ℕ
| carry, [] => if carry = 0 then [] else [carry]
| carry, m :: ms => (carry + (m + 1) / 2) :: stepAux (m / 2) ms

def rStep (config : List ℕ) : List ℕ := stepAux 0 config

lemma origStep_eq_rStep : ∀ config : List ℕ, origStep config = rStep config := by
  intro config
  induction config with
  | nil => simp [origStep, rStep, stepAux]
  | cons m ms ih =>
    simp [origStep, rStep, stepAux]

