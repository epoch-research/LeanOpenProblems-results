import FormalConjectures.Util.ProblemImports
open List Nat Function Set

def trim0 (l : List ℕ) : List ℕ :=
  (List.reverse l).dropWhile (fun x => x == 0) |>.reverse

def step (config : List ℕ) : List ℕ :=
  let base_masses := config.map (fun m => (m + 1) / 2) ++ [0]
  let received_masses := 0 :: config.map (fun m => m / 2)
  let next_config_long := List.zipWith Nat.add base_masses received_masses
  trim0 next_config_long

def addAt : List ℕ → ℕ → List ℕ
| [], 0 => [1]
| [], _+1 => [] -- won't use beyond length
| x::xs, 0 => (x+1)::xs
| x::xs, p+1 => x :: addAt xs p

#eval addAt [3,4] 1
#eval step [5]
#eval step (addAt [5] 0)
#eval addAt (step [5]) 1

example : step (addAt [5] 0) = addAt (step [5]) 1 := by native_decide

lemma div2_add_one_parity (m : ℕ) :
    (m + 1 + 1) / 2 = (m + 1) / 2 + (if Even m then 1 else 0) := by
  by_cases h : Even m
  · rcases h with ⟨k, rfl⟩
    simp
    omega
  · have hm : Odd m := Nat.not_even_iff_odd.mp h
    rcases hm with ⟨k, rfl⟩
    simp
    omega

lemma floor_add_one_parity (m : ℕ) :
    (m + 1) / 2 = m / 2 + (if Even m then 0 else 1) := by
  by_cases h : Even m
  · rcases h with ⟨k, rfl⟩
    simp
    omega
  · have hm : Odd m := Nat.not_even_iff_odd.mp h
    rcases hm with ⟨k, rfl⟩
    simp
    omega

