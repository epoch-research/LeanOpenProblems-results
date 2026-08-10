import FormalConjectures.Util.ProblemImports
open List Nat Function Set

def halfC (m : ℕ) := (m+1)/2
def halfF (m : ℕ) := m/2
def trimZ (l : List ℕ) := (List.reverse l).dropWhile (fun x => x=0) |>.reverse
def step (config : List ℕ) : List ℕ :=
  let base_masses := config.map halfC ++ [0]
  let received_masses := 0 :: config.map halfF
  let next_config_long := List.zipWith Nat.add base_masses received_masses
  trimZ next_config_long

example (x : ℕ) : step [x] = trimZ [halfC x, halfF x] := by simp [step]
example (x y : ℕ) : step [x,y] = trimZ [halfC x, halfC y + halfF x, halfF y] := by simp [step]
example (p : List ℕ) (x : ℕ) : step (p ++ [x]) = trimZ (List.zipWith Nat.add ((p ++ [x]).map halfC ++ [0]) (0 :: (p ++ [x]).map halfF)) := by simp [step]
#check List.map_append
#check List.zipWith_append
#check List.zipWith_append_right
#check List.zipWith_append_left
