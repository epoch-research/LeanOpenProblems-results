import Submission.Spec
open List Nat Function Set

def halfC2 (m : ℕ) := (m+1)/2
def halfF2 (m : ℕ) := m/2
def trimZ2 (l : List ℕ) := (List.reverse l).dropWhile (fun x => x=0) |>.reverse
def caStep2 (config : List ℕ) : List ℕ :=
  let base_masses := config.map halfC2 ++ [0]
  let received_masses := 0 :: config.map halfF2
  let next_config_long := List.zipWith Nat.add base_masses received_masses
  trimZ2 next_config_long

def S2 (N t : ℕ) : List ℕ := (List.range t).foldl (fun acc _ => caStep2 acc) [N]

lemma a_unfold_pos (N : ℕ) (hN : N ≠ 0) : a N = sInf ({k | S2 N k = List.replicate N 1} : Set ℕ) := by
  simp [a, S2, caStep2, halfC2, halfF2, trimZ2, hN]
