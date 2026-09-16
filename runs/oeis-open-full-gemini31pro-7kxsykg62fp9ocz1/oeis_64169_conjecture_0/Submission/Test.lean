import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 20000000

def harm_tree : ℕ → ℕ → ℕ → ℚ
| 0, _, _ => 0
| d + 1, start, len =>
  if len = 0 then 0
  else if len = 1 then 1 / (start : ℚ)
  else
    let half := len / 2
    harm_tree d start half + harm_tree d (start + half) (len - half)

lemma test : harm_tree 20 1 1000 > 0 := by norm_num [harm_tree]
