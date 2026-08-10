import FormalConjectures.Util.ProblemImports
open Filter

-- Sequence a_n = -2^n satisfies c*a_n < a_{n+1}? For c=3? -3*2^n < -2*2^n true, but not increasing.
example : IsLacunaryReal (fun n : ℕ => -((2:ℝ)^n)) := by
  use 3
  constructor · norm_num
  filter_upwards [] with k
  simp [pow_succ]
  nlinarith [pow_pos (by norm_num : (0:ℝ)<2) k]

example : False := by
  have ha : IsLacunaryReal (fun n : ℕ => -((2:ℝ)^n)) := by
    use 3
    constructor · norm_num
    filter_upwards [] with k
    simp [pow_succ]
    nlinarith [pow_pos (by norm_num : (0:ℝ)<2) k]
  have hev := IsLacunaryReal.eventually_lt ha
  have hbad : ∀ᶠ k in atTop, ¬ (-((2:ℝ)^k) < -((2:ℝ)^(k+1))) := by
    filter_upwards [] with k
    simp [pow_succ]
    nlinarith [pow_pos (by norm_num : (0:ℝ)<2) k]
  exact (hev.and hbad).exists.elim (fun k hk => hk.2 hk.1)
