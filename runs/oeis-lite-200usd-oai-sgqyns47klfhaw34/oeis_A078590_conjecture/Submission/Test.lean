import FormalConjectures.Util.ProblemImports

namespace A078590

private noncomputable def a_val : ℕ → ℕ
| 0 => 1
| 1 => 1
| n + 2 =>
  let a_n_minus_2 : ℕ := a_val n
  let a_n_minus_1 : ℕ := a_val (n + 1)
  (2 ^ a_n_minus_1 + 1) / a_n_minus_2

end A078590

open A078590

noncomputable def A078590 (n : ℕ) : ℕ :=
  if n ≥ 1 then
    a_val (n - 1)
  else
    0

example : A078590 5 = 171 := by
  norm_num [A078590, A078590.a_val]

example : A078590 6 = (2^171 + 1) / 9 := by
  norm_num [A078590, A078590.a_val]

example : ¬ (171 ∣ 2 ^ ((2^171 + 1) / 9) + 1) := by
  norm_num
