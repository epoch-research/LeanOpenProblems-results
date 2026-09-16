import FormalConjectures.Util.ProblemImports

open Finset Nat Real Filter Asymptotics

def A051293 (n : ℕ) : ℕ :=
  Finset.card (
    (Finset.Icc 1 n).powerset.filter fun S : Finset ℕ =>
      S.Nonempty ∧ S.card ∣ S.sum id
  )

noncomputable def a_real (n : ℕ) : ℝ := A051293 n

theorem oeis_51293_conjecture_0 :
    Tendsto
      (fun n : ℕ =>
        (a_real n - ((2 : ℝ) ^ (n + 1) / (n : ℝ)) * (
          (1 : ℝ)
          + 1 / (n : ℝ)
          + 3 / ((n : ℝ) ^ 2)
          + 13 / ((n : ℝ) ^ 3)
          + 75 / ((n : ℝ) ^ 4)
          + 541 / ((n : ℝ) ^ 5)
        ))
        /
        (((2 : ℝ) ^ (n + 1)) / ((n : ℝ) ^ 6))
      )
      atTop
      (nhds 0) := by sorry

theorem oeis_51293_conjecture_0.disproof : ¬ (type_of% @oeis_51293_conjecture_0) := by sorry
