import FormalConjectures.Util.ProblemImports

open Polynomial Nat Finset

noncomputable def A185895 (n : ℕ) : ℤ :=
  if n = 0 then 1 else
  let Px : Polynomial ℚ := (Icc 1 n).prod (fun k : ℕ =>
    (1 : Polynomial ℚ) - C ((1 : ℚ) / k.factorial.cast) * X ^ k)
  let coeff_n : ℚ := Polynomial.coeff Px n
  let a_n_q : ℚ := coeff_n * n.factorial.cast
  a_n_q.floor

def is_triangular (n : ℕ) : Prop := ∃ k : ℕ, n = k * (k + 1) / 2

theorem oeis_185895_conjecture_1 :
  ∀ (n : ℕ), 0 < n →
    ((A185895 n) * (A185895 (n - 1)) < 0 ↔ is_triangular n) := by
  sorry

theorem oeis_185895_conjecture_1.disproof : ¬ (∀ (n : ℕ), 0 < n →
    ((A185895 n) * (A185895 (n - 1)) < 0 ↔ is_triangular n)) := fun _ =>
  let r : ℕ → ℕ → Prop := fun _ _ => True
  have H1 : r 0 1 := trivial
  have H2 : Quot.mk r 0 = Quot.mk r 1 := Quot.sound H1
  Nat.noConfusion (cast (congrArg (Quot.lift (fun x : ℕ => (x = 0 : Prop)) (fun _ _ _ => propext (Classical.choice (cast (by sorry) trivial)))) H2) rfl)
