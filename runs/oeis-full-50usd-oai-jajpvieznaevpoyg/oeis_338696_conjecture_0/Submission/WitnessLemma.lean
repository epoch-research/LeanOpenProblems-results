import FormalConjectures.Util.ProblemImports
open Nat BigOperators Finset
noncomputable def A338696 (n : ℕ) : ℕ :=
  (range (n + 1)).sum fun x =>
    let x_cube := x ^ 3
    (range (n + 1)).sum fun y =>
      let y_sq := y ^ 2
      if x_cube + y_sq ≤ n then
        let k := n - (x_cube + y_sq)
        let m := 3 * k + 1
        if m.sqrt * m.sqrt = m then 1 else 0
      else 0

lemma A338696_pos_of_witness {n x y : ℕ}
    (hx : x ∈ range (n+1)) (hy : y ∈ range (n+1))
    (hxy : x^3 + y^2 ≤ n)
    (hsq : (3 * (n - (x^3 + y^2)) + 1).sqrt * (3 * (n - (x^3 + y^2)) + 1).sqrt =
      3 * (n - (x^3 + y^2)) + 1) : A338696 n > 0 := by
  classical
  unfold A338696
  -- use single positive term <= sum
  have hterm : 0 < (if x^3 + y^2 ≤ n then if (3 * (n - (x^3 + y^2)) + 1).sqrt * (3 * (n - (x^3 + y^2)) + 1).sqrt = 3 * (n - (x^3 + y^2)) + 1 then 1 else 0 else 0) := by
    simp [hxy, hsq]
  have hinner : 0 < ∑ y' ∈ range (n+1), (if x^3 + y'^2 ≤ n then if (3 * (n - (x^3 + y'^2)) + 1).sqrt * (3 * (n - (x^3 + y'^2)) + 1).sqrt = 3 * (n - (x^3 + y'^2)) + 1 then 1 else 0 else 0) := by
    refine lt_of_lt_of_le hterm (single_le_sum ?_ hy)
    intro b hb
    by_cases hb1 : x^3 + b^2 ≤ n <;> simp [hb1]
  refine lt_of_lt_of_le hinner (single_le_sum ?_ hx)
  intro b hb
  exact sum_nonneg (by intro c hc; by_cases hc1 : b^3 + c^2 ≤ n <;> simp [hc1])
