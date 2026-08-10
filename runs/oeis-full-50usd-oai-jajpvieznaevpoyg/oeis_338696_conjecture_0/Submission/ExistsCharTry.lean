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

lemma A338696_exists_of_pos {n : ℕ} (h : A338696 n > 0) :
    ∃ x ∈ range (n + 1), ∃ y ∈ range (n + 1),
      x ^ 3 + y ^ 2 ≤ n ∧
      (3 * (n - (x ^ 3 + y ^ 2)) + 1).sqrt *
        (3 * (n - (x ^ 3 + y ^ 2)) + 1).sqrt =
        3 * (n - (x ^ 3 + y ^ 2)) + 1 := by
  have hne : A338696 n ≠ 0 := Nat.ne_of_gt h
  unfold A338696 at hne
  rcases Finset.exists_ne_zero_of_sum_ne_zero hne with ⟨x, hx, hxne⟩
  rcases Finset.exists_ne_zero_of_sum_ne_zero hxne with ⟨y, hy, hyne⟩
  refine ⟨x, hx, y, hy, ?_, ?_⟩
  · by_contra hxy
    simp [hxy] at hyne
  · by_cases hxy : x ^ 3 + y ^ 2 ≤ n
    · by_contra hs
      simp [hxy, hs] at hyne
    · simp [hxy] at hyne

