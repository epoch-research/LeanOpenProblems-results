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
    (hsq : (3 * (n - (x^3 + y^2)) + 1).sqrt *
           (3 * (n - (x^3 + y^2)) + 1).sqrt =
           3 * (n - (x^3 + y^2)) + 1) : A338696 n > 0 := by
  unfold A338696
  let f : ℕ → ℕ → ℕ := fun x y =>
    if x ^ 3 + y ^ 2 ≤ n then
      if (3 * (n - (x ^ 3 + y ^ 2)) + 1).sqrt *
          (3 * (n - (x ^ 3 + y ^ 2)) + 1).sqrt =
          3 * (n - (x ^ 3 + y ^ 2)) + 1 then 1 else 0
    else 0
  change 0 < ∑ x' ∈ range (n + 1), ∑ y' ∈ range (n + 1), f x' y'
  apply Finset.sum_pos'
  · intro a ha
    exact Finset.sum_nonneg (by intro b hb; exact Nat.zero_le _)
  · refine ⟨x, hx, ?_⟩
    apply Finset.sum_pos'
    · intro b hb; exact Nat.zero_le _
    · refine ⟨y, hy, ?_⟩
      dsimp [f]
      simp [hxy, hsq]

example : A338696 20 > 0 := by
  apply A338696_pos_of_witness (x:=0) (y:=2)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
