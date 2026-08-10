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

lemma A338696_19_eq_zero : A338696 19 = 0 := by
  unfold A338696
  apply Finset.sum_eq_zero
  intro x hx
  apply Finset.sum_eq_zero
  intro y hy
  have hxlt : x < 20 := by simpa using (Finset.mem_range.mp hx)
  have hylt : y < 20 := by simpa using (Finset.mem_range.mp hy)
  interval_cases x <;> interval_cases y <;> norm_num

example (n : ℕ) (h : A338696 n > 0) : n ≠ 19 := by
  intro hn
  subst n
  rw [A338696_19_eq_zero] at h
  exact Nat.lt_irrefl 0 h
