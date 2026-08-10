import FormalConjectures.Util.ProblemImports
open Nat
def A218585 (n : ℕ) : ℕ :=
  (Finset.Icc 1 (n / 2)).sum fun x ↦
    let y := n - x
    if Nat.Prime (x * x + x * y + y * y) then 1 else 0
theorem A218585_pos_iff (n : ℕ) :
    0 < A218585 n ↔
      ∃ x ∈ Finset.Icc 1 (n / 2),
        Nat.Prime (x * x + x * (n - x) + (n - x) * (n - x)) := by
  unfold A218585
  rw [Finset.sum_pos_iff_of_nonneg (fun i _ => Nat.zero_le _)]
  constructor
  · rintro ⟨x, hx, hxp⟩; refine ⟨x, hx, ?_⟩; by_contra h; simp [h] at hxp
  · rintro ⟨x, hx, hxp⟩; exact ⟨x, hx, by simp [hxp]⟩
theorem second : A218585 8 = 0 := by decide
#print axioms A218585_pos_iff
#print axioms second
