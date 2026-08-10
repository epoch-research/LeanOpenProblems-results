import FormalConjectures.Util.ProblemImports

open scoped BigOperators

lemma sum_units_sq_eq_zero {n : ℕ} [NeZero n] (h3u : IsUnit (3 : ZMod n))
    (hu : IsUnit (2 : ZMod n)) :
    ∑ u : (ZMod n)ˣ, ((u : ZMod n))^2 = 0 := by
  obtain ⟨c, hcval⟩ := hu
  have key : ∑ u : (ZMod n)ˣ, ((u : ZMod n))^2
      = ∑ u : (ZMod n)ˣ, (((c*u : (ZMod n)ˣ) : ZMod n))^2 :=
    (Equiv.sum_comp (Equiv.mulLeft c) (fun v => ((v : ZMod n))^2)).symm
  have expand : ∑ u : (ZMod n)ˣ, (((c*u : (ZMod n)ˣ) : ZMod n))^2
      = (4 : ZMod n) * ∑ u : (ZMod n)ˣ, ((u : ZMod n))^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    push_cast
    rw [hcval]
    ring
  rw [expand] at key
  have h3 : (3 : ZMod n) * (∑ u : (ZMod n)ˣ, ((u : ZMod n))^2) = 0 := by
    linear_combination -key
  exact (h3u.mul_right_eq_zero).mp h3

-- Sum of units of ZMod n is 0 (when there's a unit c with c-1 a unit, e.g. via 2)
lemma sum_units_eq_zero {n : ℕ} [NeZero n] (hu : IsUnit (2 : ZMod n)) :
    ∑ u : (ZMod n)ˣ, ((u : ZMod n)) = 0 := by
  obtain ⟨c, hcval⟩ := hu
  have key : ∑ u : (ZMod n)ˣ, ((u : ZMod n))
      = ∑ u : (ZMod n)ˣ, (((c*u : (ZMod n)ˣ) : ZMod n)) :=
    (Equiv.sum_comp (Equiv.mulLeft c) (fun v => ((v : ZMod n)))).symm
  have expand : ∑ u : (ZMod n)ˣ, (((c*u : (ZMod n)ˣ) : ZMod n))
      = (2 : ZMod n) * ∑ u : (ZMod n)ˣ, ((u : ZMod n)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    push_cast
    rw [hcval]
  rw [expand] at key
  linear_combination -key
