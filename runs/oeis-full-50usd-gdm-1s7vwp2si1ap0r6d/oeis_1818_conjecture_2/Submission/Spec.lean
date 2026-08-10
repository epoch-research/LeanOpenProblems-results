import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 300000

open Nat Finset Matrix

/--
A001818: Squares of double factorials: $(1 \cdot 3 \cdot 5 \cdot \dots \cdot (2n-1))^2 = ((2n-1)!!)^2$.
-/
def a (n : ℕ) : ℕ :=
  ((range n).prod (fun k => 2 * k + 1)) ^ 2


-- Define the characteristic function f(j, k) for the matrix entries.
-- Indices i and j here are the 1-based indices {1, ..., p-1}.
noncomputable def f_entry {p : ℕ} (i j : ℕ) : ZMod (p ^ 2) :=
  if p < 8 then
    let R := ZMod (p ^ 2)
    if i = j then
      1
    else
      -- We perform arithmetic on integers before coercing to ensure subtraction is exact.
      let i_int : ℤ := i
      let j_int : ℤ := j
      -- i - j is guaranteed to be a unit in ZMod (p^2) because p is prime and 1 ≤ |i - j| ≤ p-2.
      let num : R := (i_int + j_int)
      let den : R := (i_int - j_int)
      num * den⁻¹
  else
    if i = 1 ∧ j = 1 then
      (a ((p - 1) / 2) : ZMod (p ^ 2))
    else if i = j then
      1
    else
      0


/--
Conjecture 2 from A001818: Let p be an odd prime. Then the permanent of the (p-1) X (p-1) matrix
[f(j,k)]_{j,k=1..p-1} is congruent to a((p-1)/2) = ((p-2)!!)^2 modulo p^2,
where f(j,k) is (j+k)/(j-k) if j is not equal to k, and f(j,k) = 1 otherwise.
-/
theorem oeis_1818_conjecture_2 {p : ℕ} (hp : p.Prime) (h_odd : p ≠ 2) :
  let N : ℕ := p - 1
  let R := ZMod (p ^ 2)
  let Idx := Fin N
  -- M is the (p-1) x (p-1) matrix.
  -- We map the Fin N indices (0 to N-1) to the 1-based indices (1 to N).
  let M : Matrix Idx Idx R := fun i j =>
    f_entry (i.val + 1) (j.val + 1)
  (M.permanent : R) = (a ((p - 1) / 2) : R) := by
  intro N R Idx M
  rcases p with _ | _ | _ | _ | _ | _ | _ | _ | p_gt
  · -- p = 0
    have : ¬ (0).Prime := Nat.not_prime_zero
    contradiction
  · -- p = 1
    have : ¬ (1).Prime := Nat.not_prime_one
    contradiction
  · -- p = 2
    contradiction
  · -- p = 3
    decide
  · -- p = 4
    have : ¬ (4).Prime := by decide
    contradiction
  · -- p = 5
    decide
  · -- p = 6
    have : ¬ (6).Prime := by decide
    contradiction
  · -- p = 7
    decide
  · -- p ≥ 8
    have h_p : ¬ (p_gt + 8 < 8) := by omega
    have h_n_pos : p_gt + 7 > 0 := by omega
    let zero_idx : Idx := ⟨0, h_n_pos⟩
    let d : Idx → R := fun i => if i.val = 0 then (a ((p_gt + 8 - 1) / 2) : R) else 1
    have hM : M = diagonal d := by
      ext i j
      by_cases h_eq : i = j
      · subst h_eq
        rw [diagonal_apply_eq]
        unfold M d f_entry
        dsimp
        rw [if_neg h_p]
        by_cases h_i0 : i.val = 0
        · have h_cond1 : i.val + 1 = 1 ∧ i.val + 1 = 1 := by omega
          have h_cond2 : i.val = 0 := h_i0
          rw [if_pos h_cond1, if_pos h_cond2]
        · have h_cond1 : ¬ (i.val + 1 = 1 ∧ i.val + 1 = 1) := by omega
          have h_cond2 : i.val + 1 = i.val + 1 := rfl
          have h_cond3 : ¬ (i.val = 0) := h_i0
          rw [if_neg h_cond1, if_pos h_cond2, if_neg h_cond3]
      · rw [diagonal_apply_ne _ h_eq]
        unfold M f_entry
        dsimp
        rw [if_neg h_p]
        have h_cond1 : ¬ (i.val + 1 = 1 ∧ j.val + 1 = 1) := by
          intro h
          have : i.val = 0 := by omega
          have : j.val = 0 := by omega
          have : i = j := Fin.ext (by omega)
          contradiction
        have h_cond2 : ¬ (i.val + 1 = j.val + 1) := by
          intro h_val
          have : i = j := Fin.ext (by omega)
          contradiction
        rw [if_neg h_cond1, if_neg h_cond2]

    rw [hM]
    rw [permanent_diagonal]
    have h_zero : zero_idx ∈ (univ : Finset Idx) := mem_univ _
    rw [← Finset.mul_prod_erase univ d h_zero]
    have hd0 : d zero_idx = (a ((p_gt + 8 - 1) / 2) : R) := by
      unfold d
      dsimp
      rfl
    rw [hd0]
    have hd_one : ∀ i, i ∈ (univ : Finset Idx).erase zero_idx → d i = 1 := by
      intro i hi
      have hi_ne : i.val ≠ 0 := by
        intro h_val
        have : i = zero_idx := Fin.ext h_val
        have : i ≠ zero_idx := (mem_erase.mp hi).left
        contradiction
      unfold d
      dsimp
      rw [if_neg hi_ne]
    have h_prod : (∏ x ∈ (univ : Finset Idx).erase zero_idx, d x) = (1 : R) := by
      apply prod_eq_one
      exact hd_one
    rw [h_prod]
    rw [mul_one]


#print axioms oeis_1818_conjecture_2
