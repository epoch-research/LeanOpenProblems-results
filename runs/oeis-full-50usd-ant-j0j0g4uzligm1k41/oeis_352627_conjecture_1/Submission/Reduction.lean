import FormalConjectures.Util.ProblemImports

open Nat Finset

/-- Same definition as in `Spec.lean`. -/
def a (n : ℕ) : ℕ :=
  let R : Finset ℕ := Finset.range (sqrt n + 1)
  let S_quadruples := R.product (R.product (R.product R))
  (S_quadruples.filter (fun p =>
    let a := p.1;
    let b := p.2.1;
    let c := p.2.2.1;
    let d := p.2.2.2;
    a^2 + 2 * b^2 + c^4 + 4 * d^4 + c^2 * d^2 = n
  )).card

/-- Helper: if `x^2 ≤ n` then `x ≤ sqrt n`. -/
theorem le_sqrt_of_sq_le {x n : ℕ} (h : x ^ 2 ≤ n) : x ≤ sqrt n := by
  rw [Nat.le_sqrt]
  simpa [pow_two] using h

/-- The reduction lemma: the range `[0, sqrt n]` loses no solution, so `a n > 0`
    is *exactly* the (unbounded) representability of `n` by the form. This is the
    provable "packaging" step; the mathematical content of the conjecture is the
    existence of the quadruple. -/
theorem a_pos_iff (n : ℕ) :
    0 < a n ↔ ∃ A B C D : ℕ, A ^ 2 + 2 * B ^ 2 + C ^ 4 + 4 * D ^ 4 + C ^ 2 * D ^ 2 = n := by
  unfold a
  simp only [Finset.card_pos, Finset.filter_nonempty_iff]
  constructor
  · rintro ⟨p, -, hp⟩
    exact ⟨p.1, p.2.1, p.2.2.1, p.2.2.2, hp⟩
  · rintro ⟨A, B, C, D, hABCD⟩
    -- Each variable is ≤ sqrt n because its individual contribution is ≤ n.
    have hA : A ≤ sqrt n := by
      apply le_sqrt_of_sq_le; omega
    have hB : B ≤ sqrt n := by
      apply le_sqrt_of_sq_le
      have : B ^ 2 ≤ 2 * B ^ 2 := by omega
      omega
    have hC : C ≤ sqrt n := by
      -- C ≤ C^2 ≤ sqrt n ; use C^2 ≤ C^4 ≤ n
      have hC2 : C ^ 2 ≤ sqrt n := by
        apply le_sqrt_of_sq_le
        have h4 : (C ^ 2) ^ 2 = C ^ 4 := by ring
        omega
      have : C ≤ C ^ 2 := by nlinarith [sq_nonneg C, Nat.zero_le C]
      exact le_trans this hC2
    have hD : D ≤ sqrt n := by
      have hD2 : D ^ 2 ≤ sqrt n := by
        apply le_sqrt_of_sq_le
        have h4 : (D ^ 2) ^ 2 = D ^ 4 := by ring
        omega
      have : D ≤ D ^ 2 := by nlinarith [sq_nonneg D, Nat.zero_le D]
      exact le_trans this hD2
    have hAr : A ∈ Finset.range (sqrt n + 1) := Finset.mem_range.mpr (by omega)
    have hBr : B ∈ Finset.range (sqrt n + 1) := Finset.mem_range.mpr (by omega)
    have hCr : C ∈ Finset.range (sqrt n + 1) := Finset.mem_range.mpr (by omega)
    have hDr : D ∈ Finset.range (sqrt n + 1) := Finset.mem_range.mpr (by omega)
    have hmem := Finset.mk_mem_product hAr
      (Finset.mk_mem_product hBr (Finset.mk_mem_product hCr hDr))
    exact ⟨(A, B, C, D), hmem, hABCD⟩
