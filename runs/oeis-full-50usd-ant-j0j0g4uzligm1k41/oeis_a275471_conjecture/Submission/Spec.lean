import FormalConjectures.Util.ProblemImports

open Nat

def a (n : ℕ) : ℕ :=
  (Finset.range (n + 1)).sum fun k =>
    (Finset.range (n.sqrt + 1)).sum fun x =>
      (Finset.range (n.sqrt + 1)).sum fun y =>
        let term_inner := 1 + x^2 + y^2
        let term_outer := 4^k * term_inner
        if x ≤ y ∧ x % 2 = y % 2 ∧ term_outer ≤ n then
          let R : ℕ := n - term_outer
          if R.sqrt * R.sqrt = R then 1 else 0
        else 0

theorem a_449 : a 449 = 0 := by native_decide

/-- If there is a valid representation `n = 4^k (1+x²+y²) + z²` with `x ≤ y`, `x ≡ y [2]`,
and the relevant parameters within the summation ranges, then `0 < a n`. -/
theorem a_pos_of_rep {n k x y : ℕ}
    (hk : k ≤ n) (hx : x ≤ n.sqrt) (hy : y ≤ n.sqrt)
    (hxy : x ≤ y) (hpar : x % 2 = y % 2)
    (hle : 4 ^ k * (1 + x ^ 2 + y ^ 2) ≤ n)
    (hsq : (n - 4 ^ k * (1 + x ^ 2 + y ^ 2)).sqrt * (n - 4 ^ k * (1 + x ^ 2 + y ^ 2)).sqrt
            = n - 4 ^ k * (1 + x ^ 2 + y ^ 2)) :
    0 < a n := by
  have hkmem : k ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
  have hxmem : x ∈ Finset.range (n.sqrt + 1) := Finset.mem_range.mpr (by omega)
  have hymem : y ∈ Finset.range (n.sqrt + 1) := Finset.mem_range.mpr (by omega)
  set F : ℕ → ℕ → ℕ → ℕ := fun k x y =>
    if x ≤ y ∧ x % 2 = y % 2 ∧ 4 ^ k * (1 + x ^ 2 + y ^ 2) ≤ n then
      (if (n - 4 ^ k * (1 + x ^ 2 + y ^ 2)).sqrt * (n - 4 ^ k * (1 + x ^ 2 + y ^ 2)).sqrt
          = n - 4 ^ k * (1 + x ^ 2 + y ^ 2) then (1:ℕ) else 0) else 0 with hF
  have hsum : a n = (Finset.range (n + 1)).sum fun k =>
      (Finset.range (n.sqrt + 1)).sum fun x =>
        (Finset.range (n.sqrt + 1)).sum fun y => F k x y := rfl
  have hone : F k x y = 1 := by
    have hbeta : F k x y = if x ≤ y ∧ x % 2 = y % 2 ∧ 4 ^ k * (1 + x ^ 2 + y ^ 2) ≤ n then
        (if (n - 4 ^ k * (1 + x ^ 2 + y ^ 2)).sqrt * (n - 4 ^ k * (1 + x ^ 2 + y ^ 2)).sqrt
          = n - 4 ^ k * (1 + x ^ 2 + y ^ 2) then (1:ℕ) else 0) else 0 := rfl
    rw [hbeta, if_pos ⟨hxy, hpar, hle⟩, if_pos hsq]
  have h1 : 1 ≤ (Finset.range (n.sqrt + 1)).sum fun y => F k x y := by
    have h := Finset.single_le_sum (f := fun y => F k x y)
      (fun i _ => Nat.zero_le (F k x i)) hymem
    simp only [] at h
    rwa [hone] at h
  have h2 : 1 ≤ (Finset.range (n.sqrt + 1)).sum fun x =>
      (Finset.range (n.sqrt + 1)).sum fun y => F k x y := by
    refine le_trans h1 ?_
    exact Finset.single_le_sum (f := fun x => (Finset.range (n.sqrt + 1)).sum fun y => F k x y)
      (fun i _ => Nat.zero_le _) hxmem
  have h3 : 1 ≤ a n := by
    rw [hsum]
    refine le_trans h2 ?_
    exact Finset.single_le_sum
      (f := fun k => (Finset.range (n.sqrt + 1)).sum fun x =>
        (Finset.range (n.sqrt + 1)).sum fun y => F k x y)
      (fun i _ => Nat.zero_le _) hkmem
  omega

/-- Pigeonhole on parities: among any three naturals, two share parity; we can extract an
ordered pair `x ≤ y` of equal parity and a third element `z`, with the same sum of squares. -/
theorem pigeon3 (X Y Z : ℕ) :
    ∃ x y z, x ≤ y ∧ x % 2 = y % 2 ∧ x ^ 2 + y ^ 2 + z ^ 2 = X ^ 2 + Y ^ 2 + Z ^ 2 := by
  have key : ∀ A B : ℕ, A % 2 = B % 2 →
      ∃ x y, x ≤ y ∧ x % 2 = y % 2 ∧ x ^ 2 + y ^ 2 = A ^ 2 + B ^ 2 := by
    intro A B hAB
    rcases le_total A B with h | h
    · exact ⟨A, B, h, hAB, rfl⟩
    · exact ⟨B, A, h, hAB.symm, by ring⟩
  by_cases hXY : X % 2 = Y % 2
  · obtain ⟨x, y, hxy, hpar, hsum⟩ := key X Y hXY
    exact ⟨x, y, Z, hxy, hpar, by rw [hsum]⟩
  · by_cases hXZ : X % 2 = Z % 2
    · obtain ⟨x, y, hxy, hpar, hsum⟩ := key X Z hXZ
      exact ⟨x, y, Y, hxy, hpar, by rw [hsum]; ring⟩
    · have hYZ : Y % 2 = Z % 2 := by omega
      obtain ⟨x, y, hxy, hpar, hsum⟩ := key Y Z hYZ
      exact ⟨x, y, X, hxy, hpar, by rw [hsum]; ring⟩

/-- The **three-squares theorem** of Gauss–Legendre (not available in Mathlib): every natural
number not of the form `4^p (8q+7)` is a sum of three squares.  This is the single deep
number-theoretic input that the whole conjecture rests upon. -/
theorem three_squares (m : ℕ) (h : ¬ ∃ p q, m = 4 ^ p * (8 * q + 7)) :
    ∃ x y z, x ^ 2 + y ^ 2 + z ^ 2 = m := by
  sorry

/-- The easy (and generic) case: if `n - 1` is a sum of three squares (i.e. not of the bad form),
then `a n > 0`, via a representation with `k = 0`. -/
theorem exists_rep_easy (n : ℕ) (hn : 0 < n)
    (hbad : ¬ ∃ p q, n - 1 = 4 ^ p * (8 * q + 7)) : 0 < a n := by
  obtain ⟨X, Y, Z, hXYZ⟩ := three_squares (n - 1) hbad
  obtain ⟨x, y, z, hxy, hpar, hsum⟩ := pigeon3 X Y Z
  have hsum' : x ^ 2 + y ^ 2 + z ^ 2 = n - 1 := by rw [hsum, hXYZ]
  -- key arithmetic facts
  have hxyz_le : x ^ 2 + y ^ 2 ≤ n - 1 := by omega
  have hle : 4 ^ 0 * (1 + x ^ 2 + y ^ 2) ≤ n := by simp; omega
  have hR : n - 4 ^ 0 * (1 + x ^ 2 + y ^ 2) = z ^ 2 := by simp; omega
  have hsq : (n - 4 ^ 0 * (1 + x ^ 2 + y ^ 2)).sqrt * (n - 4 ^ 0 * (1 + x ^ 2 + y ^ 2)).sqrt
      = n - 4 ^ 0 * (1 + x ^ 2 + y ^ 2) := by
    rw [hR]
    rw [show z ^ 2 = z * z by ring, Nat.sqrt_eq]
  have hxle : x ≤ n.sqrt := by
    apply Nat.le_sqrt.mpr
    have : x * x ≤ n := by nlinarith [sq_nonneg x, hxyz_le]
    omega
  have hyle : y ≤ n.sqrt := by
    apply Nat.le_sqrt.mpr
    have : y * y ≤ n := by nlinarith [sq_nonneg y, hxyz_le]
    omega
  exact a_pos_of_rep (Nat.zero_le n) hxle hyle hxy hpar hle hsq

/-- The hard direction. The remaining cases (where `n-1` is of the bad form) require, in addition
to `three_squares`, a *parity-refined* three-squares theorem for the residual class
`n ≡ 1 [MOD 8]`; this is the genuinely hard part. -/
theorem exists_rep (n : ℕ) (hn : 0 < n) (h : n ≠ 449) : 0 < a n := by
  by_cases hbad : ∃ p q, n - 1 = 4 ^ p * (8 * q + 7)
  · sorry
  · exact exists_rep_easy n hn hbad

theorem oeis_a275471_conjecture : ∀ n : ℕ, n > 0 → (a n > 0 ↔ n ≠ 449) := by
  intro n hn
  refine ⟨fun hpos hne => ?_, fun hne => exists_rep n hn hne⟩
  subst hne
  rw [a_449] at hpos
  exact absurd hpos (lt_irrefl 0)
