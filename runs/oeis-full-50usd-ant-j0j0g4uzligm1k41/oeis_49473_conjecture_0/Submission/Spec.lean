import FormalConjectures.Util.ProblemImports

open Real

/--
A049473: Nearest integer to $n/\sqrt{2}$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  (Int.floor ((n : ℝ) / sqrt 2 + 1 / 2)).toNat

/-- $\zeta(3)$ is the Apery's constant. -/
noncomputable def zeta_three_real : ℝ :=
  (riemannZeta 3).re

/--
Let $s(n) = \zeta(3) - \sum_{k=1}^{n} 1/k^3$.
-/
noncomputable def s (n : ℕ) : ℝ :=
  zeta_three_real - Finset.sum (Finset.range n) (fun k : ℕ => (1 : ℝ) / ((k + 1 : ℝ) ^ 3))

open Finset

noncomputable def phi : ℝ := (1 + sqrt 5) / 2

/--
A001954: Nonhomogeneous Beatty sequence $\lfloor k\phi \rfloor$ for $k \ge 1$.
-/
noncomputable def A001954 : Set ℕ :=
  {n | ∃ k : ℕ, 0 < k ∧ n = (Int.floor ((k : ℝ) * phi)).toNat}

/--
A001953: Nonhomogeneous Beatty sequence $\lfloor k\phi^2 \rfloor$ for $k \ge 1$.
-/
noncomputable def A001953 : Set ℕ :=
  {n | ∃ k : ℕ, 0 < k ∧ n = (Int.floor ((k : ℝ) * phi ^ 2)).toNat}

/--
oeis_49473_conjecture_0: Let s(n) = zeta(3) - Sum_{k=1..n} 1/k^3.
Conjecture: for n >=1, s(a(n)) < 1/n^2 < s(a(n)-1), and the difference sequence of A049473
consists solely of 0's and 1, in positions given by the nonhomogeneous Beatty sequences
A001954 and A001953, respectively.

This conjecture is FALSE.  Its second part claims that the difference
`a n - a (n-1)` equals `0` exactly at the positions of the Beatty sequence
`A001953 = ⌊k φ²⌋`.  But at `n = 5` we have `a 5 = 4`, `a 4 = 3`, so the
difference is `1 ≠ 0`, while `5 ∈ A001953` (taking `k = 2`, since
`⌊2 φ²⌋ = ⌊3 + √5⌋ = 5`).  Hence the equivalence `(diff = 0 ↔ n ∈ A001953)`
fails at `n = 5`.
-/
theorem oeis_49473_conjecture_0.disproof :
  ¬ ((∀ (n : ℕ), 1 ≤ n → s (a n) < 1 / (n : ℝ) ^ 2 ∧ 1 / (n : ℝ) ^ 2 < s (a n - 1)) ∧
  (∀ (n : ℕ), 1 ≤ n →
    let diff : ℕ := a n - a (n - 1);
    (diff = 1 ↔ n ∈ A001954) ∧ (diff = 0 ↔ n ∈ A001953))) := by
  rintro ⟨-, h2⟩
  -- Bounds on √2.
  have h2nn : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have h2pos : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h2sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hlo : (1.4:ℝ) < Real.sqrt 2 := by nlinarith [h2sq, h2nn]
  have hhi : Real.sqrt 2 < 1.42 := by nlinarith [h2sq, h2nn]
  -- Compute a 4 = 3.
  have hu4pos : (0:ℝ) < 4 / Real.sqrt 2 := by positivity
  have hc4 : Real.sqrt 2 * (4 / Real.sqrt 2) = 4 := by field_simp
  have ha4 : a 4 = 3 := by
    have key : ⌊(4:ℝ) / Real.sqrt 2 + 1 / 2⌋ = 3 := by
      rw [Int.floor_eq_iff]
      refine ⟨?_, ?_⟩
      · push_cast; nlinarith [hc4, hhi, hu4pos]
      · push_cast; nlinarith [hc4, hlo, hu4pos]
    unfold a
    push_cast
    rw [key]
    rfl
  -- Compute a 5 = 4.
  have hu5pos : (0:ℝ) < 5 / Real.sqrt 2 := by positivity
  have hc5 : Real.sqrt 2 * (5 / Real.sqrt 2) = 5 := by field_simp
  have ha5 : a 5 = 4 := by
    have key : ⌊(5:ℝ) / Real.sqrt 2 + 1 / 2⌋ = 4 := by
      rw [Int.floor_eq_iff]
      refine ⟨?_, ?_⟩
      · push_cast; nlinarith [hc5, hhi, hu5pos]
      · push_cast; nlinarith [hc5, hlo, hu5pos]
    unfold a
    push_cast
    rw [key]
    rfl
  -- 5 ∈ A001953, witnessed by k = 2.
  have h5nn : (0:ℝ) ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have h5sq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs5lo : (2:ℝ) ≤ Real.sqrt 5 := by nlinarith [h5sq, h5nn]
  have hs5hi : Real.sqrt 5 < 3 := by nlinarith [h5sq, h5nn]
  have hmem : (5:ℕ) ∈ A001953 := by
    refine ⟨2, by norm_num, ?_⟩
    have e : (2:ℝ) * phi ^ 2 = 3 + Real.sqrt 5 := by
      unfold phi
      linear_combination (1/2 : ℝ) * h5sq
    have key : ⌊((2:ℕ):ℝ) * phi ^ 2⌋ = 5 := by
      push_cast
      rw [e, Int.floor_eq_iff]
      refine ⟨?_, ?_⟩
      · push_cast; linarith [hs5lo]
      · push_cast; linarith [hs5hi]
    rw [key]
    rfl
  -- Derive the contradiction from the (diff = 0 ↔ n ∈ A001953) equivalence at n = 5.
  have H := h2 5 (by norm_num)
  have hdiff0 : (a 5 - a (5 - 1) = 0 ↔ (5:ℕ) ∈ A001953) := H.2
  have hval : a 5 - a (5 - 1) = 1 := by
    rw [ha5, show (5:ℕ) - 1 = 4 from rfl, ha4]
  have contra := hdiff0.mpr hmem
  rw [hval] at contra
  exact absurd contra (by norm_num)
