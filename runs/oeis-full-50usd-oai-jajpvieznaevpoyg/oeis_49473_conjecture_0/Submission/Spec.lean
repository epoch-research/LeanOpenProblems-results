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
-/
theorem oeis_49473_conjecture_0.disproof :
  ¬ ((∀ (n : ℕ), 1 ≤ n → s (a n) < 1 / (n : ℝ) ^ 2 ∧ 1 / (n : ℝ) ^ 2 < s (a n - 1)) ∧
  (∀ (n : ℕ), 1 ≤ n →
    let diff : ℕ := a n - a (n - 1);
    (diff = 1 ↔ n ∈ A001954) ∧ (diff = 0 ↔ n ∈ A001953))) :=
by
  intro h
  have ha5 : a 5 = 4 := by
    unfold a
    have hfloor : Int.floor ((5 : ℝ) / sqrt 2 + 1 / 2) = (4 : ℤ) := by
      rw [Int.floor_eq_iff]
      constructor
      · have hs2pos : 0 < sqrt 2 := sqrt_pos.2 (by norm_num)
        have hs2le : sqrt 2 ≤ (10 / 7 : ℝ) := by
          rw [sqrt_le_left (by norm_num)]
          norm_num
        have hle : (7 / 2 : ℝ) ≤ 5 / sqrt 2 := by
          rw [le_div_iff₀ hs2pos]
          nlinarith
        nlinarith
      · have hs2pos : 0 < sqrt 2 := sqrt_pos.2 (by norm_num)
        have hs2gt : (10 / 9 : ℝ) < sqrt 2 := by
          rw [lt_sqrt (by norm_num)]
          norm_num
        have hlt : 5 / sqrt 2 < (9 / 2 : ℝ) := by
          rw [div_lt_iff₀ hs2pos]
          nlinarith
        norm_num at hlt ⊢
        linarith
    norm_num1 at hfloor ⊢
    rw [hfloor]
    rfl
  have ha4 : a 4 = 3 := by
    unfold a
    have hfloor : Int.floor ((4 : ℝ) / sqrt 2 + 1 / 2) = (3 : ℤ) := by
      rw [Int.floor_eq_iff]
      constructor
      · have hs2pos : 0 < sqrt 2 := sqrt_pos.2 (by norm_num)
        have hs2le : sqrt 2 ≤ (8 / 5 : ℝ) := by
          rw [sqrt_le_left (by norm_num)]
          norm_num
        have hle : (5 / 2 : ℝ) ≤ 4 / sqrt 2 := by
          rw [le_div_iff₀ hs2pos]
          nlinarith
        nlinarith
      · have hs2pos : 0 < sqrt 2 := sqrt_pos.2 (by norm_num)
        have hs2gt : (8 / 7 : ℝ) < sqrt 2 := by
          rw [lt_sqrt (by norm_num)]
          norm_num
        have hlt : 4 / sqrt 2 < (7 / 2 : ℝ) := by
          rw [div_lt_iff₀ hs2pos]
          nlinarith
        norm_num at hlt ⊢
        linarith
    norm_num1 at hfloor ⊢
    rw [hfloor]
    rfl
  have hdiff1 : a 5 - a (5 - 1) = 1 := by
    norm_num [ha5, ha4]
  have hmem : (5 : ℕ) ∈ A001953 := by
    unfold A001953
    refine ⟨2, by norm_num, ?_⟩
    unfold phi
    have hfloor : Int.floor ((2 : ℝ) * ((1 + sqrt 5) / 2) ^ 2) = (5 : ℤ) := by
      rw [Int.floor_eq_iff]
      constructor
      · have hs5sq : (sqrt 5) ^ 2 = (5 : ℝ) := sq_sqrt (by norm_num)
        nlinarith [sqrt_nonneg (5 : ℝ), hs5sq]
      · have hs5lt : sqrt 5 < (3 : ℝ) := by
          rw [sqrt_lt (show (0 : ℝ) ≤ 5 by norm_num) (show (0 : ℝ) ≤ 3 by norm_num)]
          norm_num
        nlinarith [sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), hs5lt]
    change 5 = (Int.floor ((2 : ℝ) * ((1 + sqrt 5) / 2) ^ 2)).toNat
    rw [hfloor]
    rfl
  have hdiff0 : a 5 - a (5 - 1) = 0 := by
    exact ((h.2 5 (by norm_num)).2).mpr hmem
  omega
