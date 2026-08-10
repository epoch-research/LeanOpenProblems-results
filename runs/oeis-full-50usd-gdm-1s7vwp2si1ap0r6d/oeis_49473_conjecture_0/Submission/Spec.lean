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
theorem sqrt_two_bounds : (8/7 : ℝ) < sqrt 2 ∧ sqrt 2 < (10/7 : ℝ) := by
  constructor
  · rw [lt_sqrt (by norm_num)]
    norm_num
  · rw [sqrt_lt' (by norm_num)]
    norm_num

theorem a_five_eq_four : a 5 = 4 := by
  unfold a
  have h_floor : Int.floor (((5 : ℕ) : ℝ) / sqrt 2 + 1 / 2) = 4 := by
    rw [Int.floor_eq_iff]
    have h1 : (8/7 : ℝ) < sqrt 2 := sqrt_two_bounds.1
    have h2 : sqrt 2 < (10/7 : ℝ) := sqrt_two_bounds.2
    constructor
    · -- 4 ≤ 5 / sqrt 2 + 1 / 2
      have : 5 / sqrt 2 > 5 / (10/7 : ℝ) := by
        apply div_lt_div_of_pos_left (by norm_num) (by norm_num) h2
      linarith
    · -- 5 / sqrt 2 + 1 / 2 < 5
      have : 5 / sqrt 2 < 5 / (8/7 : ℝ) := by
        apply div_lt_div_of_pos_left (by norm_num) (by norm_num) h1
      linarith
  rw [h_floor]
  rfl

theorem a_four_eq_three : a 4 = 3 := by
  unfold a
  have h_floor : Int.floor (((4 : ℕ) : ℝ) / sqrt 2 + 1 / 2) = 3 := by
    rw [Int.floor_eq_iff]
    have h1 : (8/7 : ℝ) < sqrt 2 := sqrt_two_bounds.1
    have h2 : sqrt 2 < (10/7 : ℝ) := sqrt_two_bounds.2
    constructor
    · -- 3 ≤ 4 / sqrt 2 + 1 / 2
      have : 4 / sqrt 2 > 4 / (10/7 : ℝ) := by
        apply div_lt_div_of_pos_left (by norm_num) (by norm_num) h2
      linarith
    · -- 4 / sqrt 2 + 1 / 2 < 4
      have : 4 / sqrt 2 < 4 / (8/7 : ℝ) := by
        apply div_lt_div_of_pos_left (by norm_num) (by norm_num) h1
      linarith
  rw [h_floor]
  rfl

theorem sqrt_five_bounds : (2 : ℝ) < sqrt 5 ∧ sqrt 5 < (7/3 : ℝ) := by
  constructor
  · rw [lt_sqrt (by norm_num)]
    norm_num
  · rw [sqrt_lt' (by norm_num)]
    norm_num

theorem not_five_mem_A001954 : 5 ∉ A001954 := by
  intro h
  unfold A001954 at h
  rcases h with ⟨k, hk_pos, hk_eq⟩
  have h1 : (2 : ℝ) < sqrt 5 := sqrt_five_bounds.1
  have h2 : sqrt 5 < (7/3 : ℝ) := sqrt_five_bounds.2
  have h_phi_pos : phi > 0 := by
    unfold phi
    linarith
  rcases k with _ | (_ | (_ | (_ | s)))
  · -- k = 0
    contradiction
  · -- k = 1
    have h_eq : ((0 + 1 : ℕ) : ℝ) = 1 := by norm_num
    rw [h_eq] at hk_eq
    rw [one_mul] at hk_eq
    have h_floor : Int.floor phi = 1 := by
      rw [Int.floor_eq_iff]
      unfold phi
      constructor
      · linarith
      · linarith
    rw [h_floor] at hk_eq
    contradiction
  · -- k = 2
    have h_eq : ((0 + 1 + 1 : ℕ) : ℝ) = 2 := by norm_num
    rw [h_eq] at hk_eq
    have h_floor : Int.floor (2 * phi) = 3 := by
      rw [Int.floor_eq_iff]
      unfold phi
      constructor
      · linarith
      · linarith
    rw [h_floor] at hk_eq
    contradiction
  · -- k = 3
    have h_eq : ((0 + 1 + 1 + 1 : ℕ) : ℝ) = 3 := by norm_num
    rw [h_eq] at hk_eq
    have h_floor : Int.floor (3 * phi) = 4 := by
      rw [Int.floor_eq_iff]
      unfold phi
      constructor
      · linarith
      · linarith
    rw [h_floor] at hk_eq
    contradiction
  · -- k = s + 4
    have h_eq : ((s + 1 + 1 + 1 + 1 : ℕ) : ℝ) = (s : ℝ) + 4 := by
      push_cast
      ring
    rw [h_eq] at hk_eq
    have hk_cast : ((s : ℝ) + 4) ≥ 4 := by
      have : (s : ℝ) ≥ 0 := by positivity
      linarith
    have h_mul_ge : ((s : ℝ) + 4) * phi ≥ 6 := by
      calc
        ((s : ℝ) + 4) * phi ≥ 4 * phi := by
          apply mul_le_mul_of_nonneg_right hk_cast h_phi_pos.le
        _ = 2 + 2 * sqrt 5 := by
          unfold phi
          ring
        _ ≥ 6 := by
          linarith
    have h_floor_ge : Int.floor (((s : ℝ) + 4) * phi) ≥ 6 := by
      rw [ge_iff_le]
      apply Int.le_floor.mpr
      exact h_mul_ge
    have hk_eq_int : (5 : ℤ) = Int.floor (((s : ℝ) + 4) * phi) := by
      have h_nonneg : Int.floor (((s : ℝ) + 4) * phi) ≥ 0 := by linarith
      have : ((Int.floor (((s : ℝ) + 4) * phi)).toNat : ℤ) = (Int.floor (((s : ℝ) + 4) * phi)) := by
        apply Int.toNat_of_nonneg
        exact h_nonneg
      rw [← this]
      rw [← hk_eq]
      rfl
    omega

theorem oeis_49473_conjecture_0.disproof :
  ¬ ((∀ (n : ℕ), 1 ≤ n → s (a n) < 1 / (n : ℝ) ^ 2 ∧ 1 / (n : ℝ) ^ 2 < s (a n - 1)) ∧
  (∀ (n : ℕ), 1 ≤ n →
    let diff : ℕ := a n - a (n - 1);
    (diff = 1 ↔ n ∈ A001954) ∧ (diff = 0 ↔ n ∈ A001953))) := by
  intro h
  rcases h with ⟨_, h2⟩
  have h5 : (a 5 - a 4 = 1 ↔ 5 ∈ A001954) ∧ (a 5 - a 4 = 0 ↔ 5 ∈ A001953) := by
    have h_spec := h2 5 (by norm_num)
    exact h_spec
  have h5_left := h5.left
  have h_a5 : a 5 = 4 := a_five_eq_four
  have h_a4 : a 4 = 3 := a_four_eq_three
  have h_diff : a 5 - a 4 = 1 := by
    rw [h_a5, h_a4]
  rw [h_diff] at h5_left
  have h_five_mem : 5 ∈ A001954 := h5_left.mp rfl
  exact not_five_mem_A001954 h_five_mem
