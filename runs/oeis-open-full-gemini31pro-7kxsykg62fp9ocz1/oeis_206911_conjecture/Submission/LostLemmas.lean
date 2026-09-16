import Mathlib

open Real Finset Filter Topology Nat

lemma floor_add_floor_le (a b : ℝ) : Int.floor a + Int.floor b ≤ Int.floor (a + b) := by
  rw [Int.le_floor]
  push_cast
  exact add_le_add (Int.floor_le a) (Int.floor_le b)

lemma floor_add_le_floor_add_floor_add_one (a b : ℝ) : Int.floor (a + b) ≤ Int.floor a + Int.floor b + 1 := by
  rw [Int.floor_le_iff]
  push_cast
  have h1 := Int.lt_floor_add_one a
  have h2 := Int.lt_floor_add_one b
  linarith

lemma floor_sub_floor (x y : ℝ) : Int.floor x - Int.floor y = Int.floor (x - y) ∨ Int.floor x - Int.floor y = Int.floor (x - y) + 1 := by
  have h1 := floor_add_floor_le y (x - y)
  have h2 := floor_add_le_floor_add_floor_add_one y (x - y)
  have : y + (x - y) = x := add_sub_cancel y x
  rw [this] at h1 h2
  omega

lemma diff_eq_2_or_3 {x y : ℝ} (h_pos_y : 0 ≤ y) (h_pos_x : 0 ≤ x) (h_bound : 1 < x - y ∧ x - y < 2) :
    let diff := 1 + (Int.toNat (Int.floor x)) - (Int.toNat (Int.floor y))
    diff = 2 ∨ diff = 3 := by
  intro diff
  have h_floor : Int.floor (x - y) = 1 := by
    rw [Int.floor_eq_iff]
    push_cast
    exact ⟨h_bound.left.le, by linarith [h_bound.right]⟩
  have h_cases := floor_sub_floor x y
  rw [h_floor] at h_cases
  have h_cast_y : (Int.toNat (Int.floor y) : ℤ) = Int.floor y := Int.toNat_of_nonneg (Int.floor_nonneg.mpr h_pos_y)
  have h_cast_x : (Int.toNat (Int.floor x) : ℤ) = Int.floor x := Int.toNat_of_nonneg (Int.floor_nonneg.mpr h_pos_x)
  dsimp [diff]
  omega

lemma c_mono_le {c : ℕ → ℝ} (h : ∀ n, 1 ≤ n → c n ≤ c (n + 1)) (n m : ℕ) (hn : 1 ≤ n) (hnm : n ≤ m) : c n ≤ c m := by
  induction' m, hnm using Nat.le_induction with k hk ih
  · rfl
  · have h_k : c k ≤ c (k + 1) := h k (hn.trans hk)
    exact ih.trans h_k

lemma c_upper_bound (n : ℕ) : exp (harmonic (n + 1)) - exp (harmonic n) < exp (harmonic (n + 1)) / (n + 1 : ℝ) := by
  have h1 : (harmonic n : ℝ) = harmonic (n + 1) - 1 / (n + 1 : ℝ) := by
    rw [harmonic_succ]
    push_cast
    ring
  have h2 : exp (harmonic n) = exp (harmonic (n + 1)) * exp (- (1 / (n + 1 : ℝ))) := by
    calc
      exp (harmonic n) = exp (harmonic (n + 1) - 1 / (n + 1 : ℝ)) := by rw [h1]
      _ = exp (harmonic (n + 1) + - (1 / (n + 1 : ℝ))) := by ring_nf
      _ = exp (harmonic (n + 1)) * exp (- (1 / (n + 1 : ℝ))) := by rw [exp_add]
  rw [h2]
  have h3 : -(1 / (n + 1 : ℝ)) + 1 < exp (- (1 / (n + 1 : ℝ))) := by
    apply add_one_lt_exp
    have : (n + 1 : ℝ) ≠ 0 := by positivity
    exact neg_ne_zero.mpr (one_div_ne_zero this)
  have h4 : 1 - exp (- (1 / (n + 1 : ℝ))) < 1 / (n + 1 : ℝ) := by linarith
  calc
    exp (harmonic (n + 1)) - exp (harmonic (n + 1)) * exp (- (1 / (n + 1 : ℝ))) = exp (harmonic (n + 1)) * (1 - exp (- (1 / (n + 1 : ℝ)))) := by ring
    _ < exp (harmonic (n + 1)) * (1 / (n + 1 : ℝ)) := by
      apply mul_lt_mul_of_pos_left h4 (exp_pos _)
    _ = exp (harmonic (n + 1)) / (n + 1 : ℝ) := by ring

