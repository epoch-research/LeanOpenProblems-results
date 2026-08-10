import Mathlib

open Nat

set_option maxRecDepth 200000
set_option maxHeartbeats 10000000

def binary_sqrt_aux (n low high fuel : ℕ) : ℕ :=
  match fuel with
  | 0 => low
  | fuel' + 1 =>
    if low + 1 ≥ high then low
    else
      let mid := (low + high) / 2
      if mid * mid ≤ n then binary_sqrt_aux n mid high fuel'
      else binary_sqrt_aux n low mid fuel'

def fast_sqrt (n : ℕ) : ℕ :=
  binary_sqrt_aux n 0 (n + 1) 32

def search_z (q x y z : ℕ) : Option (ℕ × ℕ) :=
  match z with
  | 0 => none
  | z' + 1 =>
    let z := z'
    if x^2 + y^2 + z^2 = q then
      let val := x^2 + 8*y^2 + 16*z^2
      let r := fast_sqrt val
      if h_eq : r * r = val then
        some (z, r)
      else
        search_z q x y z'
    else
      search_z q x y z'

lemma search_z_correct (q x y z : ℕ) : ∀ {sol : ℕ × ℕ}, search_z q x y z = some sol →
  x^2 + y^2 + sol.1^2 = q ∧ sol.2 * sol.2 = x^2 + 8*y^2 + 16*sol.1^2 := by
  induction z with
  | zero =>
    simp [search_z]
  | succ z' ih =>
    intro sol h
    simp only [search_z] at h
    split at h
    · rename_i h_sum
      split at h
      · rename_i h_sq
        simp only [Option.some.injEq] at h
        rw [← h]
        exact ⟨h_sum, h_sq⟩
      · exact ih h
    · exact ih h

def search_y (q x y : ℕ) : Option (ℕ × ℕ × ℕ × ℕ) :=
  match y with
  | 0 => none
  | y' + 1 =>
    let y := y'
    if x^2 + y^2 ≤ q then
      let q_sqrt := fast_sqrt q
      match search_z q x y (q_sqrt + 1) with
      | some (z, r) => some (x, y, z, r)
      | none => search_y q x y'
    else
      search_y q x y'

lemma search_y_correct (q x y : ℕ) : ∀ {sol : ℕ × ℕ × ℕ × ℕ}, search_y q x y = some sol →
  sol.1 = x ∧ sol.2.1 < y ∧ sol.1^2 + sol.2.1^2 + sol.2.2.1^2 = q ∧ sol.2.2.2 * sol.2.2.2 = sol.1^2 + 8*sol.2.1^2 + 16*sol.2.2.1^2 := by
  induction y with
  | zero =>
    simp [search_y]
  | succ y' ih =>
    intro sol h
    simp only [search_y] at h
    split at h
    · split at h
      · rename_i h_sz
        simp only [Option.some.injEq] at h
        have h_sz_prop := search_z_correct q x y' (fast_sqrt q + 1) h_sz
        rw [← h]
        simp only
        refine ⟨True.intro, by omega, h_sz_prop.1, h_sz_prop.2⟩
      · have ih' := ih h
        refine ⟨ih'.1, by omega, ih'.2.2⟩
    · have ih' := ih h
      refine ⟨ih'.1, by omega, ih'.2.2⟩

def search_x (q x : ℕ) : Option (ℕ × ℕ × ℕ × ℕ) :=
  match x with
  | 0 => none
  | x' + 1 =>
    let x := x'
    if x^2 ≤ q then
      match search_y q x (x + 1) with
      | some sol => some sol
      | none => search_x q x'
    else
      search_x q x'

lemma search_x_correct (q x : ℕ) : ∀ {sol : ℕ × ℕ × ℕ × ℕ}, search_x q x = some sol →
  sol.1 < x ∧ sol.1 ≥ sol.2.1 ∧ sol.1^2 + sol.2.1^2 + sol.2.2.1^2 = q ∧ sol.2.2.2 * sol.2.2.2 = sol.1^2 + 8*sol.2.1^2 + 16*sol.2.2.1^2 := by
  induction x with
  | zero =>
    simp [search_x]
  | succ x' ih =>
    intro sol h
    simp only [search_x] at h
    split at h
    · split at h
      · rename_i h_sy
        simp only [Option.some.injEq] at h
        rw [h] at h_sy
        have h_sy_prop := search_y_correct q x' (x' + 1) h_sy
        refine ⟨by omega, by omega, h_sy_prop.2.2⟩
      · have ih' := ih h
        refine ⟨by omega, ih'.2.1, ih'.2.2⟩
    · have ih' := ih h
      refine ⟨by omega, ih'.2.1, ih'.2.2⟩

def find_H0_sol (q : ℕ) : Option (ℕ × ℕ × ℕ × ℕ) :=
  let q_sqrt := fast_sqrt q
  search_x q (q_sqrt + 1)

def has_sol_w0 (n : ℕ) : Prop :=
  ∃ x y z, x^2 + y^2 + z^2 = n ∧ x ≥ y ∧ (x^2 + 8*y^2 + 16*z^2).sqrt * (x^2 + 8*y^2 + 16*z^2).sqrt = x^2 + 8*y^2 + 16*z^2

lemma find_H0_sol_correct (q : ℕ) {sol : ℕ × ℕ × ℕ × ℕ} (h : find_H0_sol q = some sol) :
  has_sol_w0 q := by
  unfold find_H0_sol at h
  have h_sx := search_x_correct q (fast_sqrt q + 1) h
  use sol.1, sol.2.1, sol.2.2.1
  refine ⟨h_sx.2.2.1, h_sx.2.1, ?_⟩
  have h_sq_eq : sol.2.2.2 * sol.2.2.2 = sol.1^2 + 8*sol.2.1^2 + 16*sol.2.2.1^2 := h_sx.2.2.2
  rw [← h_sq_eq]
  rw [Nat.sqrt_eq]

