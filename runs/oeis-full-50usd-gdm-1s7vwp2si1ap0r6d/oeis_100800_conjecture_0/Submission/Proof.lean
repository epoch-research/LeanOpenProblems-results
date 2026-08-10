import FormalConjectures.Util.ProblemImports
open Nat Function Classical

def sum_digits (n : ℕ) : ℕ :=
  (Nat.digits 10 n).sum

def f (n : ℕ) : ℕ := n + sum_digits n

lemma ofDigits_zero (b : ℕ) (l : List ℕ) (h : l.sum = 0) : Nat.ofDigits b l = 0 := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.sum_cons] at h
    have hx : x = 0 := by omega
    have hxs : xs.sum = 0 := by omega
    simp [Nat.ofDigits, hx, ih hxs]

lemma sum_digits_pos {n : ℕ} (h : n ≠ 0) : sum_digits n > 0 := by
  unfold sum_digits
  by_contra hc
  have h_zero : (Nat.digits 10 n).sum = 0 := by omega
  have h_of_digits := ofDigits_zero 10 (Nat.digits 10 n) h_zero
  rw [Nat.ofDigits_digits] at h_of_digits
  exact h h_of_digits

lemma f_gt_self {n : ℕ} (h : n ≠ 0) : f n > n := by
  unfold f
  have h_pos := sum_digits_pos h
  omega

lemma iterate_f_gt_self (k : ℕ) {n : ℕ} (h : n ≠ 0) : Nat.iterate f k n ≠ 0 := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rw [Function.iterate_succ']
    simp only [Function.comp_apply]
    have h_f := f_gt_self ih
    omega

noncomputable def A100800 (n : ℕ) : ℕ :=
  let P (k : ℕ) : Prop := n ∣ Nat.iterate f (k + 1) n
  dite (∃ k, P k)
    (fun h_exists =>
      let k₀ : ℕ := Nat.find h_exists
      Nat.iterate f (k₀ + 1) n)
    (fun _ => 0)

theorem oeis_100800_conjecture_0 : ∀ (n : ℕ), n ≠ 0 → A100800 n ≠ 0 := by
  intro n hn
  unfold A100800
  by_cases h : ∃ k, n ∣ Nat.iterate f (k + 1) n
  · rw [dif_pos h]
    intro h_zero
    let k₀ := Nat.find h
    have h_gt : Nat.iterate f (k₀ + 1) n ≠ 0 := iterate_f_gt_self (k₀ + 1) hn
    exact h_gt h_zero
  · sorry
