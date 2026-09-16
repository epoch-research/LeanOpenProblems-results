import Mathlib
import Submission.Helper10

open Finset

lemma sum_countP_eq {α} (l : List α) (f : α → ℕ) (S : Finset ℕ) (hS : ∀ x ∈ l, f x ∈ S) (p : α → Bool) :
  l.countP p = ∑ q ∈ S, l.countP (fun x => (f x == q) && p x) := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    rw [List.countP_cons]
    have hS_tl : ∀ x ∈ tl, f x ∈ S := fun x hx => hS x (List.mem_cons_of_mem _ hx)
    rw [ih hS_tl]
    have h_hd : f hd ∈ S := hS hd List.mem_cons_self
    have : (∑ q ∈ S, List.countP (fun x => (f x == q) && p x) (hd :: tl)) =
           ∑ q ∈ S, (List.countP (fun x => (f x == q) && p x) tl + if f hd = q ∧ p hd = true then 1 else 0) := by
      apply sum_congr rfl
      intros q hq
      rw [List.countP_cons]
      have : (((f hd == q) && p hd) = true) ↔ (f hd = q ∧ p hd = true) := by
        simp only [Bool.and_eq_true, beq_iff_eq]
      by_cases h_cond : ((f hd == q) && p hd) = true
      · rw [if_pos h_cond, if_pos (this.mp h_cond)]
      · rw [if_neg h_cond, if_neg (by intro h; exact h_cond (this.mpr h))]
    rw [this, sum_add_distrib]
    by_cases hp : p hd = true
    · rw [if_pos hp]
      have : (∑ q ∈ S, if f hd = q ∧ p hd = true then 1 else 0) = 1 := by
        have H_eq : (∑ q ∈ S, if f hd = q ∧ p hd = true then 1 else 0) = ∑ q ∈ S, if f hd = q then 1 else 0 := by
          apply sum_congr rfl
          intros q hq
          have : (f hd = q ∧ p hd = true) ↔ f hd = q := by simp [hp]
          by_cases h_eq : f hd = q
          · rw [if_pos (this.mpr h_eq), if_pos h_eq]
          · rw [if_neg (by intro h; exact h_eq (this.mp h)), if_neg h_eq]
        rw [H_eq, sum_ite_eq, if_pos h_hd]
      omega
    · rw [if_neg hp]
      have : (∑ q ∈ S, if f hd = q ∧ p hd = true then 1 else 0) = 0 := by
        have H_eq : (∑ q ∈ S, if f hd = q ∧ p hd = true then 1 else 0) = ∑ q ∈ S, 0 := by
          apply sum_congr rfl
          intros q hq
          have : ¬(f hd = q ∧ p hd = true) := by intro h; exact hp h.2
          rw [if_neg this]
        rw [H_eq, sum_const_zero]
      omega

lemma sum_countP_filter {α} (l : List α) (f : α → ℕ) (S : Finset ℕ) (hS : ∀ x ∈ l, f x ∈ S) (p : α → Bool) :
  l.countP p = ∑ q ∈ S, (l.filter (fun x => f x == q)).countP p := by
  rw [sum_countP_eq l f S hS p]
  apply sum_congr rfl
  intros q hq
  rw [List.countP_filter]
  have H : (fun (x : α) => p x && (f x == q)) = (fun x => (f x == q) && p x) := by
    ext x
    exact Bool.and_comm (p x) (f x == q)
  rw [H]
