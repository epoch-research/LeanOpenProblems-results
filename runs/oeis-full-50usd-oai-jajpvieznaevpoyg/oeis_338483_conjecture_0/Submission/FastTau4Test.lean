import FormalConjectures.Util.ProblemImports
open Finset Nat Set
noncomputable def tau (n : ℕ) : ℕ := (Nat.divisors n).card

def countPredLoop (P : ℕ → Prop) [DecidablePred P] : ℕ → ℕ → ℕ
  | 0, acc => acc
  | n+1, acc => countPredLoop P n (if P n then acc+1 else acc)

def countPredFast (P : ℕ → Prop) [DecidablePred P] (n : ℕ) : ℕ := countPredLoop P n 0
lemma countPredLoop_eq (P : ℕ → Prop) [DecidablePred P] (n acc : ℕ) :
    countPredLoop P n acc = acc + Nat.count P n := by
  induction n generalizing acc with
  | zero => simp [countPredLoop]
  | succ n ih =>
      simp [countPredLoop, ih, Nat.count_succ]
      by_cases h : P n <;> simp [h, Nat.add_comm, Nat.add_left_comm]
lemma countPredFast_eq (P : ℕ → Prop) [DecidablePred P] (n : ℕ) :
    countPredFast P n = Nat.count P n := by simp [countPredFast, countPredLoop_eq]

lemma tau4Count_eq_count (p : ℕ) :
    ((Finset.Ico 1 p).filter (fun k => tau k = 4)).card = Nat.count (fun k => 1 ≤ k ∧ tau k = 4) p := by
  change ((Finset.Ico 1 p).filter (fun k => tau k = 4)).card = Nat.count (fun k => 1 ≤ k ∧ tau k = 4) p
  rw [Nat.count_eq_card_filter_range]
  apply Finset.card_bij (fun k _ => k)
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_range] at hk ⊢
    exact ⟨hk.1.2, hk.1.1, hk.2⟩
  · intro a _ b _ h; exact h
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_range] at hk ⊢
    exact ⟨k, ⟨⟨hk.2.1, hk.1⟩, hk.2.2⟩, rfl⟩

example : ((Finset.Ico 1 100000).filter (fun k => tau k = 4)).card = 23327 := by
  rw [tau4Count_eq_count, ← countPredFast_eq]
  unfold tau
  native_decide
