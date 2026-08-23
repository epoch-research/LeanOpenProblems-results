import FormalConjectures.Util.ProblemImports

open Nat

set_option maxRecDepth 2000000
set_option maxHeartbeats 8000000

/-- Search predicate matching the conjecture. -/
def SunGood (n : ℕ) : Prop :=
  (∃ (a b : ℕ), 2 ^ a * 3 ^ b ≤ n ∧ Nat.Prime (6 * (n - 2 ^ a * 3 ^ b) + 1))
  ∨
  (∃ (a b : ℕ), 2 ^ a * 3 ^ b < n ∧ Nat.Prime (6 * (n - 2 ^ a * 3 ^ b) - 1))

def checkM (n m : ℕ) : Bool :=
  decide (m ≤ n ∧ Nat.Prime (6 * (n - m) + 1))
    || decide (m < n ∧ Nat.Prime (6 * (n - m) - 1))

def checkFrom : ℕ → ℕ → ℕ → Bool
  | _, _, 0 => false
  | n, m, fuel + 1 =>
      if m = 0 ∨ n < m then false
      else if checkM n m then true else checkFrom n (m * 2) fuel

def check3 : ℕ → ℕ → ℕ → Bool
  | _, _, 0 => false
  | n, tb, fuel + 1 =>
      if tb = 0 ∨ n < tb then false
      else if checkFrom n tb (fuel + 1) then true else check3 n (tb * 3) fuel

def check (n : ℕ) : Bool := check3 n 1 (n + 8)

lemma checkM_true {n m : ℕ} (h : checkM n m = true) :
    (m ≤ n ∧ Nat.Prime (6 * (n - m) + 1))
      ∨ (m < n ∧ Nat.Prime (6 * (n - m) - 1)) := by
  unfold checkM at h
  rw [Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h
  exact h

lemma sunGood_of_checkM {n m : ℕ} (h : checkM n m = true)
    (hex : ∃ a b, m = 2 ^ a * 3 ^ b) : SunGood n := by
  obtain ⟨a, b, rfl⟩ := hex
  refine (checkM_true h).elim ?_ ?_
  · intro ⟨hle, hp⟩; exact Or.inl ⟨a, b, hle, hp⟩
  · intro ⟨hlt, hp⟩; exact Or.inr ⟨a, b, hlt, hp⟩

lemma checkFrom_sound (n m fuel : ℕ) (h : checkFrom n m fuel = true)
    (hex : ∃ a b, m = 2 ^ a * 3 ^ b) : SunGood n := by
  induction fuel generalizing m with
  | zero => simp [checkFrom] at h
  | succ fuel ih =>
      rw [checkFrom] at h
      by_cases hm : m = 0 ∨ n < m
      · rw [if_pos hm] at h; cases h
      · rw [if_neg hm] at h
        by_cases hM : checkM n m = true
        · rw [if_pos hM] at h; exact sunGood_of_checkM hM hex
        · rw [if_neg hM] at h
          obtain ⟨a, b, rfl⟩ := hex
          exact ih _ h ⟨a + 1, b, by rw [pow_succ]; ac_rfl⟩

lemma check3_sound (n tb fuel : ℕ) (h : check3 n tb fuel = true)
    (hex : ∃ a b, tb = 2 ^ a * 3 ^ b) : SunGood n := by
  induction fuel generalizing tb with
  | zero => simp [check3] at h
  | succ fuel ih =>
      rw [check3] at h
      by_cases ht : tb = 0 ∨ n < tb
      · rw [if_pos ht] at h; cases h
      · rw [if_neg ht] at h
        by_cases hF : checkFrom n tb (fuel + 1) = true
        · rw [if_pos hF] at h; exact checkFrom_sound n tb (fuel + 1) hF hex
        · rw [if_neg hF] at h
          obtain ⟨a, b, rfl⟩ := hex
          exact ih _ h ⟨a, b + 1, by rw [pow_succ, mul_assoc]⟩

lemma check_sound {n : ℕ} (h : check n = true) : SunGood n :=
  check3_sound n 1 (n + 8) h ⟨0, 0, by simp⟩

lemma check_lt_80 : (List.range 80).all (fun n => !decide (1 < n) || check n) = true :=
  rfl

lemma check_lt_200 : (List.range 200).all (fun n => !decide (1 < n) || check n) = true :=
  rfl

lemma sunGood_of_lt_80 {n : ℕ} (hn : 1 < n) (hN : n < 80) : SunGood n := by
  have hall := List.all_eq_true.mp check_lt_80 n (List.mem_range.mpr hN)
  have : check n = true := by
    simp [decide_eq_true hn] at hall
    exact hall
  exact check_sound this
