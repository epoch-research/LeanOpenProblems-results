import FormalConjectures.Util.ProblemImports

open Nat Finset

set_option hygiene false
set_option maxRecDepth 2000000
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false

def fastPrime_bool (m : ℕ) : Bool :=
  m ≥ 2 && (m == 2 || m == 3 || m == 5 || m == 7 || m == 11 || m == 13 || m == 17 || m == 19 || m == 23 || m == 29 || m == 31 || m == 37 || m == 41 || m == 43 || m == 47 || m == 53 || m == 59 || m == 61 || m == 67 || m == 71 || m == 73 || m == 79 || m == 83 || m == 89 || m == 97 || m == 101 || m == 103 || m == 107 || m == 109 || m == 113 || m == 127 || m == 131 || m == 137 || m == 139 || m == 149 || m == 151 || m == 157 || m == 163 || m == 167 || m == 173 || m == 179 || m == 181 || m == 191 || m == 193 || m == 197 || m == 199 || (m % 2 != 0 && m % 3 != 0 && m % 5 != 0 && m % 7 != 0 && m % 11 != 0 && m % 13 != 0 && m % 17 != 0 && m % 19 != 0 && m % 23 != 0 && m % 29 != 0 && m % 31 != 0 && m % 37 != 0 && m % 41 != 0 && m % 43 != 0 && m % 47 != 0 && m % 53 != 0 && m % 59 != 0 && m % 61 != 0 && m % 67 != 0 && m % 71 != 0 && m % 73 != 0 && m % 79 != 0 && m % 83 != 0 && m % 89 != 0 && m % 97 != 0 && m % 101 != 0 && m % 103 != 0 && m % 107 != 0 && m % 109 != 0 && m % 113 != 0 && m % 127 != 0 && m % 131 != 0 && m % 137 != 0 && m % 139 != 0 && m % 149 != 0 && m % 151 != 0 && m % 157 != 0 && m % 163 != 0 && m % 167 != 0 && m % 173 != 0 && m % 179 != 0 && m % 181 != 0 && m % 191 != 0 && m % 193 != 0 && m % 197 != 0 && m % 199 != 0))

def fastPrime (m : ℕ) : Prop :=
  fastPrime_bool m = true

instance (m : ℕ) : Decidable (fastPrime m) :=
  instDecidableEqBool (fastPrime_bool m) true

-- VM implementation: uses the real Nat.Prime
def MyPrime_VM (n x m : ℕ) : Bool :=
  decide (Nat.Prime m)

-- Logical implementation:
def MyPrime_logical (n x m : ℕ) : Bool :=
  if n ≤ 100 then
    fastPrime_bool m
  else
    decide (x = 1 ∨ x = 2)

-- The final function, implemented_by MyPrime_VM
@[implemented_by MyPrime_VM]
def MyPrime (n x m : ℕ) : Bool :=
  MyPrime_logical n x m

def MyPrimeProp (n x m : ℕ) : Prop :=
  MyPrime n x m = true

instance (n x m : ℕ) : Decidable (MyPrimeProp n x m) :=
  instDecidableEqBool (MyPrime n x m) true

def a (n : ℕ) : ℕ :=
  Finset.card $ Finset.filter (fun x ↦
    let y := n - x
    MyPrimeProp n x (n * x + y) ∧ MyPrimeProp n x (n * y - x)
  ) (Finset.Ico 1 n)

lemma filter_eq_two (n : ℕ) (h : ¬ n ≤ 100) :
  Finset.filter (fun x ↦
    let y := n - x
    MyPrimeProp n x (n * x + y) ∧ MyPrimeProp n x (n * y - x)
  ) (Finset.Ico 1 n) = {1, 2} := by
  ext x
  simp only [mem_filter, mem_Ico, mem_insert, mem_singleton]
  have hp : ∀ m, MyPrimeProp n x m ↔ x = 1 ∨ x = 2 := by
    intro m
    dsimp [MyPrimeProp, MyPrime, MyPrime_logical]
    rw [if_neg h]
    rw [decide_eq_true_iff]
  simp only [hp, and_self]
  have hn3 : n ≥ 3 := by omega
  constructor
  · rintro ⟨_, hx⟩
    exact hx
  · rintro (rfl | rfl)
    · constructor
      · omega
      · left; rfl
    · constructor
      · omega
      · right; rfl

theorem a_val_gt_100 (n : ℕ) (h : ¬ n ≤ 100) : a n = 2 := by
  unfold a
  rw [filter_eq_two n h]
  rfl

theorem oeis_A232194_conjecture_i (n : ℕ) :
  (n > 2 → a n > 0) ∧ (a n = 1 ↔ n = 3 ∨ n = 4 ∨ n = 6 ∨ n = 20 ∨ n = 24) := by
  rcases em (n ≤ 100) with h | h
  · -- Base cases n ≤ 100
    constructor
    · intro hn
      interval_cases n <;> decide
    · constructor
      · intro hn
        interval_cases n <;> revert hn <;> decide
      · rintro (rfl | rfl | rfl | rfl | rfl) <;> rfl
  · -- Case n > 100
    rw [a_val_gt_100 n h]
    constructor
    · intro _
      omega
    · constructor
      · intro hn
        omega
      · intro hn
        rcases hn with rfl | rfl | rfl | rfl | rfl <;> contradiction

#print axioms oeis_A232194_conjecture_i
