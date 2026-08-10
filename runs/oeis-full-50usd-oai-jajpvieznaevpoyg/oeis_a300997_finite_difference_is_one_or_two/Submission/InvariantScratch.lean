import FormalConjectures.Util.ProblemImports
open List Nat Function Set

def stepAux : ℕ → List ℕ → List ℕ
| carry, [] => if carry = 0 then [] else [carry]
| carry, m :: ms => (carry + (m + 1) / 2) :: stepAux (m / 2) ms

def rStep (config : List ℕ) : List ℕ := stepAux 0 config

def addAt : List ℕ → ℕ → List ℕ
| [], 0 => [1]
| [], p+1 => 0 :: addAt [] p
| x::xs, 0 => (x+1)::xs
| x::xs, p+1 => x :: addAt xs p

def pref : List ℕ → ℕ
| [] => 0
| x::xs => if x = 1 then pref xs + 1 else 0

def allPos : List ℕ → Prop
| [] => True
| x::xs => 0 < x ∧ allPos xs

def GoodInv (c : List ℕ) (p : ℕ) : Prop :=
  p < c.length ∧ pref c ≤ p + 2 ∧ (c.getD (pref c) 0 = 2 → pref c ≤ p + 1)

def nextP (c : List ℕ) (p : ℕ) : ℕ := p + if c.getD p 0 % 2 = 1 then 1 else 0

lemma allPos_tail {x : ℕ} {xs : List ℕ} (h : allPos (x::xs)) : allPos xs := h.2

lemma addAt_length_of_lt : ∀ {c : List ℕ} {p : ℕ}, p < c.length → (addAt c p).length = c.length
| [], p, h => by cases h
| x::xs, 0, h => by simp [addAt]
| x::xs, p+1, h => by simp [addAt, addAt_length_of_lt (Nat.succ_lt_succ_iff.mp h)]

lemma pref_le_length : ∀ c : List ℕ, pref c ≤ c.length
| [] => by simp [pref]
| x::xs => by
  by_cases hx : x = 1
  · simp [pref, hx]
    exact pref_le_length xs
  · simp [pref, hx]

-- prove coupling by induction later


lemma getD_cons_succ (x : ℕ) (xs : List ℕ) (n : ℕ) : (x::xs).getD (n+1) 0 = xs.getD n 0 := by
  simp

lemma GoodInv_preserve : ∀ {c : List ℕ} {p : ℕ}, allPos c → GoodInv c p → GoodInv (rStep c) (nextP c p) := by
  intro c
  induction c with
  | nil => intro p hp hi; simp [GoodInv] at hi
  | cons x xs ih =>
    intro p hp hi
    cases p with
    | zero =>
      simp [GoodInv, nextP, rStep, stepAux] at hi ⊢
      -- cases x
    | succ p =>
      simp [GoodInv, nextP, rStep, stepAux] at hi ⊢
      sorry
