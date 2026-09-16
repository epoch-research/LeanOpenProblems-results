import Mathlib

def a (n : ℕ) : ℕ :=
  match n with
  | 0 => 1
  | 1 => 3
  | (n + 2) => 2 * a (n + 1) + 2 * a n
termination_by n

def shift_seq {L : ℕ} (σ : Fin L → ℕ) (k : ℕ) : Fin L → ℕ :=
  fun i => σ i + k

def map1 {L : ℕ} (σ : Fin L → ℕ) : Fin (L + 1) → ℕ :=
  Fin.snoc (shift_seq σ 1) 1

def map2 {L : ℕ} (σ : Fin L → ℕ) : Fin (L + 1) → ℕ :=
  Fin.snoc σ 1

def map3 {L : ℕ} (σ : Fin L → ℕ) : Fin (L + 2) → ℕ :=
  Fin.snoc (Fin.snoc (shift_seq σ 1) 1) 2

def map4 {L : ℕ} (σ : Fin L → ℕ) : Fin (L + 2) → ℕ :=
  Fin.snoc (Fin.snoc (shift_seq σ 2) 1) 2

def gen : (L : ℕ) → List (Fin L → ℕ)
| 0 => []
| 1 => [fun _ => 1]
| 2 =>
  let w1 := gen 1
  (w1.map map1 ++ w1.map map2) ++ [Fin.snoc (fun _ => 1) 2]
| L + 2 =>
  let w_prev := gen (L + 1)
  let w_prev2 := gen L
  let end1 := w_prev.map map1 ++ w_prev.map map2
  let end2 := w_prev2.map map3 ++ w_prev2.map map4
  end1 ++ end2

def ValidGen {L : ℕ} (x : Fin L → ℕ) : Prop :=
  (∀ i, x i > 0) ∧ (∃ i, x i = 1)
