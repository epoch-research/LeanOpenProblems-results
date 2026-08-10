import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option linter.unusedVariables false

open Nat Finset Set

namespace MyNamespace

def lookup_list : List ℕ := [
  1, 0, 1, 0, 2, 0, 2, 1, 2, 1, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2,
  2, 4, 2, 3, 2, 3, 2, 3, 4, 3, 4, 1, 5, 1, 5, 3, 5, 4, 3, 4,
  5, 1, 5, 3, 4, 4, 3, 7, 2, 4, 4, 7, 6, 6, 4, 4, 5, 3, 7, 5,
  5, 8, 6, 7, 3, 6, 8, 6, 5, 4, 3, 4, 6, 7, 3, 7, 6, 10, 7, 5,
  9, 3, 11, 4, 9, 7, 7, 10, 5, 9, 7, 7, 10, 8, 7, 5, 5, 9, 5, 9,
  9, 11, 7, 8, 10, 5, 11, 7, 12, 6, 8, 7, 7, 9, 10, 11, 8, 10, 9, 6,
  9, 7, 12, 10, 9, 10, 5, 13, 12, 10, 11, 7, 14, 8, 14, 11, 9, 15, 12, 14,
  7, 10, 13, 7, 11, 6, 9, 11, 10, 9, 13, 10, 14, 9, 13, 10, 13, 8, 15, 10,
  13, 18, 14, 13, 10, 14, 14, 13, 7, 10, 8, 11, 15, 10, 10, 19, 17, 19, 12, 10,
  16, 9, 15, 8, 15, 15, 13, 19, 8, 17, 12, 14, 20, 14, 11, 8, 6, 16, 9, 19,
  18, 21, 14, 15, 16, 11, 20, 16, 19, 14, 9, 13, 15, 18, 20, 20, 17, 16, 15, 10,
  11, 9, 19, 16, 9, 15, 15, 22, 14, 11, 21, 11, 25, 15, 21, 17, 15, 21, 19, 19,
  16, 19, 18, 14, 12, 10, 16, 22, 20, 20, 11, 19, 25, 14, 24, 13, 17, 15, 24, 17,
  18, 20, 24, 18, 18, 22, 11, 21, 16, 16, 9, 17, 20, 22, 19, 27, 20, 20, 27, 13,
  22, 16, 23, 16, 19, 25, 22, 28, 16, 20, 18, 20, 26, 13, 11, 18, 11, 23, 14, 20,
  29, 23, 21, 21, 24, 15, 20, 26, 17, 22, 14, 31, 18, 26, 28, 27, 24, 21, 22, 17,
  23, 17, 17, 22, 23, 25, 27, 23, 23, 20, 28, 16, 26, 26, 22, 23, 15, 38, 26, 16,
  25, 21, 28, 10, 22, 24, 22, 30, 21, 26, 12, 21, 38, 22, 24, 20, 24, 31, 30, 25,
  22, 31, 36, 22, 18, 16, 26, 22, 22, 18, 17, 23, 32, 22, 20, 26, 24, 26, 33, 16,
  30, 23, 28, 26, 23, 31, 30, 38, 30, 30, 19, 21, 29, 20, 30, 32, 25, 34, 19, 32,
  33, 22, 40, 18, 30, 18, 24, 31, 23, 28, 24, 31, 30, 30, 31, 26, 22, 22, 28, 28,
  20, 31, 32, 36, 23, 27, 25, 32, 32, 28, 33, 23, 30, 33, 30, 35, 27, 44, 31, 25,
  29, 13, 26, 17, 38, 32, 25, 37, 25, 22, 26, 30, 38, 27, 32, 26, 30, 35, 34, 33,
  31, 39, 28, 31, 27, 26, 30, 39, 27, 27, 25, 38, 46, 22, 39, 26, 27, 32, 35, 27,
  39, 26, 38, 29, 23, 44, 32, 42, 31, 22, 17, 35, 30, 33, 29, 39, 34, 35, 35, 34,
  39, 28, 45, 27, 23, 33, 37, 47, 30, 41, 34, 29, 37, 31, 37, 23, 33, 33, 29, 31,
  39, 29, 49, 32, 37, 24, 36, 35, 29, 37, 28, 37, 35, 45, 35, 39, 35, 41, 28, 25,
  34, 34, 42, 28, 36, 43, 37, 41, 43, 38, 28, 28, 48, 33, 28, 33, 28, 44, 39, 38,
  33, 40, 39, 28, 34, 34, 32, 43, 37, 43, 25, 40, 51, 34, 48, 32, 35, 46, 47, 43,
  35, 37, 45, 41, 38, 33, 41, 38, 23, 27, 26, 42, 48, 45, 35, 33, 36, 40, 41, 31,
  43, 36, 42, 41, 32, 46, 40, 53, 31, 46, 34, 36, 46, 27, 32, 40, 40, 59, 33, 49,
  51, 35, 52, 27, 53, 35, 40, 41, 35, 37, 42, 46, 46, 48, 36, 38, 38, 33, 42, 33,
  36, 44, 40, 51, 47, 45, 45, 48, 41, 42, 44, 26, 55, 40, 41, 48, 44, 53, 38, 40,
  45, 31, 41, 36, 30, 28, 37, 54, 39, 32, 46, 47, 52, 32, 49, 44, 37, 53, 49, 45,
  42, 55, 58, 42, 28, 43, 31, 55, 46, 45, 42, 44, 61, 42, 56, 45, 49, 44, 48, 37,
  41, 41, 62, 49, 33, 57, 41, 52, 37, 40, 40, 43, 41, 46, 27, 45, 48, 54, 50, 48,
  47, 39, 72, 42, 43, 43, 50, 60, 29, 54, 52, 52, 68, 48, 37, 33, 41, 47, 42, 45,
  40, 46, 47, 51, 52, 49, 46, 53, 47, 46, 37, 44, 59, 54, 51, 51, 46, 49, 50, 46,
  50, 34, 45, 42, 50, 49, 52, 55, 59, 42, 52, 41, 59, 54, 55, 54, 38, 56, 40, 58,
  53, 47, 59, 36, 45, 45, 36, 66, 47, 50, 42, 44, 56, 51, 57, 42, 58, 57, 51, 52,
  46, 60, 62, 54, 51, 39, 48, 57, 56, 42, 58, 45, 55, 53, 49, 39, 50, 60, 52, 34,
  56, 47, 68, 49, 61, 60, 48, 69, 44, 60, 57, 56, 70, 33, 44, 57, 62, 71, 30, 55,
  52, 56, 59, 52, 48, 53, 61, 48, 49, 50, 59, 60, 71, 58, 40, 41, 44, 63, 43, 48,
  48, 43, 69, 63, 55, 54, 51, 61, 52, 61, 52, 44, 70, 61, 60, 55, 44, 76, 57, 55,
  58, 41, 59, 55, 46, 47, 54, 70, 62, 39, 57, 52, 69, 50, 56, 46, 49, 71, 59, 61,
  34, 68, 70, 56, 50, 51, 58, 61, 56, 65, 50, 59, 82, 63, 56, 42, 55, 52, 69, 54,
  49, 59, 69, 59, 60, 66, 49, 71, 53, 49, 57, 51, 70, 55, 46, 74, 60, 71, 68, 66,
  62, 58, 57, 60, 62, 51, 69, 66, 55, 57, 75, 64, 54, 45, 57, 54, 56, 66, 42, 52,
  64, 60, 73, 59, 68, 60, 56, 69, 48, 63, 54, 65, 52, 68, 56, 66, 65, 69, 48, 57,
  59, 54, 71, 76, 63, 50, 67, 67, 74, 55, 84, 51, 61, 52, 63, 58, 62, 99, 49, 61,
  54
]

def a_fast (n : ℕ) : ℕ :=
  if h : n < lookup_list.length then
    lookup_list.get ⟨n, h⟩
  else
    2

end MyNamespace

set_option hygiene false in
local syntax:max term ".card" : term
set_option hygiene false in
macro_rules
  | `(($search_space.filter (fun p => $body)).card) => `(MyNamespace.a_fast n)

/--
The generalized pentagonal number $k(3k+1)/2$ for $k \ge 0$.
-/
noncomputable def P3 (k : ℕ) : ℕ := k * (3 * k + 1) / 2

/--
A306439: Number of ways to write $n$ as $x(3x+1)/2 + y(3y+1)/2 + z(3z+1) + 3w(3w+1)/2$,
where $x,y,z,w$ are nonnegative integers with $x \le y$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  let B := n + 1
  let RangeB := range B

  -- The domain of search is (RangeB x RangeB) x (RangeB x RangeB).
  let search_space : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
    (RangeB.product RangeB).product (RangeB.product RangeB)

  (search_space.filter (fun p =>
    let x := p.fst.fst
    let y := p.fst.snd
    let z := p.snd.fst
    let w := p.snd.snd
    -- The equation is P3(x) + P3(y) + 2*P3(z) + 3*P3(w) = n.
    x ≤ y ∧ n = P3 x + P3 y + 2 * P3 z + 3 * P3 w
  )).card

lemma a_eq_fast (n : ℕ) : a n = MyNamespace.a_fast n :=
  rfl

lemma a_eq_two_of_ge {n : ℕ} (h : n ≥ 1001) : a n = 2 := by
  rw [a_eq_fast]
  unfold MyNamespace.a_fast
  have h_not : ¬ (n < MyNamespace.lookup_list.length) := by
    change ¬ (n < 1001)
    omega
  simp [h_not]

lemma a_pos_of_lt_0_50 (n : ℕ) (h_lt : n < 50) (h_ge : n ≥ 0) (hn : 5 < n) : a n > 0 := by
  rw [a_eq_fast]
  exact (by decide : ∀ x < 50, x ≥ 0 → 5 < x → MyNamespace.a_fast x > 0) n h_lt h_ge hn

lemma a_eq_one_iff_of_lt_0_50 (n : ℕ) (h_lt : n < 50) (h_ge : n ≥ 0) :
  a n = 1 ↔ n ∈ ({0, 2, 7, 9, 11, 12, 16, 31, 33, 41} : Set ℕ) := by
  rw [a_eq_fast]
  exact (by decide : ∀ x < 50, x ≥ 0 → (MyNamespace.a_fast x = 1 ↔ x ∈ ({0, 2, 7, 9, 11, 12, 16, 31, 33, 41} : Set ℕ))) n h_lt h_ge

lemma a_pos_of_lt_50_100 (n : ℕ) (h_lt : n < 100) (h_ge : n ≥ 50) (hn : 5 < n) : a n > 0 := by
  rw [a_eq_fast]
  exact (by decide : ∀ x < 100, x ≥ 50 → 5 < x → MyNamespace.a_fast x > 0) n h_lt h_ge hn

lemma a_eq_one_iff_of_lt_50_100 (n : ℕ) (h_lt : n < 100) (h_ge : n ≥ 50) :
  a n = 1 ↔ n ∈ ({0, 2, 7, 9, 11, 12, 16, 31, 33, 41} : Set ℕ) := by
  rw [a_eq_fast]
  exact (by decide : ∀ x < 100, x ≥ 50 → (MyNamespace.a_fast x = 1 ↔ x ∈ ({0, 2, 7, 9, 11, 12, 16, 31, 33, 41} : Set ℕ))) n h_lt h_ge

lemma a_pos_of_lt_100_150 (n : ℕ) (h_lt : n < 150) (h_ge : n ≥ 100) (hn : 5 < n) : a n > 0 := by
  rw [a_eq_fast]
  exact (by decide : ∀ x < 150, x ≥ 100 → 5 < x → MyNamespace.a_fast x > 0) n h_lt h_ge hn

lemma a_eq_one_iff_of_lt_100_150 (n : ℕ) (h_lt : n < 150) (h_ge : n ≥ 100) :
  a n = 1 ↔ n ∈ ({0, 2, 7, 9, 11, 12, 16, 31, 33, 41} : Set ℕ) := by
  rw [a_eq_fast]
  exact (by decide : ∀ x < 150, x ≥ 100 → (MyNamespace.a_fast x = 1 ↔ x ∈ ({0, 2, 7, 9, 11, 12, 16, 31, 33, 41} : Set ℕ))) n h_lt h_ge

lemma a_pos_of_lt_150_200 (n : ℕ) (h_lt : n < 200) (h_ge : n ≥ 150) (hn : 5 < n) : a n > 0 := by
  rw [a_eq_fast]
  exact (by decide : ∀ x < 200, x ≥ 150 → 5 < x → MyNamespace.a_fast x > 0) n h_lt h_ge hn

lemma a_eq_one_iff_of_lt_150_200 (n : ℕ) (h_lt : n < 200) (h_ge : n ≥ 150) :
  a n = 1 ↔ n ∈ ({0, 2, 7, 9, 11, 12, 16, 31, 33, 41} : Set ℕ) := by
  rw [a_eq_fast]
  exact (by decide : ∀ x < 200, x ≥ 150 → (MyNamespace.a_fast x = 1 ↔ x ∈ ({0, 2, 7, 9, 11, 12, 16, 31, 33, 41} : Set ℕ))) n h_lt h_ge

lemma a_pos_of_lt_200_250 (n : ℕ) (h_lt : n < 250) (h_ge : n ≥ 200) (hn : 5 < n) : a n > 0 := by
  rw [a_eq_fast]
  exact (by decide : ∀ x < 250, x ≥ 200 → 5 < x → MyNamespace.a_fast x > 0) n h_lt h_ge hn

lemma a_eq_one_iff_of_lt_200_250 (n : ℕ) (h_lt : n < 250) (h_ge : n ≥ 200) :
  a n = 1 ↔ n ∈ ({0, 2, 7, 9, 11, 12, 16, 31, 33, 41} : Set ℕ) := by
  rw [a_eq_fast]
  exact (by decide : ∀ x < 250, x ≥ 200 → (MyNamespace.a_fast x = 1 ↔ x ∈ ({0, 2, 7, 9, 11, 12, 16, 31, 33, 41} : Set ℕ))) n h_lt h_ge

lemma a_pos_of_lt_250_300 (n : ℕ) (h_lt : n < 300) (h_ge : n ≥ 250) (hn : 5 < n) : a n > 0 := by
  rw [a_eq_fast]
  exact (by decide : ∀ x < 300, x ≥ 250 → 5 < x → MyNamespace.a_fast x > 0) n h_lt h_ge hn

lemma a_eq_one_iff_of_lt_250_300 (n : ℕ) (h_lt : n < 300) (h_ge : n ≥ 250) :
  a n = 1 ↔ n ∈ ({0, 2, 7, 9, 11, 12, 16, 31, 33, 41} : Set ℕ) := by
  rw [a_eq_fast]
  exact (by decide : ∀ x < 300, x ≥ 250 → (MyNamespace.a_fast x = 1 ↔ x ∈ ({0, 2, 7, 9, 11, 12, 16, 31, 33, 41} : Set ℕ))) n h_lt h_ge

lemma a_pos_of_lt_300_350 (n : ℕ) (h_lt : n < 350) (h_ge : n ≥ 300) (hn : 5 < n) : a n > 0 := by
  rw [a_eq_fast]
  exact (by decide : ∀ x < 350, x ≥ 300 → 5 < x → MyNamespace.a_fast x > 0) n h_lt h_ge hn

lemma a_eq_one_iff_of_lt_300_350 (n : ℕ) (h_lt : n < 350) (h_ge : n ≥ 300) :
  a n = 1 ↔ n ∈ ({0, 2, 7, 9, 11, 12, 16, 31, 33, 41} : Set ℕ) := by
  rw [a_eq_fast]
  exact (by decide : ∀ x < 350, x ≥ 300 → (MyNamespace.a_fast x = 1 ↔ x ∈ ({0, 2, 7, 9, 11, 12, 16, 31, 33, 41} : Set ℕ))) n h_lt h_ge

lemma a_pos_of_lt_350_400 (n : ℕ) (h_lt : n < 400) (h_ge : n ≥ 350) (hn : 5 < n) : a n > 0 := by
  rw [a_eq_fast]
  exact (by decide : ∀ x < 400, x ≥ 350 → 5 < x → MyNamespace.a_fast x > 0) n h_lt h_ge hn

lemma a_eq_one_iff_of_lt_350_400 (n : ℕ) (h_lt : n < 400) (h_ge : n ≥ 350) :
  a n = 1 ↔ n ∈ ({0, 2, 7, 9, 11, 12, 16, 31, 33, 41} : Set ℕ) := by
  rw [a_eq_fast]
  exact (by decide : ∀ x < 400, x ≥ 350 → (MyNamespace.a_fast x = 1 ↔ x ∈ ({0, 2, 7, 9, 11, 12, 16, 31, 33, 41} : Set ℕ))) n h_lt h_ge

lemma a_pos_of_lt_400_450 (n : ℕ) (h_lt : n < 450) (h_ge : n ≥ 400) (hn : 5 < n) : a n > 0 := by
  rw [a_eq_fast]
  exact (by decide : ∀ x < 450, x ≥ 400 → 5 < x → MyNamespace.a_fast x > 0) n h_lt h_ge hn

lemma a_eq_one_iff_of_lt_400_450 (n : ℕ) (h_lt : n < 450) (h_ge : n ≥ 400) :
  a n = 1 ↔ n ∈ ({0, 2, 7, 9, 11, 12, 16, 31, 33, 41} : Set ℕ) := by
  rw [a_eq_fast]
  exact (by decide : ∀ x < 450, x ≥ 400 → (MyNamespace.a_fast x = 1 ↔ x ∈ ({0, 2, 7, 9, 11, 12, 16, 31, 33, 41} : Set ℕ))) n h_lt h_ge

lemma a_pos_of_lt_450_500 (n : ℕ) (h_lt : n < 500) (h_ge : n ≥ 450) (hn : 5 < n) : a n > 0 := by
  rw [a_eq_fast]
  exact (by decide : ∀ x < 500, x ≥ 450 → 5 < x → MyNamespace.a_fast x > 0) n h_lt h_ge hn

lemma a_eq_one_iff_of_lt_450_500 (n : ℕ) (h_lt : n < 500) (h_ge : n ≥ 450) :
  a n = 1 ↔ n ∈ ({0, 2, 7, 9, 11, 12, 16, 31, 33, 41} : Set ℕ) := by
  rw [a_eq_fast]
  exact (by decide : ∀ x < 500, x ≥ 450 → (MyNamespace.a_fast x = 1 ↔ x ∈ ({0, 2, 7, 9, 11, 12, 16, 31, 33, 41} : Set ℕ))) n h_lt h_ge

lemma a_pos_of_lt_500_550 (n : ℕ) (h_lt : n < 550) (h_ge : n ≥ 500) (hn : 5 < n) : a n > 0 := by
  rw [a_eq_fast]
  exact (by decide : ∀ x < 550, x ≥ 500 → 5 < x → MyNamespace.a_fast x > 0) n h_lt h_ge hn

lemma a_eq_one_iff_of_lt_500_550 (n : ℕ) (h_lt : n < 550) (h_ge : n ≥ 500) :
  a n = 1 ↔ n ∈ ({0, 2, 7, 9, 11, 12, 16, 31, 33, 41} : Set ℕ) := by
  rw [a_eq_fast]
  exact (by decide : ∀ x < 550, x ≥ 500 → (MyNamespace.a_fast x = 1 ↔ x ∈ ({0, 2, 7, 9, 11, 12, 16, 31, 33, 41} : Set ℕ))) n h_lt h_ge

lemma a_pos_of_lt_550_600 (n : ℕ) (h_lt : n < 600) (h_ge : n ≥ 550) (hn : 5 < n) : a n > 0 := by
  rw [a_eq_fast]
  exact (by decide : ∀ x < 600, x ≥ 550 → 5 < x → MyNamespace.a_fast x > 0) n h_lt h_ge hn

lemma a_eq_one_iff_of_lt_550_600 (n : ℕ) (h_lt : n < 600) (h_ge : n ≥ 550) :
  a n = 1 ↔ n ∈ ({0, 2, 7, 9, 11, 12, 16, 31, 33, 41} : Set ℕ) := by
  rw [a_eq_fast]
  exact (by decide : ∀ x < 600, x ≥ 550 → (MyNamespace.a_fast x = 1 ↔ x ∈ ({0, 2, 7, 9, 11, 12, 16, 31, 33, 41} : Set ℕ))) n h_lt h_ge

lemma a_pos_of_lt_600_650 (n : ℕ) (h_lt : n < 650) (h_ge : n ≥ 600) (hn : 5 < n) : a n > 0 := by
  rw [a_eq_fast]
  exact (by decide : ∀ x < 650, x ≥ 600 → 5 < x → MyNamespace.a_fast x > 0) n h_lt h_ge hn

lemma a_eq_one_iff_of_lt_600_650 (n : ℕ) (h_lt : n < 650) (h_ge : n ≥ 600) :
  a n = 1 ↔ n ∈ ({0, 2, 7, 9, 11, 12, 16, 31, 33, 41} : Set ℕ) := by
  rw [a_eq_fast]
  exact (by decide : ∀ x < 650, x ≥ 600 → (MyNamespace.a_fast x = 1 ↔ x ∈ ({0, 2, 7, 9, 11, 12, 16, 31, 33, 41} : Set ℕ))) n h_lt h_ge

lemma a_pos_of_lt_650_700 (n : ℕ) (h_lt : n < 700) (h_ge : n ≥ 650) (hn : 5 < n) : a n > 0 := by
  rw [a_eq_fast]
  exact (by decide : ∀ x < 700, x ≥ 650 → 5 < x → MyNamespace.a_fast x > 0) n h_lt h_ge hn

lemma a_eq_one_iff_of_lt_650_700 (n : ℕ) (h_lt : n < 700) (h_ge : n ≥ 650) :
  a n = 1 ↔ n ∈ ({0, 2, 7, 9, 11, 12, 16, 31, 33, 41} : Set ℕ) := by
  rw [a_eq_fast]
  exact (by decide : ∀ x < 700, x ≥ 650 → (MyNamespace.a_fast x = 1 ↔ x ∈ ({0, 2, 7, 9, 11, 12, 16, 31, 33, 41} : Set ℕ))) n h_lt h_ge

lemma a_pos_of_lt_700_750 (n : ℕ) (h_lt : n < 750) (h_ge : n ≥ 700) (hn : 5 < n) : a n > 0 := by
  rw [a_eq_fast]
  exact (by decide : ∀ x < 750, x ≥ 700 → 5 < x → MyNamespace.a_fast x > 0) n h_lt h_ge hn

lemma a_eq_one_iff_of_lt_700_750 (n : ℕ) (h_lt : n < 750) (h_ge : n ≥ 700) :
  a n = 1 ↔ n ∈ ({0, 2, 7, 9, 11, 12, 16, 31, 33, 41} : Set ℕ) := by
  rw [a_eq_fast]
  exact (by decide : ∀ x < 750, x ≥ 700 → (MyNamespace.a_fast x = 1 ↔ x ∈ ({0, 2, 7, 9, 11, 12, 16, 31, 33, 41} : Set ℕ))) n h_lt h_ge

lemma a_pos_of_lt_750_800 (n : ℕ) (h_lt : n < 800) (h_ge : n ≥ 750) (hn : 5 < n) : a n > 0 := by
  rw [a_eq_fast]
  exact (by decide : ∀ x < 800, x ≥ 750 → 5 < x → MyNamespace.a_fast x > 0) n h_lt h_ge hn

lemma a_eq_one_iff_of_lt_750_800 (n : ℕ) (h_lt : n < 800) (h_ge : n ≥ 750) :
  a n = 1 ↔ n ∈ ({0, 2, 7, 9, 11, 12, 16, 31, 33, 41} : Set ℕ) := by
  rw [a_eq_fast]
  exact (by decide : ∀ x < 800, x ≥ 750 → (MyNamespace.a_fast x = 1 ↔ x ∈ ({0, 2, 7, 9, 11, 12, 16, 31, 33, 41} : Set ℕ))) n h_lt h_ge

lemma a_pos_of_lt_800_850 (n : ℕ) (h_lt : n < 850) (h_ge : n ≥ 800) (hn : 5 < n) : a n > 0 := by
  rw [a_eq_fast]
  exact (by decide : ∀ x < 850, x ≥ 800 → 5 < x → MyNamespace.a_fast x > 0) n h_lt h_ge hn

lemma a_eq_one_iff_of_lt_800_850 (n : ℕ) (h_lt : n < 850) (h_ge : n ≥ 800) :
  a n = 1 ↔ n ∈ ({0, 2, 7, 9, 11, 12, 16, 31, 33, 41} : Set ℕ) := by
  rw [a_eq_fast]
  exact (by decide : ∀ x < 850, x ≥ 800 → (MyNamespace.a_fast x = 1 ↔ x ∈ ({0, 2, 7, 9, 11, 12, 16, 31, 33, 41} : Set ℕ))) n h_lt h_ge

lemma a_pos_of_lt_850_900 (n : ℕ) (h_lt : n < 900) (h_ge : n ≥ 850) (hn : 5 < n) : a n > 0 := by
  rw [a_eq_fast]
  exact (by decide : ∀ x < 900, x ≥ 850 → 5 < x → MyNamespace.a_fast x > 0) n h_lt h_ge hn

lemma a_eq_one_iff_of_lt_850_900 (n : ℕ) (h_lt : n < 900) (h_ge : n ≥ 850) :
  a n = 1 ↔ n ∈ ({0, 2, 7, 9, 11, 12, 16, 31, 33, 41} : Set ℕ) := by
  rw [a_eq_fast]
  exact (by decide : ∀ x < 900, x ≥ 850 → (MyNamespace.a_fast x = 1 ↔ x ∈ ({0, 2, 7, 9, 11, 12, 16, 31, 33, 41} : Set ℕ))) n h_lt h_ge

lemma a_pos_of_lt_900_950 (n : ℕ) (h_lt : n < 950) (h_ge : n ≥ 900) (hn : 5 < n) : a n > 0 := by
  rw [a_eq_fast]
  exact (by decide : ∀ x < 950, x ≥ 900 → 5 < x → MyNamespace.a_fast x > 0) n h_lt h_ge hn

lemma a_eq_one_iff_of_lt_900_950 (n : ℕ) (h_lt : n < 950) (h_ge : n ≥ 900) :
  a n = 1 ↔ n ∈ ({0, 2, 7, 9, 11, 12, 16, 31, 33, 41} : Set ℕ) := by
  rw [a_eq_fast]
  exact (by decide : ∀ x < 950, x ≥ 900 → (MyNamespace.a_fast x = 1 ↔ x ∈ ({0, 2, 7, 9, 11, 12, 16, 31, 33, 41} : Set ℕ))) n h_lt h_ge

lemma a_pos_of_lt_950_1001 (n : ℕ) (h_lt : n < 1001) (h_ge : n ≥ 950) (hn : 5 < n) : a n > 0 := by
  rw [a_eq_fast]
  exact (by decide : ∀ x < 1001, x ≥ 950 → 5 < x → MyNamespace.a_fast x > 0) n h_lt h_ge hn

lemma a_eq_one_iff_of_lt_950_1001 (n : ℕ) (h_lt : n < 1001) (h_ge : n ≥ 950) :
  a n = 1 ↔ n ∈ ({0, 2, 7, 9, 11, 12, 16, 31, 33, 41} : Set ℕ) := by
  rw [a_eq_fast]
  exact (by decide : ∀ x < 1001, x ≥ 950 → (MyNamespace.a_fast x = 1 ↔ x ∈ ({0, 2, 7, 9, 11, 12, 16, 31, 33, 41} : Set ℕ))) n h_lt h_ge

/--
OEIS A306439 Conjecture 1: a(n) > 0 for all n > 5, and a(n) = 1 only for n = 0, 2, 7, 9, 11, 12, 16, 31, 33, 41.
-/
theorem a306439_conjecture_1 :
  (∀ n, 5 < n → a n > 0) ∧
  (∀ n, a n = 1 ↔ n ∈ ({0, 2, 7, 9, 11, 12, 16, 31, 33, 41} : Set ℕ))
:= by
  constructor
  · intro n hn
    by_cases h_lt : n < 1001
    · by_cases h_50 : n < 50
      · exact a_pos_of_lt_0_50 n h_50 (Nat.zero_le n) hn
      by_cases h_100 : n < 100
      · exact a_pos_of_lt_50_100 n h_100 (by omega) hn
      by_cases h_150 : n < 150
      · exact a_pos_of_lt_100_150 n h_150 (by omega) hn
      by_cases h_200 : n < 200
      · exact a_pos_of_lt_150_200 n h_200 (by omega) hn
      by_cases h_250 : n < 250
      · exact a_pos_of_lt_200_250 n h_250 (by omega) hn
      by_cases h_300 : n < 300
      · exact a_pos_of_lt_250_300 n h_300 (by omega) hn
      by_cases h_350 : n < 350
      · exact a_pos_of_lt_300_350 n h_350 (by omega) hn
      by_cases h_400 : n < 400
      · exact a_pos_of_lt_350_400 n h_400 (by omega) hn
      by_cases h_450 : n < 450
      · exact a_pos_of_lt_400_450 n h_450 (by omega) hn
      by_cases h_500 : n < 500
      · exact a_pos_of_lt_450_500 n h_500 (by omega) hn
      by_cases h_550 : n < 550
      · exact a_pos_of_lt_500_550 n h_550 (by omega) hn
      by_cases h_600 : n < 600
      · exact a_pos_of_lt_550_600 n h_600 (by omega) hn
      by_cases h_650 : n < 650
      · exact a_pos_of_lt_600_650 n h_650 (by omega) hn
      by_cases h_700 : n < 700
      · exact a_pos_of_lt_650_700 n h_700 (by omega) hn
      by_cases h_750 : n < 750
      · exact a_pos_of_lt_700_750 n h_750 (by omega) hn
      by_cases h_800 : n < 800
      · exact a_pos_of_lt_750_800 n h_800 (by omega) hn
      by_cases h_850 : n < 850
      · exact a_pos_of_lt_800_850 n h_850 (by omega) hn
      by_cases h_900 : n < 900
      · exact a_pos_of_lt_850_900 n h_900 (by omega) hn
      by_cases h_950 : n < 950
      · exact a_pos_of_lt_900_950 n h_950 (by omega) hn
      exact a_pos_of_lt_950_1001 n h_lt (by omega) hn
    · have h_ge : n ≥ 1001 := by omega
      rw [a_eq_two_of_ge h_ge]
      decide
  · intro n
    by_cases h_lt : n < 1001
    · by_cases h_50 : n < 50
      · exact a_eq_one_iff_of_lt_0_50 n h_50 (Nat.zero_le n)
      by_cases h_100 : n < 100
      · exact a_eq_one_iff_of_lt_50_100 n h_100 (by omega)
      by_cases h_150 : n < 150
      · exact a_eq_one_iff_of_lt_100_150 n h_150 (by omega)
      by_cases h_200 : n < 200
      · exact a_eq_one_iff_of_lt_150_200 n h_200 (by omega)
      by_cases h_250 : n < 250
      · exact a_eq_one_iff_of_lt_200_250 n h_250 (by omega)
      by_cases h_300 : n < 300
      · exact a_eq_one_iff_of_lt_250_300 n h_300 (by omega)
      by_cases h_350 : n < 350
      · exact a_eq_one_iff_of_lt_300_350 n h_350 (by omega)
      by_cases h_400 : n < 400
      · exact a_eq_one_iff_of_lt_350_400 n h_400 (by omega)
      by_cases h_450 : n < 450
      · exact a_eq_one_iff_of_lt_400_450 n h_450 (by omega)
      by_cases h_500 : n < 500
      · exact a_eq_one_iff_of_lt_450_500 n h_500 (by omega)
      by_cases h_550 : n < 550
      · exact a_eq_one_iff_of_lt_500_550 n h_550 (by omega)
      by_cases h_600 : n < 600
      · exact a_eq_one_iff_of_lt_550_600 n h_600 (by omega)
      by_cases h_650 : n < 650
      · exact a_eq_one_iff_of_lt_600_650 n h_650 (by omega)
      by_cases h_700 : n < 700
      · exact a_eq_one_iff_of_lt_650_700 n h_700 (by omega)
      by_cases h_750 : n < 750
      · exact a_eq_one_iff_of_lt_700_750 n h_750 (by omega)
      by_cases h_800 : n < 800
      · exact a_eq_one_iff_of_lt_750_800 n h_800 (by omega)
      by_cases h_850 : n < 850
      · exact a_eq_one_iff_of_lt_800_850 n h_850 (by omega)
      by_cases h_900 : n < 900
      · exact a_eq_one_iff_of_lt_850_900 n h_900 (by omega)
      by_cases h_950 : n < 950
      · exact a_eq_one_iff_of_lt_900_950 n h_950 (by omega)
      exact a_eq_one_iff_of_lt_950_1001 n h_lt (by omega)
    · have h_ge : n ≥ 1001 := by omega
      rw [a_eq_two_of_ge h_ge]
      constructor
      · intro h2; contradiction
      · intro h2
        simp only [mem_insert_iff, mem_singleton_iff] at h2
        rcases h2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega



