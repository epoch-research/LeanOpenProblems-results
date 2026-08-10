import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 1000000

open Nat List Filter Real

/--
A326746: $a(n) = (\text{sum of digits of } n) \bmod (\text{sum of digits of } n+1)$.
-/
def a (n : ℕ) : ℕ :=
  (Nat.digits 10 n).sum % (Nat.digits 10 (n + 1)).sum

/-- The count of non-negative integers $n < N$ such that $a(n) = m$. -/
def count_a_eq (N m : ℕ) : ℕ :=
  (List.range N).countP fun n => a n = m

def my_sum_digits (fuel : ℕ) (n : ℕ) : ℕ :=
  match fuel with
  | 0 => 0
  | f + 1 => if n = 0 then 0 else n % 10 + my_sum_digits f (n / 10)

def a_fast_200 (n : ℕ) : ℕ :=
  my_sum_digits 200 n % my_sum_digits 200 (n + 1)

def count_a_fast_200 (N m : ℕ) : ℕ :=
  (List.range N).countP fun n => a_fast_200 n = m

theorem digits_sum_eq_my_sum (fuel : ℕ) : ∀ n : ℕ, n < fuel → (Nat.digits 10 n).sum = my_sum_digits fuel n := by
  induction fuel with
  | zero =>
    intro n hn
    omega
  | succ f ih =>
    intro n hn
    by_cases hn0 : n = 0
    · subst hn0
      simp [my_sum_digits, Nat.digits_zero]
    · rw [my_sum_digits]
      simp only [hn0, ↓reduceIte]
      have h10 : 1 < 10 := by decide
      rw [Nat.digits_eq_cons_digits_div h10 hn0]
      simp only [List.sum_cons]
      have h_div_lt : n / 10 < f := by
        have : n / 10 < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn0) (by decide)
        omega
      rw [ih (n / 10) h_div_lt]

lemma a_eq_a_fast_200 (n : ℕ) (hn : n < 199) : a n = a_fast_200 n := by
  unfold a a_fast_200
  have h1 : (Nat.digits 10 n).sum = my_sum_digits 200 n := by
    apply digits_sum_eq_my_sum
    omega
  have h2 : (Nat.digits 10 (n + 1)).sum = my_sum_digits 200 (n + 1) := by
    apply digits_sum_eq_my_sum
    omega
  rw [h1, h2]

lemma count_a_eq_eq_count_a_fast_200 (m : ℕ) (N : ℕ) (hN : N ≤ 190) : count_a_eq N m = count_a_fast_200 N m := by
  unfold count_a_eq count_a_fast_200
  apply List.countP_congr
  intro n hn
  rw [List.mem_range] at hn
  have hn_lt : n < 199 := by omega
  rw [a_eq_a_fast_200 n hn_lt]

lemma base_case_m_lt_18_fast (m : ℕ) (hm : m < 18) (hm8 : m ≠ 8) :
  (count_a_fast_200 120 m ≤ count_a_fast_200 120 8) ∧
  (count_a_fast_200 120 m + (if a_fast_200 120 = m then 2 else 1) + (if a_fast_200 121 = m then 1 else 0) ≤
   count_a_fast_200 120 8 + (if a_fast_200 120 = 8 then 1 else 0) + (if a_fast_200 121 = 8 then 1 else 0)) := by
  revert m hm hm8; decide

lemma a_ne_a_succ (n : ℕ) : a n ≠ a (n + 1) := by
  sorry

lemma a_ne_a_succ_succ (n : ℕ) : a n ≠ a (n + 2) := by
  sorry

lemma count_a_eq_succ (n m : ℕ) : count_a_eq (n + 1) m = count_a_eq n m + (if a n = m then 1 else 0) := by
  unfold count_a_eq
  simp [List.range_succ]

lemma count_a_eq_invariant_step_back_small (m : ℕ) (hm : m ≠ 8) (n : ℕ) (hn : 72 ≤ n) (hn190 : n ≤ 190) (ha : a (n + 1) = m) : count_a_eq n m + 1 ≤ count_a_eq n 8 := by
  have hn_fast : count_a_eq n m = count_a_fast_200 n m := count_a_eq_eq_count_a_fast_200 m n hn190
  have h8_fast : count_a_eq n 8 = count_a_fast_200 n 8 := count_a_eq_eq_count_a_fast_200 8 n hn190
  rw [hn_fast, h8_fast]
  have h_a_fast : a (n + 1) = a_fast_200 (n + 1) := by
    apply a_eq_a_fast_200
    omega
  rw [h_a_fast] at ha
  subst ha
  have hn_cases : n = 72 ∨ n = 73 ∨ n = 74 ∨ n = 75 ∨ n = 76 ∨ n = 77 ∨ n = 78 ∨ n = 79 ∨ n = 80 ∨
            n = 81 ∨ n = 82 ∨ n = 83 ∨ n = 84 ∨ n = 85 ∨ n = 86 ∨ n = 87 ∨ n = 88 ∨ n = 89 ∨ n = 90 ∨
            n = 91 ∨ n = 92 ∨ n = 93 ∨ n = 94 ∨ n = 95 ∨ n = 96 ∨ n = 97 ∨ n = 98 ∨ n = 99 ∨ n = 100 ∨
            n = 101 ∨ n = 102 ∨ n = 103 ∨ n = 104 ∨ n = 105 ∨ n = 106 ∨ n = 107 ∨ n = 108 ∨ n = 109 ∨ n = 110 ∨
            n = 111 ∨ n = 112 ∨ n = 113 ∨ n = 114 ∨ n = 115 ∨ n = 116 ∨ n = 117 ∨ n = 118 ∨ n = 119 ∨ n = 120 ∨
            n = 121 ∨ n = 122 ∨ n = 123 ∨ n = 124 ∨ n = 125 ∨ n = 126 ∨ n = 127 ∨ n = 128 ∨ n = 129 ∨ n = 130 ∨
            n = 131 ∨ n = 132 ∨ n = 133 ∨ n = 134 ∨ n = 135 ∨ n = 136 ∨ n = 137 ∨ n = 138 ∨ n = 139 ∨ n = 140 ∨
            n = 141 ∨ n = 142 ∨ n = 143 ∨ n = 144 ∨ n = 145 ∨ n = 146 ∨ n = 147 ∨ n = 148 ∨ n = 149 ∨ n = 150 ∨
            n = 151 ∨ n = 152 ∨ n = 153 ∨ n = 154 ∨ n = 155 ∨ n = 156 ∨ n = 157 ∨ n = 158 ∨ n = 159 ∨ n = 160 ∨
            n = 161 ∨ n = 162 ∨ n = 163 ∨ n = 164 ∨ n = 165 ∨ n = 166 ∨ n = 167 ∨ n = 168 ∨ n = 169 ∨ n = 170 ∨
            n = 171 ∨ n = 172 ∨ n = 173 ∨ n = 174 ∨ n = 175 ∨ n = 176 ∨ n = 177 ∨ n = 178 ∨ n = 179 ∨ n = 180 ∨
            n = 181 ∨ n = 182 ∨ n = 183 ∨ n = 184 ∨ n = 185 ∨ n = 186 ∨ n = 187 ∨ n = 188 ∨ n = 189 ∨ n = 190 := by omega
  rcases hn_cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals
    revert hm
    decide

lemma count_a_eq_invariant_step_back_large (m : ℕ) (hm : m ≠ 8) (n : ℕ) (hn : 120 ≤ n) (ha : a (n + 1) = m) : count_a_eq n m + 1 ≤ count_a_eq n 8 := by
  sorry
