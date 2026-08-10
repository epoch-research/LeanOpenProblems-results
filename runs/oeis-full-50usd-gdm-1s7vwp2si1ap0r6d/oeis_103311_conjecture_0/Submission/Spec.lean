import FormalConjectures.Util.ProblemImports

/--
A103311: A transform of the Fibonacci numbers.
The sequence $a(n)$ satisfies the linear recurrence relation:
$$a(n) = 3a(n-1) - 4a(n-2) + 2a(n-3) - a(n-4)$$
with initial terms $a(0)=0, a(1)=1, a(2)=1, a(3)=0$.
The sequence takes values in $\mathbb{Z}$.
-/
def a : ℕ → ℤ
| 0 => 0
| 1 => 1
| 2 => 1
| 3 => 0
| n + 4 => 3 * a (n + 3) - 4 * a (n + 2) + 2 * a (n + 1) - a n

def sign (q : ℕ) : ℤ := if q % 2 = 0 then 1 else -1

lemma fib_add_two_eq (j : ℕ) : Nat.fib (j + 2) = Nat.fib (j + 1) + Nat.fib j := by
  have := @Nat.fib_add_two j
  omega

lemma fib_add_three (j : ℕ) : Nat.fib (j + 3) = 2 * Nat.fib (j + 1) + Nat.fib j := by
  have h1 : j + 3 = (j + 1) + 2 := by omega
  rw [h1, fib_add_two_eq, fib_add_two_eq]
  omega

lemma fib_add_four (j : ℕ) : Nat.fib (j + 4) = 3 * Nat.fib (j + 1) + 2 * Nat.fib j := by
  have h1 : j + 4 = (j + 2) + 2 := by omega
  rw [h1, fib_add_two_eq, fib_add_three, fib_add_two_eq]
  omega

lemma fib_add_five (j : ℕ) : Nat.fib (j + 5) = 5 * Nat.fib (j + 1) + 3 * Nat.fib j := by
  have h1 : j + 5 = (j + 3) + 2 := by omega
  rw [h1, fib_add_two_eq, fib_add_four, fib_add_three]
  omega

lemma fib_add_six (j : ℕ) : Nat.fib (j + 6) = 8 * Nat.fib (j + 1) + 5 * Nat.fib j := by
  have h1 : j + 6 = (j + 4) + 2 := by omega
  rw [h1, fib_add_two_eq, fib_add_five, fib_add_four]
  omega

lemma sign_succ (q : ℕ) : sign (q + 1) = - sign q := by
  simp [sign]
  split_ifs <;> omega

lemma ident1 (j : ℕ) : (Nat.fib (j + 3) : ℤ) - 2 * Nat.fib (j + 1) - Nat.fib j = 0 := by
  rw [fib_add_three]
  push_cast
  ring

lemma ident2 (j : ℕ) : (Nat.fib (j + 5) : ℤ) - 3 * Nat.fib (j + 3) + Nat.fib (j + 1) = 0 := by
  rw [fib_add_five, fib_add_three]
  push_cast
  ring

lemma ident3 (j : ℕ) : (Nat.fib (j + 6) : ℤ) - 3 * Nat.fib (j + 5) + 4 * Nat.fib (j + 3) - Nat.fib (j + 1) = 0 := by
  rw [fib_add_six, fib_add_five, fib_add_three]
  push_cast
  ring

lemma ident4 (j : ℕ) : 2 * (Nat.fib (j + 6) : ℤ) - 4 * Nat.fib (j + 5) + 2 * Nat.fib (j + 3) = 0 := by
  rw [fib_add_six, fib_add_five, fib_add_three]
  push_cast
  ring

lemma ident5 (j : ℕ) : (Nat.fib (j + 6) : ℤ) - 2 * Nat.fib (j + 5) + Nat.fib (j + 3) = 0 := by
  rw [fib_add_six, fib_add_five, fib_add_three]
  push_cast
  ring

def a_formula (n : ℕ) : ℤ :=
  let q := n / 5
  let r := n % 5
  match r with
  | 0 => sign q * (Nat.fib (5 * q) : ℤ)
  | 1 => sign q * (Nat.fib (5 * q + 1) : ℤ)
  | 2 => sign q * (Nat.fib (5 * q + 1) : ℤ)
  | 3 => 0
  | _ => - sign q * (Nat.fib (5 * q + 3) : ℤ)

lemma a_formula_5k_0 (k : ℕ) : a_formula (5 * k) = sign k * Nat.fib (5 * k) := by
  change (match (5 * k) % 5 with
    | 0 => sign ((5 * k) / 5) * (Nat.fib (5 * ((5 * k) / 5)) : ℤ)
    | 1 => sign ((5 * k) / 5) * (Nat.fib (5 * ((5 * k) / 5) + 1) : ℤ)
    | 2 => sign ((5 * k) / 5) * (Nat.fib (5 * ((5 * k) / 5) + 1) : ℤ)
    | 3 => 0
    | _ => - sign ((5 * k) / 5) * (Nat.fib (5 * ((5 * k) / 5) + 3) : ℤ)) = _
  have hq : (5 * k) / 5 = k := by omega
  have hr : (5 * k) % 5 = 0 := by omega
  rw [hq, hr]

lemma a_formula_5k_1 (k : ℕ) : a_formula (5 * k + 1) = sign k * Nat.fib (5 * k + 1) := by
  change (match (5 * k + 1) % 5 with
    | 0 => sign ((5 * k + 1) / 5) * (Nat.fib (5 * ((5 * k + 1) / 5)) : ℤ)
    | 1 => sign ((5 * k + 1) / 5) * (Nat.fib (5 * ((5 * k + 1) / 5) + 1) : ℤ)
    | 2 => sign ((5 * k + 1) / 5) * (Nat.fib (5 * ((5 * k + 1) / 5) + 1) : ℤ)
    | 3 => 0
    | _ => - sign ((5 * k + 1) / 5) * (Nat.fib (5 * ((5 * k + 1) / 5) + 3) : ℤ)) = _
  have hq : (5 * k + 1) / 5 = k := by omega
  have hr : (5 * k + 1) % 5 = 1 := by omega
  rw [hq, hr]

lemma a_formula_5k_2 (k : ℕ) : a_formula (5 * k + 2) = sign k * Nat.fib (5 * k + 1) := by
  change (match (5 * k + 2) % 5 with
    | 0 => sign ((5 * k + 2) / 5) * (Nat.fib (5 * ((5 * k + 2) / 5)) : ℤ)
    | 1 => sign ((5 * k + 2) / 5) * (Nat.fib (5 * ((5 * k + 2) / 5) + 1) : ℤ)
    | 2 => sign ((5 * k + 2) / 5) * (Nat.fib (5 * ((5 * k + 2) / 5) + 1) : ℤ)
    | 3 => 0
    | _ => - sign ((5 * k + 2) / 5) * (Nat.fib (5 * ((5 * k + 2) / 5) + 3) : ℤ)) = _
  have hq : (5 * k + 2) / 5 = k := by omega
  have hr : (5 * k + 2) % 5 = 2 := by omega
  rw [hq, hr]

lemma a_formula_5k_3 (k : ℕ) : a_formula (5 * k + 3) = 0 := by
  change (match (5 * k + 3) % 5 with
    | 0 => sign ((5 * k + 3) / 5) * (Nat.fib (5 * ((5 * k + 3) / 5)) : ℤ)
    | 1 => sign ((5 * k + 3) / 5) * (Nat.fib (5 * ((5 * k + 3) / 5) + 1) : ℤ)
    | 2 => sign ((5 * k + 3) / 5) * (Nat.fib (5 * ((5 * k + 3) / 5) + 1) : ℤ)
    | 3 => 0
    | _ => - sign ((5 * k + 3) / 5) * (Nat.fib (5 * ((5 * k + 3) / 5) + 3) : ℤ)) = _
  have hq : (5 * k + 3) / 5 = k := by omega
  have hr : (5 * k + 3) % 5 = 3 := by omega
  rw [hq, hr]

lemma a_formula_5k_4 (k : ℕ) : a_formula (5 * k + 4) = - sign k * Nat.fib (5 * k + 3) := by
  change (match (5 * k + 4) % 5 with
    | 0 => sign ((5 * k + 4) / 5) * (Nat.fib (5 * ((5 * k + 4) / 5)) : ℤ)
    | 1 => sign ((5 * k + 4) / 5) * (Nat.fib (5 * ((5 * k + 4) / 5) + 1) : ℤ)
    | 2 => sign ((5 * k + 4) / 5) * (Nat.fib (5 * ((5 * k + 4) / 5) + 1) : ℤ)
    | 3 => 0
    | _ => - sign ((5 * k + 4) / 5) * (Nat.fib (5 * ((5 * k + 4) / 5) + 3) : ℤ)) = _
  have hq : (5 * k + 4) / 5 = k := by omega
  have hr : (5 * k + 4) % 5 = 4 := by omega
  rw [hq, hr]

lemma a_formula_recurrence (m : ℕ) : a_formula (m + 4) = 3 * a_formula (m + 3) - 4 * a_formula (m + 2) + 2 * a_formula (m + 1) - a_formula m := by
  have h_m : m = 5 * (m / 5) + (m % 5) := by omega
  generalize hd : m / 5 = k
  generalize hm : m % 5 = r
  rw [hd, hm] at h_m
  rw [h_m]
  have h_r : r < 5 := by omega
  have h_idx5 : 5 * (k + 1) = 5 * k + 5 := by omega
  have h_idx6 : 5 * (k + 1) + 1 = 5 * k + 6 := by omega
  interval_cases r
  · -- r = 0
    have h0 : 5 * k + 0 = 5 * k := by omega
    have h1 : 5 * k + 1 = 5 * k + 1 := by omega
    have h2 : 5 * k + 2 = 5 * k + 2 := by omega
    have h3 : 5 * k + 3 = 5 * k + 3 := by omega
    have h4 : 5 * k + 4 = 5 * k + 4 := by omega
    rw [h0, h1, h2, h3, h4]
    rw [a_formula_5k_0, a_formula_5k_1, a_formula_5k_2, a_formula_5k_3, a_formula_5k_4]
    have h_id1 := ident1 (5 * k)
    linear_combination -sign k * h_id1
  · -- r = 1
    have h0 : 5 * k + 1 = 5 * k + 1 := by omega
    have h1 : 5 * k + 1 + 1 = 5 * k + 2 := by omega
    have h2 : 5 * k + 1 + 2 = 5 * k + 3 := by omega
    have h3 : 5 * k + 1 + 3 = 5 * k + 4 := by omega
    have h4 : 5 * k + 1 + 4 = 5 * (k + 1) := by omega
    rw [h0, h1, h2, h3, h4]
    rw [a_formula_5k_1, a_formula_5k_2, a_formula_5k_3, a_formula_5k_4, a_formula_5k_0]
    rw [sign_succ]
    rw [h_idx5]
    have h_id2 := ident2 (5 * k)
    linear_combination -sign k * h_id2
  · -- r = 2
    have h0 : 5 * k + 2 = 5 * k + 2 := by omega
    have h1 : 5 * k + 2 + 1 = 5 * k + 3 := by omega
    have h2 : 5 * k + 2 + 2 = 5 * k + 4 := by omega
    have h3 : 5 * k + 2 + 3 = 5 * (k + 1) := by omega
    have h4 : 5 * k + 2 + 4 = 5 * (k + 1) + 1 := by omega
    rw [h0, h1, h2, h3, h4]
    rw [a_formula_5k_2, a_formula_5k_3, a_formula_5k_4, a_formula_5k_0, a_formula_5k_1]
    rw [sign_succ]
    rw [h_idx6, h_idx5]
    have h_id3 := ident3 (5 * k)
    linear_combination -sign k * h_id3
  · -- r = 3
    have h0 : 5 * k + 3 = 5 * k + 3 := by omega
    have h1 : 5 * k + 3 + 1 = 5 * k + 4 := by omega
    have h2 : 5 * k + 3 + 2 = 5 * (k + 1) := by omega
    have h3 : 5 * k + 3 + 3 = 5 * (k + 1) + 1 := by omega
    have h4 : 5 * k + 3 + 4 = 5 * (k + 1) + 2 := by omega
    rw [h0, h1, h2, h3, h4]
    rw [a_formula_5k_3, a_formula_5k_4, a_formula_5k_0, a_formula_5k_1, a_formula_5k_2]
    rw [sign_succ]
    rw [h_idx6, h_idx5]
    have h_id4 := ident4 (5 * k)
    linear_combination sign k * h_id4
  · -- r = 4
    have h0 : 5 * k + 4 = 5 * k + 4 := by omega
    have h1 : 5 * k + 4 + 1 = 5 * (k + 1) := by omega
    have h2 : 5 * k + 4 + 2 = 5 * (k + 1) + 1 := by omega
    have h3 : 5 * k + 4 + 3 = 5 * (k + 1) + 2 := by omega
    have h4 : 5 * k + 4 + 4 = 5 * (k + 1) + 3 := by omega
    rw [h0, h1, h2, h3, h4]
    rw [a_formula_5k_4, a_formula_5k_0, a_formula_5k_1, a_formula_5k_2, a_formula_5k_3]
    rw [sign_succ]
    rw [h_idx6, h_idx5]
    have h_id5 := ident5 (5 * k)
    linear_combination -sign k * h_id5

theorem a_eq_a_formula (n : ℕ) : a n = a_formula n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | _ | _ | n
    · rfl
    · rfl
    · rfl
    · rfl
    · rw [a]
      have ih3 := ih (n + 3) (by omega)
      have ih2 := ih (n + 2) (by omega)
      have ih1 := ih (n + 1) (by omega)
      have ih0 := ih n (by omega)
      rw [ih3, ih2, ih1, ih0]
      exact (a_formula_recurrence n).symm

lemma natAbs_sign_mul (q : ℕ) (X : ℕ) : Int.natAbs (sign q * (X : ℤ)) = X := by
  simp [sign]
  split_ifs <;> simp

lemma natAbs_neg_sign_mul (q : ℕ) (X : ℕ) : Int.natAbs (- sign q * (X : ℤ)) = X := by
  simp [sign]
  split_ifs <;> simp

/--
Conjecture: all elements in absolute value are Fibonacci numbers. That is, for every $n$, $|a(n)| = \operatorname{fib}(m)$ for some $m \in \mathbb{N}$.
-/
theorem oeis_103311_conjecture_0 (n : ℕ) : ∃ m : ℕ, Int.natAbs (a n) = Nat.fib m := by
  rw [a_eq_a_formula n]
  let q := n / 5
  let r := n % 5
  have h_n : n = 5 * q + r := by omega
  have h_r : r < 5 := by omega
  rw [h_n]
  interval_cases r
  · -- r = 0
    have h0 : 5 * q + 0 = 5 * q := by omega
    rw [h0]
    rw [a_formula_5k_0]
    rw [natAbs_sign_mul]
    use 5 * q
  · -- r = 1
    rw [a_formula_5k_1]
    rw [natAbs_sign_mul]
    use 5 * q + 1
  · -- r = 2
    rw [a_formula_5k_2]
    rw [natAbs_sign_mul]
    use 5 * q + 1
  · -- r = 3
    rw [a_formula_5k_3]
    use 0
    rfl
  · -- r = 4
    rw [a_formula_5k_4]
    rw [natAbs_neg_sign_mul]
    use 5 * q + 3
