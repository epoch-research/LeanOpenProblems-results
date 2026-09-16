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

@[simp] lemma a_0 : a 0 = 0 := rfl
@[simp] lemma a_1 : a 1 = 1 := rfl
@[simp] lemma a_2 : a 2 = 1 := rfl
@[simp] lemma a_3 : a 3 = 0 := rfl
@[simp] lemma a_add_4 (n : ℕ) : a (n + 4) = 3 * a (n + 3) - 4 * a (n + 2) + 2 * a (n + 1) - a n := rfl

def fibZ (n : ℕ) : ℤ := (Nat.fib n : ℤ)

@[simp] lemma fibZ_add_two (n : ℕ) : fibZ (n + 2) = fibZ (n + 1) + fibZ n := by
  dsimp [fibZ]
  rw [Nat.fib_add_two, Nat.add_comm (Nat.fib n)]
  push_cast
  rfl

@[simp] lemma fibZ_0 : fibZ 0 = 0 := rfl
@[simp] lemma fibZ_1 : fibZ 1 = 1 := rfl

@[simp] lemma neg_one_pow_succ (k : ℕ) : (-1 : ℤ) ^ (k + 1) = - (-1 : ℤ) ^ k := by
  rw [pow_add, pow_one]
  ring

@[simp] lemma natAbs_neg_one_pow (k : ℕ) : Int.natAbs ((-1 : ℤ) ^ k) = 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_add, pow_one, Int.natAbs_mul, ih]
    rfl

@[simp] lemma natAbs_fibZ_mul (k m : ℕ) : Int.natAbs ((-1 : ℤ) ^ k * fibZ m) = Nat.fib m := by
  rw [Int.natAbs_mul, natAbs_neg_one_pow, one_mul]
  rfl

@[simp] lemma natAbs_neg_fibZ_mul (k m : ℕ) : Int.natAbs (-(-1 : ℤ) ^ k * fibZ m) = Nat.fib m := by
  have h : -(-1 : ℤ) ^ k * fibZ m = - ((-1 : ℤ) ^ k * fibZ m) := by ring
  rw [h, Int.natAbs_neg, Int.natAbs_mul, natAbs_neg_one_pow, one_mul]
  rfl

lemma a_eq_fib (k : ℕ) :
  a (5 * k) = (-1 : ℤ) ^ k * fibZ (5 * k) ∧
  a (5 * k + 1) = (-1 : ℤ) ^ k * fibZ (5 * k + 1) ∧
  a (5 * k + 2) = (-1 : ℤ) ^ k * fibZ (5 * k + 1) ∧
  a (5 * k + 3) = 0 ∧
  a (5 * k + 4) = - (-1 : ℤ) ^ k * fibZ (5 * k + 3) := by
  induction' k with k ih
  · simp
  · rcases ih with ⟨h0, h1, h2, h3, h4⟩
    have e0 : 5 * (k + 1) = 5 * k + 5 := by ring
    rw [e0]
    
    have p0 : a (5 * k + 5) = (-1 : ℤ) ^ (k + 1) * fibZ (5 * k + 5) := by
      have h : a (5 * k + 5) = a (5 * k + 1 + 4) := rfl
      rw [h, a_add_4, h4, h3, h2, h1]
      simp
      ring

    have p1 : a (5 * k + 5 + 1) = (-1 : ℤ) ^ (k + 1) * fibZ (5 * k + 5 + 1) := by
      have h : a (5 * k + 5 + 1) = a (5 * k + 2 + 4) := rfl
      rw [h, a_add_4, p0, h4, h3, h2]
      simp
      ring

    have p2 : a (5 * k + 5 + 2) = (-1 : ℤ) ^ (k + 1) * fibZ (5 * k + 5 + 1) := by
      have h : a (5 * k + 5 + 2) = a (5 * k + 3 + 4) := rfl
      rw [h, a_add_4, p1, p0, h4, h3]
      simp
      ring

    have p3 : a (5 * k + 5 + 3) = 0 := by
      have h : a (5 * k + 5 + 3) = a (5 * k + 4 + 4) := rfl
      rw [h, a_add_4, p2, p1, p0, h4]
      simp
      ring

    have p4 : a (5 * k + 5 + 4) = - (-1 : ℤ) ^ (k + 1) * fibZ (5 * k + 5 + 3) := by
      have h2 : a (5 * k + 5 + 4) = 3 * a (5 * k + 5 + 3) - 4 * a (5 * k + 5 + 2) + 2 * a (5 * k + 5 + 1) - a (5 * k + 5) := rfl
      rw [h2, p3, p2, p1, p0]
      simp
      ring

    exact ⟨p0, p1, p2, p3, p4⟩

/--
Conjecture: all elements in absolute value are Fibonacci numbers. That is, for every $n$, $|a(n)| = \operatorname{fib}(m)$ for some $m \in \mathbb{N}$.
-/
theorem oeis_103311_conjecture_0 (n : ℕ) : ∃ m : ℕ, Int.natAbs (a n) = Nat.fib m := by
  have H := a_eq_fib (n / 5)
  rcases H with ⟨h0, h1, h2, h3, h4⟩
  have h_mod : n % 5 < 5 := by omega
  interval_cases r : n % 5
  · use 5 * (n / 5)
    have eq : a n = a (5 * (n / 5)) := by congr 1; omega
    rw [eq, h0]
    exact natAbs_fibZ_mul (n / 5) (5 * (n / 5))
  · use 5 * (n / 5) + 1
    have eq : a n = a (5 * (n / 5) + 1) := by congr 1; omega
    rw [eq, h1]
    exact natAbs_fibZ_mul (n / 5) (5 * (n / 5) + 1)
  · use 5 * (n / 5) + 1
    have eq : a n = a (5 * (n / 5) + 2) := by congr 1; omega
    rw [eq, h2]
    exact natAbs_fibZ_mul (n / 5) (5 * (n / 5) + 1)
  · use 0
    have eq : a n = a (5 * (n / 5) + 3) := by congr 1; omega
    rw [eq, h3]
    rfl
  · use 5 * (n / 5) + 3
    have eq : a n = a (5 * (n / 5) + 4) := by congr 1; omega
    rw [eq, h4]
    exact natAbs_neg_fibZ_mul (n / 5) (5 * (n / 5) + 3)

theorem oeis_103311_conjecture_0.disproof : ¬ (type_of% @oeis_103311_conjecture_0) := sorry
