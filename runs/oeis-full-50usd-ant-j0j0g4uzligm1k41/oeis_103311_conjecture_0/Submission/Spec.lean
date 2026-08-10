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

/-- Closed form of `a`: a period-10 modulation of consecutive Fibonacci numbers. -/
def b (n : ℕ) : ℤ :=
  match n % 10 with
  | 0 => Nat.fib n
  | 1 => Nat.fib n
  | 2 => - Nat.fib n + Nat.fib (n+1)
  | 3 => 0
  | 4 => Nat.fib n - Nat.fib (n+1)
  | 5 => - Nat.fib n
  | 6 => - Nat.fib n
  | 7 => Nat.fib n - Nat.fib (n+1)
  | 8 => 0
  | 9 => - Nat.fib n + Nat.fib (n+1)
  | _ => 0

/-- `b` satisfies the same linear recurrence as `a`. -/
theorem b_rec (n : ℕ) : b (n+4) = 3 * b (n+3) - 4 * b (n+2) + 2 * b (n+1) - b n := by
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 10 ∧ n = 10 * q + r :=
    ⟨n/10, n%10, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod n 10).symm⟩
  have e : ∀ c:ℕ, (10*q + c) % 10 = c % 10 := by intro c; omega
  have R2 : (Nat.fib (10*q+2):ℤ) = Nat.fib (10*q) + Nat.fib (10*q+1) := by exact_mod_cast Nat.fib_add_two
  have R3 : (Nat.fib (10*q+3):ℤ) = Nat.fib (10*q+1) + Nat.fib (10*q+2) := by exact_mod_cast Nat.fib_add_two
  have R4 : (Nat.fib (10*q+4):ℤ) = Nat.fib (10*q+2) + Nat.fib (10*q+3) := by exact_mod_cast Nat.fib_add_two
  have R5 : (Nat.fib (10*q+5):ℤ) = Nat.fib (10*q+3) + Nat.fib (10*q+4) := by exact_mod_cast Nat.fib_add_two
  have R6 : (Nat.fib (10*q+6):ℤ) = Nat.fib (10*q+4) + Nat.fib (10*q+5) := by exact_mod_cast Nat.fib_add_two
  have R7 : (Nat.fib (10*q+7):ℤ) = Nat.fib (10*q+5) + Nat.fib (10*q+6) := by exact_mod_cast Nat.fib_add_two
  have R8 : (Nat.fib (10*q+8):ℤ) = Nat.fib (10*q+6) + Nat.fib (10*q+7) := by exact_mod_cast Nat.fib_add_two
  have R9 : (Nat.fib (10*q+9):ℤ) = Nat.fib (10*q+7) + Nat.fib (10*q+8) := by exact_mod_cast Nat.fib_add_two
  have R10 : (Nat.fib (10*q+10):ℤ) = Nat.fib (10*q+8) + Nat.fib (10*q+9) := by exact_mod_cast Nat.fib_add_two
  have R11 : (Nat.fib (10*q+11):ℤ) = Nat.fib (10*q+9) + Nat.fib (10*q+10) := by exact_mod_cast Nat.fib_add_two
  have R12 : (Nat.fib (10*q+12):ℤ) = Nat.fib (10*q+10) + Nat.fib (10*q+11) := by exact_mod_cast Nat.fib_add_two
  have R13 : (Nat.fib (10*q+13):ℤ) = Nat.fib (10*q+11) + Nat.fib (10*q+12) := by exact_mod_cast Nat.fib_add_two
  have R14 : (Nat.fib (10*q+14):ℤ) = Nat.fib (10*q+12) + Nat.fib (10*q+13) := by exact_mod_cast Nat.fib_add_two
  interval_cases r <;>
  · simp only [b, Nat.add_assoc, Nat.reduceAdd, e, Nat.reduceMod, Nat.add_zero, Nat.mul_mod_right]
    push_cast
    omega

/-- `a` equals its closed form `b`. -/
theorem key (n : ℕ) : a n = b n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => rfl
    | 1, _ => rfl
    | 2, _ => rfl
    | 3, _ => rfl
    | (k+4), ih =>
      have h3 := ih (k+3) (by omega)
      have h2 := ih (k+2) (by omega)
      have h1 := ih (k+1) (by omega)
      have h0 := ih k (by omega)
      have ha : a (k+4) = 3 * a (k+3) - 4 * a (k+2) + 2 * a (k+1) - a k := rfl
      rw [ha, h3, h2, h1, h0]
      exact (b_rec k).symm

/-- Each value of `b` is plus or minus a Fibonacci number. -/
theorem b_pm (n : ℕ) : ∃ m, b n = Nat.fib m ∨ b n = -(Nat.fib m : ℤ) := by
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 10 ∧ n = 10 * q + r :=
    ⟨n/10, n%10, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod n 10).symm⟩
  have e : ∀ c:ℕ, (10*q + c) % 10 = c % 10 := by intro c; omega
  have R3 : (Nat.fib (10*q+3):ℤ) = Nat.fib (10*q+1) + Nat.fib (10*q+2) := by exact_mod_cast Nat.fib_add_two
  have R5 : (Nat.fib (10*q+5):ℤ) = Nat.fib (10*q+3) + Nat.fib (10*q+4) := by exact_mod_cast Nat.fib_add_two
  have R8 : (Nat.fib (10*q+8):ℤ) = Nat.fib (10*q+6) + Nat.fib (10*q+7) := by exact_mod_cast Nat.fib_add_two
  have R10 : (Nat.fib (10*q+10):ℤ) = Nat.fib (10*q+8) + Nat.fib (10*q+9) := by exact_mod_cast Nat.fib_add_two
  interval_cases r
  · exact ⟨10*q,   Or.inl (by simp only [b, Nat.add_zero, Nat.mul_mod_right])⟩
  · exact ⟨10*q+1, Or.inl (by simp only [b, e, Nat.reduceMod])⟩
  · exact ⟨10*q+1, Or.inl (by simp only [b, e, Nat.reduceMod, Nat.add_assoc, Nat.reduceAdd]; omega)⟩
  · exact ⟨0,      Or.inl (by simp only [b, e, Nat.reduceMod, Nat.fib_zero, Nat.cast_zero])⟩
  · exact ⟨10*q+3, Or.inr (by simp only [b, e, Nat.reduceMod, Nat.add_assoc, Nat.reduceAdd]; omega)⟩
  · exact ⟨10*q+5, Or.inr (by simp only [b, e, Nat.reduceMod])⟩
  · exact ⟨10*q+6, Or.inr (by simp only [b, e, Nat.reduceMod])⟩
  · exact ⟨10*q+6, Or.inr (by simp only [b, e, Nat.reduceMod, Nat.add_assoc, Nat.reduceAdd]; omega)⟩
  · exact ⟨0,      Or.inl (by simp only [b, e, Nat.reduceMod, Nat.fib_zero, Nat.cast_zero])⟩
  · exact ⟨10*q+8, Or.inl (by simp only [b, e, Nat.reduceMod, Nat.add_assoc, Nat.reduceAdd]; omega)⟩

/--
Conjecture: all elements in absolute value are Fibonacci numbers. That is, for every $n$, $|a(n)| = \operatorname{fib}(m)$ for some $m \in \mathbb{N}$.
-/
theorem oeis_103311_conjecture_0 (n : ℕ) : ∃ m : ℕ, Int.natAbs (a n) = Nat.fib m := by
  obtain ⟨m, hm⟩ := b_pm n
  refine ⟨m, ?_⟩
  rw [key n]
  rcases hm with h | h <;> rw [h] <;> simp
