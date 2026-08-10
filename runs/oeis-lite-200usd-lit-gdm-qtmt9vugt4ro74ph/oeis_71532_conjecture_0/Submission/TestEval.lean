import FormalConjectures.Util.ProblemImports

open BigOperators Int Real

def a_fast_loop : ℕ → ℕ → ℕ → ℤ → ℤ
  | 0, _, _, acc => acc
  | m + 1, p3, p2, acc =>
    let p3' := p3 * 3
    let p2' := p2 * 2
    let term : ℤ := if (p3' / p2') % 2 = 0 then -1 else 1
    a_fast_loop m p3' p2' (acc + term)

def a_fast (n : ℕ) : ℤ :=
  a_fast_loop n 1 1 0

lemma a_fast_loop_add (m n : ℕ) (p3 p2 : ℕ) (acc : ℤ) :
  a_fast_loop (m + n) p3 p2 acc = a_fast_loop n (p3 * 3^m) (p2 * 2^m) (a_fast_loop m p3 p2 acc) := by
  induction m generalizing p3 p2 acc with
  | zero =>
    simp [a_fast_loop]
  | succ m ih =>
    have h_add : m + 1 + n = m + n + 1 := by omega
    rw [h_add]
    dsimp [a_fast_loop]
    rw [ih (p3 * 3) (p2 * 2)]
    congr 1
    · have : 3 * 3^m = 3^(m+1) := by ring
      rw [mul_assoc, this]
    · have : 2 * 2^m = 2^(m+1) := by ring
      rw [mul_assoc, this]

lemma a_fast_add (m n : ℕ) :
  a_fast (m + n) = a_fast_loop n (3^m) (2^m) (a_fast m) := by
  dsimp [a_fast]
  rw [a_fast_loop_add]
  simp

set_option maxRecDepth 1000000
set_option exponentiation.threshold 1000000

lemma a_fast_1000 : a_fast 1000 = 102 := by rfl

lemma a_fast_2000 : a_fast 2000 = 96 := by
  have h : a_fast (1000 + 1000) = a_fast_loop 1000 (3^1000) (2^1000) (a_fast 1000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_1000]
  rfl
