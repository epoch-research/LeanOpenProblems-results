import FormalConjectures.Util.ProblemImports
import Submission.DetAnti13
import Submission.DetAnti14

open Nat Finset Matrix

/--
A228304: The sequence $a(n)$ is defined by the alternating sum of fourth powers of binomial coefficients.
$$a(n) = \sum_{k=0}^n \binom{n}{k}^4 (-1)^k$$
-/
def a (n : ℕ) : ℤ :=
  Finset.sum (range (n + 1)) fun k => ((-1 : ℤ) ^ k) * ((choose n k : ℤ) ^ 4)

/--
A228304 c(n) sequence:
$$c(n) = \sum_{k=0}^n (-1)^k \binom{n}{k}^2 \binom{2k}{k} \binom{2(n-k)}{n-k}$$
-/
def c (n : ℕ) : ℤ :=
  Finset.sum (range (n + 1)) fun k =>
    ((-1 : ℤ) ^ k) * ((choose n k : ℤ) ^ 2) * (choose (2 * k) k : ℤ) * (choose (2 * (n - k)) (n - k) : ℤ)

/--
A228304 Conjecture: Let p be any odd prime, and let A(p) be the p X p determinant with (i,j)-entry equal to a(i+j) for all i,j = 0,...,p-1. Then A(p) == (-1)^{(p-1)/2} (mod p). Similarly, if c(n) = sum_{k=0}^n (-1)^k*C(n,k)^2*C(2k,k)*C(2(n-k),n-k) and C(p) is the p X p determinant with (i,j)-entry equal to c(i+j) for all i,j = 0,...,p-1, then we have C(p) == 1 (mod p).
-/
theorem oeis_228304_conjecture_0 (p : ℕ) (hp : Nat.Prime p) (h_odd : p ≠ 2) :
    let N := Fin p
    let half_minus_one := (p - 1) / 2
    -- A(p) is the p x p matrix with entries a(i+j)
    let A : Matrix N N ℤ := fun i j => a (i.val + j.val)
    -- C(p) is the p x p matrix with entries c(i+j)
    let C : Matrix N N ℤ := fun i j => c (i.val + j.val)
    (Matrix.det A ≡ (-1 : ℤ) ^ half_minus_one [ZMOD p]) ∧ (Matrix.det C ≡ 1 [ZMOD p]) := by
  intro N half_minus_one A C
  haveI : Fact p.Prime := ⟨hp⟩
  have eq_A : A = fun i j => a_val (i.val + j.val) := by
    ext i j
    dsimp [A, a, a_val]
  have eq_C : C = fun i j => c_val (i.val + j.val) := by
    ext i j
    dsimp [C, c, c_val]
  constructor
  · rw [eq_A, ← ZMod.intCast_eq_intCast_iff]
    have h_RHS : (((-1 : ℤ) ^ half_minus_one : ℤ) : ZMod p) = (-1 : ZMod p) ^ half_minus_one := by push_cast; rfl
    rw [h_RHS]
    exact a_matrix_mod_p p h_odd
  · rw [eq_C, ← ZMod.intCast_eq_intCast_iff]
    have h_RHS : ((1 : ℤ) : ZMod p) = 1 := by push_cast; rfl
    rw [h_RHS]
    exact c_matrix_mod_p p h_odd

theorem oeis_228304_conjecture_0.disproof : ¬ (type_of% @oeis_228304_conjecture_0) := sorry
