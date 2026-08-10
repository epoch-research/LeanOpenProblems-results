import FormalConjectures.Util.ProblemImports

open Nat Int

/--
A113254: Corresponds to $m = 8$ in a family of 4th-order linear recurrence sequences.

The sequence $a(n)$ is defined by the initial conditions $a(0)=-1, a(1)=4, a(2)=176, a(3)=3136$,
and the linear recurrence relation $a(n) = -4 * a (n-1) + 256 * a (n-3) + 4096 * a (n-4)$ for $n \ge 4$.
-/
def a (n : ℕ) : ℤ :=
  match n with
  | 0 => -1
  | 1 => 4
  | 2 => 176
  | 3 => 3136
  | n' + 4 => -4 * a (n' + 3) + 256 * a (n' + 1) + 4096 * a n'

def L : ℕ → ℤ
  | 0 => 2
  | 1 => 1
  | n + 2 => L (n + 1) - 4 * L n

def witness (n : ℕ) : ℤ := (2 : ℤ) ^ (2 * n + 1) * L (n + 1)

def F (n : ℕ) : ℤ := witness n * witness n

lemma L_sq_rec (n : ℕ) :
    L (n + 4)^2 = -3 * L (n + 3)^2 + 12 * L (n + 2)^2 + 64 * L (n + 1)^2 := by
  have h3 : L (n + 4) = L (n + 3) - 4 * L (n + 2) := by cases n <;> rfl
  have h2 : L (n + 3) = L (n + 2) - 4 * L (n + 1) := by cases n <;> rfl
  rw [h3, h2]
  ring

lemma F_eq (n : ℕ) : F n = 4 * (16 : ℤ)^n * L (n + 1)^2 := by
  have h16 : (16 : ℤ)^n = 2^(n * 4) := by
    calc
      (16 : ℤ)^n = ((2 : ℤ)^4)^n := by norm_num
      _ = (2 : ℤ)^(4 * n) := by rw [pow_mul]
      _ = (2 : ℤ)^(n * 4) := by rw [Nat.mul_comm n 4]
  unfold F witness
  rw [show (4 : ℤ) = 2^2 by norm_num, h16]
  ring_nf

lemma F_rec (n : ℕ) :
    F (n + 3) = -48 * F (n + 2) + 3072 * F (n + 1) + 262144 * F n := by
  repeat rw [F_eq]
  rw [L_sq_rec]
  ring_nf

lemma a_six_rec (n : ℕ) :
    a (n + 6) = -48 * a (n + 4) + 3072 * a (n + 2) + 262144 * a n := by
  simp [a]
  ring

lemma a_odd_square_aux : ∀ n : ℕ, a (2 * n + 1) = F n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rcases n with _ | _ | _ | k
      · norm_num [a, F, witness, L]
      · norm_num [a, F, witness, L]
      · norm_num [a, F, witness, L]
      · have hrecA := a_six_rec (2 * k + 1)
        have hA : a (2 * (k + 3) + 1) =
            -48 * a (2 * (k + 2) + 1) + 3072 * a (2 * (k + 1) + 1) + 262144 * a (2 * k + 1) := by
          simpa only [Nat.cast_ofNat] using hrecA
        have hk2 : a (2 * (k + 2) + 1) = F (k + 2) := ih (k + 2) (by omega)
        have hk1 : a (2 * (k + 1) + 1) = F (k + 1) := ih (k + 1) (by omega)
        have hk0 : a (2 * k + 1) = F k := ih k (by omega)
        calc
          a (2 * (k + 3) + 1) = -48 * a (2 * (k + 2) + 1) + 3072 * a (2 * (k + 1) + 1) + 262144 * a (2 * k + 1) := hA
          _ = -48 * F (k + 2) + 3072 * F (k + 1) + 262144 * F k := by rw [hk2, hk1, hk0]
          _ = F (k + 3) := (F_rec k).symm

/-- oeis_113254_conjecture_0: Conjecture: a(m, 2*n+1) is a perfect square for all m,n (see A113249).
For the specific sequence A113254 (which fixes m=8), this conjecture is interpreted as:
a(2*n+1) is a perfect square for all n.
-/
theorem oeis_113254_conjecture_0 : ∀ n : ℕ, IsSquare (a (2 * n + 1)) := by
  intro n
  exact ⟨witness n, a_odd_square_aux n⟩
