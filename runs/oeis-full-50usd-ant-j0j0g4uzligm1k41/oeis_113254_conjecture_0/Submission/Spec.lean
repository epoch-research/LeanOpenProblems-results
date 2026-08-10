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

/- Auxiliary complex root of x^2 + 4x + 64. -/

/-- A root `rt` of `x^2 + 4x + 64 = 0` (i.e. `-2 + 2*i*√15`, here written `-2 + i*√60`). -/
noncomputable def rt : ℂ := -2 + Complex.I * (Real.sqrt 60 : ℂ)

/-- The conjugate root. -/
noncomputable def rb : ℂ := -4 - rt

lemma rt_sq : rt ^ 2 = -4 * rt - 64 := by
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  have h60 : ((Real.sqrt 60 : ℝ) : ℂ) ^ 2 = 60 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 60)]
    norm_num
  unfold rt
  linear_combination ((Real.sqrt 60 : ℝ) : ℂ) ^ 2 * hI - h60

lemma rt_sum : rt + rb = -4 := by unfold rb; ring

lemma rt_prod : rt * rb = 64 := by unfold rb; linear_combination -rt_sq

lemma rb_sq : rb ^ 2 = -4 * rb - 64 := by unfold rb; linear_combination rt_sq

lemma rt_rec (m : ℕ) : rt ^ (m + 2) = -4 * rt ^ (m + 1) - 64 * rt ^ m := by
  rw [pow_add, rt_sq]; ring

lemma rb_rec (m : ℕ) : rb ^ (m + 2) = -4 * rb ^ (m + 1) - 64 * rb ^ m := by
  rw [pow_add, rb_sq]; ring

/- Integer linear recurrence sequences. -/

/-- `c n = s(n+1)` where `s` is the Lucas-type sequence `r^n + conj r^n`; equivalently
`4 * a n = 8*8^n - 8*(-8)^n + c n`. -/
def c : ℕ → ℤ
  | 0 => -4
  | 1 => -112
  | (k + 2) => -4 * c (k + 1) - 64 * c k

/-- The square-root sequence: `c n = 2 * d n` and `a (2n+1) = d n ^ 2`. -/
def d : ℕ → ℤ
  | 0 => -2
  | 1 => -56
  | (k + 2) => -4 * d (k + 1) - 64 * d k

/-- Order-4 recurrence satisfied by `c`. -/
lemma c_rec4 (k : ℕ) : c (k + 4) = -4 * c (k + 3) + 256 * c (k + 1) + 4096 * c k := by
  have e1 : c (k + 4) = -4 * c (k + 3) - 64 * c (k + 2) := rfl
  have e2 : c (k + 2) = -4 * c (k + 1) - 64 * c k := rfl
  rw [e1, e2]; ring

/-- Cast of `c` to `ℂ` in terms of the roots. -/
lemma c_cast (k : ℕ) : (c k : ℂ) = rt ^ (k + 1) + rb ^ (k + 1) := by
  have H : ∀ k, ((c k : ℂ) = rt ^ (k + 1) + rb ^ (k + 1)) ∧
      ((c (k + 1) : ℂ) = rt ^ (k + 2) + rb ^ (k + 2)) := by
    intro k
    induction k with
    | zero =>
      refine ⟨?_, ?_⟩
      · have : (c 0 : ℂ) = -4 := by norm_num [c]
        rw [this]; simp only [zero_add, pow_one]; linear_combination -rt_sum
      · have : (c 1 : ℂ) = -112 := by norm_num [c]
        rw [this, rt_sq, rb_sq]; linear_combination (4 : ℂ) * rt_sum
    | succ m ih =>
      obtain ⟨ih0, ih1⟩ := ih
      refine ⟨ih1, ?_⟩
      have hr : rt ^ (m + 3) = -4 * rt ^ (m + 2) - 64 * rt ^ (m + 1) := rt_rec (m + 1)
      have hrb : rb ^ (m + 3) = -4 * rb ^ (m + 2) - 64 * rb ^ (m + 1) := rb_rec (m + 1)
      have hcast : (c (m + 2) : ℂ) = -4 * (c (m + 1) : ℂ) - 64 * (c m : ℂ) := by
        have hh : c (m + 2) = -4 * c (m + 1) - 64 * c m := rfl
        rw [hh]; push_cast; ring
      rw [hcast, ih0, ih1, hr, hrb]; ring
  exact (H k).1

/-- `c n = 2 * d n`. -/
lemma c_eq_two_d (k : ℕ) : c k = 2 * d k := by
  have H : ∀ k, (c k = 2 * d k) ∧ (c (k + 1) = 2 * d (k + 1)) := by
    intro k
    induction k with
    | zero => exact ⟨rfl, rfl⟩
    | succ m ih =>
      obtain ⟨ih0, ih1⟩ := ih
      refine ⟨ih1, ?_⟩
      have hc : c (m + 2) = -4 * c (m + 1) - 64 * c m := rfl
      have hd : d (m + 2) = -4 * d (m + 1) - 64 * d m := rfl
      rw [hc, hd, ih0, ih1]; ring
  exact (H k).1

/-- Closed form for `a`. -/
lemma a_closed (n : ℕ) : 4 * a n = 8 * 8 ^ n - 8 * (-8) ^ n + c n := by
  have H : ∀ n,
      (4 * a n = 8 * 8 ^ n - 8 * (-8) ^ n + c n) ∧
      (4 * a (n + 1) = 8 * 8 ^ (n + 1) - 8 * (-8) ^ (n + 1) + c (n + 1)) ∧
      (4 * a (n + 2) = 8 * 8 ^ (n + 2) - 8 * (-8) ^ (n + 2) + c (n + 2)) ∧
      (4 * a (n + 3) = 8 * 8 ^ (n + 3) - 8 * (-8) ^ (n + 3) + c (n + 3)) := by
    intro n
    induction n with
    | zero => refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num [a, c]
    | succ k ih =>
      obtain ⟨ih0, ih1, ih2, ih3⟩ := ih
      refine ⟨ih1, ih2, ih3, ?_⟩
      show 4 * a (k + 4) = 8 * 8 ^ (k + 4) - 8 * (-8) ^ (k + 4) + c (k + 4)
      have hrec : a (k + 4) = -4 * a (k + 3) + 256 * a (k + 1) + 4096 * a k := rfl
      have h4 : 4 * a (k + 4)
          = -4 * (4 * a (k + 3)) + 256 * (4 * a (k + 1)) + 4096 * (4 * a k) := by
        rw [hrec]; ring
      rw [h4, ih0, ih1, ih3, c_rec4 k]
      simp only [pow_add]; ring
  exact (H n).1

/-- The doubling identity. -/
lemma c_double (n : ℕ) : c n ^ 2 = c (2 * n + 1) + 128 * 64 ^ n := by
  have hc : (c n : ℂ) ^ 2 = (c (2 * n + 1) : ℂ) + 128 * 64 ^ n := by
    rw [c_cast n, c_cast (2 * n + 1)]
    have e1 : rt ^ (2 * n + 1 + 1) = (rt ^ (n + 1)) ^ 2 := by
      rw [show 2 * n + 1 + 1 = (n + 1) * 2 by ring, pow_mul]
    have e2 : rb ^ (2 * n + 1 + 1) = (rb ^ (n + 1)) ^ 2 := by
      rw [show 2 * n + 1 + 1 = (n + 1) * 2 by ring, pow_mul]
    have e3 : rt ^ (n + 1) * rb ^ (n + 1) = 64 ^ (n + 1) := by
      rw [← mul_pow, rt_prod]
    have e4 : (64 : ℂ) ^ (n + 1) = 64 * 64 ^ n := by rw [pow_succ]; ring
    rw [e1, e2]
    linear_combination (2 : ℂ) * e3 + (2 : ℂ) * e4
  exact_mod_cast hc

lemma pow8 (n : ℕ) : (8 : ℤ) ^ (2 * n + 1) = 8 * 64 ^ n := by
  rw [pow_succ, pow_mul]; norm_num [mul_comm]

lemma powm8 (n : ℕ) : (-8 : ℤ) ^ (2 * n + 1) = -8 * 64 ^ n := by
  rw [pow_succ, pow_mul]; norm_num [mul_comm]

/-- oeis_113254_conjecture_0: Conjecture: a(m, 2*n+1) is a perfect square for all m,n (see A113249).
For the specific sequence A113254 (which fixes m=8), this conjecture is interpreted as:
a(2*n+1) is a perfect square for all n.
-/
theorem oeis_113254_conjecture_0 : ∀ n : ℕ, IsSquare (a (2 * n + 1)) := by
  intro n
  refine ⟨d n, ?_⟩
  have key : 4 * a (2 * n + 1) = 4 * (d n * d n) := by
    have hA := a_closed (2 * n + 1)
    rw [hA, pow8, powm8]
    have hdbl := c_double n
    have hcd := c_eq_two_d n
    linear_combination (-1 : ℤ) * hdbl + (c n + 2 * d n) * hcd
  exact mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0) key
