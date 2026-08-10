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

/-- Auxiliary sequence `c`, with `c n = 8^n * cos (n θ)` where `cos θ = -1/4`.
It satisfies the order-2 recurrence with characteristic polynomial `x^2 + 4x + 64`. -/
private def c : ℕ → ℤ
  | 0 => 1
  | 1 => -2
  | (n+2) => -4 * c (n+1) - 64 * c n

/-- Auxiliary sequence `s`, with `8^n * sin (n θ) = √15 * s n`. Same recurrence as `c`. -/
private def s : ℕ → ℤ
  | 0 => 0
  | 1 => 2
  | (n+2) => -4 * s (n+1) - 64 * s n

private lemma c_rec (n : ℕ) : c (n+2) = -4 * c (n+1) - 64 * c n := rfl
private lemma s_rec (n : ℕ) : s (n+2) = -4 * s (n+1) - 64 * s n := rfl
private lemma a_rec (n : ℕ) : a (n+4) = -4 * a (n+3) + 256 * a (n+1) + 4096 * a n := rfl

/-- Closed form for `a`: `2 * a n = 4·8^n - 4·(-8)^n + c (n+1)`. -/
private theorem key2 : ∀ n, 2 * a n = 4 * 8^n - 4 * (-8)^n + c (n+1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => decide
    | 1 => decide
    | 2 => decide
    | 3 => decide
    | (m+4) =>
      have h3 := ih (m+3) (by omega)
      have h1 := ih (m+1) (by omega)
      have h0 := ih m (by omega)
      have ha : a (m+4) = -4 * a (m+3) + 256 * a (m+1) + 4096 * a m := a_rec m
      have hc5 : c (m+5) = -4 * c (m+4) - 64 * c (m+3) := c_rec (m+3)
      have hc4 : c (m+4) = -4 * c (m+3) - 64 * c (m+2) := c_rec (m+2)
      have hc3 : c (m+3) = -4 * c (m+2) - 64 * c (m+1) := c_rec (m+1)
      have p8 : (8:ℤ)^(m+4) = 8^m * 4096 := by rw [pow_add]; norm_num
      have p8b : (8:ℤ)^(m+3) = 8^m * 512 := by rw [pow_add]; norm_num
      have p8c : (8:ℤ)^(m+1) = 8^m * 8 := by rw [pow_add]; norm_num
      have q8 : (-8:ℤ)^(m+4) = (-8)^m * 4096 := by rw [pow_add]; norm_num
      have q8b : (-8:ℤ)^(m+3) = (-8)^m * (-512) := by rw [pow_add]; norm_num
      have q8c : (-8:ℤ)^(m+1) = (-8)^m * (-8) := by rw [pow_add]; norm_num
      show 2 * a (m+4) = 4 * 8^(m+4) - 4 * (-8)^(m+4) + c (m+5)
      have e3 : c (m+3+1) = c (m+4) := rfl
      have e1 : c (m+1+1) = c (m+2) := rfl
      rw [e3] at h3
      rw [e1] at h1
      linarith [ha, h3, h1, h0, hc5, hc4, hc3, p8, p8b, p8c, q8, q8b, q8c]

/-- The "step" relations linking consecutive `c`, `s` values. -/
private theorem step : ∀ m, c (m+1) = -2 * c m - 30 * s m ∧ s (m+1) = 2 * c m - 2 * s m := by
  intro m
  induction m with
  | zero => decide
  | succ k ih =>
    obtain ⟨ihc, ihs⟩ := ih
    refine ⟨?_, ?_⟩
    · linarith [c_rec k, ihc, ihs]
    · linarith [s_rec k, ihc, ihs]

/-- Addition formula (the "angle-addition" identity). -/
private theorem add_formula : ∀ n m,
    c (m+n) = c m * c n - 15 * s m * s n ∧ s (m+n) = c m * s n + s m * c n := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero => intro m; simp [c, s]
  | one =>
    intro m
    obtain ⟨hc, hs⟩ := step m
    refine ⟨?_, ?_⟩
    · simp only [c, s]; linarith [hc, hs]
    · simp only [c, s]; linarith [hc, hs]
  | more n ih1 ih2 =>
    intro m
    obtain ⟨ihc1, ihs1⟩ := ih1 m
    obtain ⟨ihc2, ihs2⟩ := ih2 m
    have hassoc : m + (n+2) = (m+n)+2 := by ring
    rw [show m+(n+1) = m+n+1 from rfl] at ihc2 ihs2
    rw [hassoc]
    constructor
    · rw [c_rec (m+n), c_rec n, s_rec n]
      rw [ihc2, ihc1]; ring
    · rw [s_rec (m+n), c_rec n, s_rec n]
      rw [ihs2, ihs1]; ring

/-- Norm identity: `c n ^ 2 + 15 * s n ^ 2 = 64 ^ n`. -/
private theorem norm : ∀ n, c n ^ 2 + 15 * s n ^ 2 = 64 ^ n := by
  intro n
  induction n with
  | zero => decide
  | succ k ih =>
    obtain ⟨hc, hs⟩ := step k
    have pk : (64:ℤ) ^ (k+1) = 64 ^ k * 64 := by rw [pow_add]; norm_num
    rw [hc, hs, pk]
    linear_combination 64 * ih

/-- oeis_113254_conjecture_0: Conjecture: a(m, 2*n+1) is a perfect square for all m,n (see A113249).
For the specific sequence A113254 (which fixes m=8), this conjecture is interpreted as:
a(2*n+1) is a perfect square for all n.
-/
theorem oeis_113254_conjecture_0 : ∀ n : ℕ, IsSquare (a (2 * n + 1)) := by
  intro n
  have hk := key2 (2*n+1)
  have e1 : (8:ℤ) ^ (2*n+1) = 64 ^ n * 8 := by rw [pow_succ, pow_mul]; norm_num
  have e2 : (-8:ℤ) ^ (2*n+1) = 64 ^ n * (-8) := by rw [pow_succ, pow_mul]; norm_num
  rw [e1, e2] at hk
  have idx : 2*n+1+1 = 2*(n+1) := by ring
  rw [idx] at hk
  have hd := (add_formula (n+1) (n+1)).1
  have hsum : (n+1)+(n+1) = 2*(n+1) := by ring
  rw [hsum] at hd
  have hn := norm (n+1)
  have hp : (64:ℤ) ^ (n+1) = 64 ^ n * 64 := by rw [pow_add]; norm_num
  have h2 : 2 * a (2*n+1) = 2 * (c (n+1) * c (n+1)) := by
    rw [hk, hd]
    nlinarith [hn, hp]
  have key : a (2*n+1) = c (n+1) * c (n+1) :=
    mul_left_cancel₀ (by norm_num : (2:ℤ) ≠ 0) h2
  exact ⟨c (n+1), key⟩
