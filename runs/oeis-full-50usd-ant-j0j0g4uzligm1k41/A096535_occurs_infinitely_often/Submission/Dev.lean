import FormalConjectures.Util.ProblemImports

def A096535 : ℕ → ℕ
| 0 => 1
| 1 => 1
| n + 2 => (A096535 (n + 1) + A096535 n) % (n + 2)

@[simp] lemma A096535_zero : A096535 0 = 1 := rfl
@[simp] lemma A096535_one : A096535 1 = 1 := rfl
lemma A096535_succ_succ (n : ℕ) :
    A096535 (n + 2) = (A096535 (n + 1) + A096535 n) % (n + 2) := rfl

/-- For all `n`, `A096535 n ≤ n + 1` (a uniform bound; for `n ≥ 2` it is `< n`). -/
lemma A096535_le (n : ℕ) : A096535 n ≤ n + 1 := by
  match n with
  | 0 => simp
  | 1 => simp
  | (m + 2) =>
    rw [A096535_succ_succ]
    exact le_trans (Nat.le_of_lt (Nat.mod_lt _ (by omega))) (by omega)

/-- `A096535 n < n + 2` for all `n`. -/
lemma A096535_lt_add_two (n : ℕ) : A096535 n < n + 2 := by
  have := A096535_le n; omega

/-- The sharp bound `A096535 n < n` for `n ≥ 2`. -/
lemma A096535_strict_lt (n : ℕ) (hn : 2 ≤ n) : A096535 n < n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [show 2 + m = m + 2 by ring, A096535_succ_succ]
  exact Nat.mod_lt _ (by omega)

/-- Consecutive terms never both vanish: `1 ≤ A096535 n + A096535 (n+1)`. -/
lemma A096535_consec_pos (n : ℕ) : 1 ≤ A096535 n + A096535 (n + 1) := by
  induction n with
  | zero => simp
  | succ m ih =>
    show 1 ≤ A096535 (m + 1) + A096535 (m + 2)
    rcases Nat.eq_zero_or_pos (A096535 (m + 1)) with h0 | hpos
    · have hm : 1 ≤ A096535 m := by omega
      have hlt : A096535 m < m + 2 := A096535_lt_add_two m
      have heq : A096535 (m + 2) = A096535 m := by
        rw [A096535_succ_succ m, h0, zero_add, Nat.mod_eq_of_lt hlt]
      omega
    · omega

/-- In the "no reduction" regime the recurrence is exactly Fibonacci. -/
lemma A096535_fib_step (m : ℕ) (h : A096535 (m + 1) + A096535 m < m + 2) :
    A096535 (m + 2) = A096535 (m + 1) + A096535 m := by
  rw [A096535_succ_succ, Nat.mod_eq_of_lt h]

/-- Under a global bound `B`, the recurrence is pure Fibonacci from index `2B` on. -/
lemma A096535_fib_of_bounded {B : ℕ} (hB : ∀ n, A096535 n ≤ B) (m : ℕ)
    (hm : 2 * B ≤ m) :
    A096535 (m + 2) = A096535 (m + 1) + A096535 m := by
  apply A096535_fib_step
  have h1 := hB (m + 1); have h2 := hB m; omega

/-- Core growth step: at any `p ≥ 2B`, the consecutive-sum potential increases by ≥1
over two indices. All indices are in canonical `p + k` form. -/
lemma A096535_grow {B : ℕ} (hB : ∀ n, A096535 n ≤ B) (p : ℕ) (hp : 2 * B ≤ p) :
    A096535 p + A096535 (p + 1) + 1 ≤ A096535 (p + 2) + A096535 (p + 3) := by
  have hfib2 : A096535 (p + 2) = A096535 (p + 1) + A096535 p :=
    A096535_fib_of_bounded hB p hp
  -- `A096535_fib_of_bounded hB (p+1) : A096535 (p+1+2) = A096535 (p+1+1) + A096535 (p+1)`,
  -- and `p+1+2 ≡ p+3`, `p+1+1 ≡ p+2` definitionally.
  have hfib3 : A096535 (p + 3) = A096535 (p + 2) + A096535 (p + 1) :=
    A096535_fib_of_bounded hB (p + 1) (by omega)
  -- `A096535_consec_pos (p+1) : 1 ≤ A096535 (p+1) + A096535 (p+1+1)`, `p+1+1 ≡ p+2`.
  have hpos : 1 ≤ A096535 (p + 1) + A096535 (p + 2) := A096535_consec_pos (p + 1)
  omega

/-- Linear lower bound on the potential: `A096535 (2B+2t) + A096535 (2B+2t+1) ≥ t + 1`. -/
lemma A096535_pot {B : ℕ} (hB : ∀ n, A096535 n ≤ B) (t : ℕ) :
    t + 1 ≤ A096535 (2 * B + 2 * t) + A096535 (2 * B + 2 * t + 1) := by
  induction t with
  | zero =>
    show 1 ≤ A096535 (2 * B) + A096535 (2 * B + 1)
    exact A096535_consec_pos (2 * B)
  | succ s ih =>
    have hk := A096535_grow hB (2 * B + 2 * s) (by omega)
    -- hk : A(2B+2s) + A(2B+2s+1) + 1 ≤ A(2B+2s+2) + A(2B+2s+3)
    show s + 1 + 1 ≤ A096535 (2 * B + 2 * s + 2) + A096535 (2 * B + 2 * s + 3)
    omega

/-- **Theorem (provable).** `A096535` is unbounded. -/
theorem A096535_unbounded : ∀ B : ℕ, ∃ n, B < A096535 n := by
  intro B
  by_contra h
  push_neg at h    -- h : ∀ n, A096535 n ≤ B
  have hlin := A096535_pot h (2 * B)
  have hb1 := h (2 * B + 2 * (2 * B))
  have hb2 := h (2 * B + 2 * (2 * B) + 1)
  omega

/-- In the reduction regime (`a(m+1)+a(m) ≥ m+2`) the recurrence is
`a(m+2) + (m+2) = a(m+1) + a(m)`. -/
lemma A096535_reduce_step (m : ℕ) (h : m + 2 ≤ A096535 (m + 1) + A096535 m) :
    A096535 (m + 2) + (m + 2) = A096535 (m + 1) + A096535 m := by
  rw [A096535_succ_succ]
  have hlt : (A096535 (m + 1) + A096535 m) - (m + 2) < m + 2 := by
    have h1 := A096535_le (m + 1); have h2 := A096535_le m; omega
  rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt hlt]
  omega

/-- **Deficit recurrence.** Writing the deficit `d n := n - a n`, in the reduction regime
`d (m+2) = d (m+1) + d m + 3`.  (Stated additively to avoid `ℕ`-subtraction.) -/
lemma A096535_deficit_step (m : ℕ) (hm : 2 ≤ m)
    (h : m + 2 ≤ A096535 (m + 1) + A096535 m) :
    ((m + 2) - A096535 (m + 2)) =
      ((m + 1) - A096535 (m + 1)) + (m - A096535 m) + 3 := by
  have hr := A096535_reduce_step m h
  have h1 : A096535 (m + 1) < m + 1 := A096535_strict_lt (m + 1) (by omega)
  have h2 : A096535 m < m := A096535_strict_lt m hm
  omega

/-- **Theorem (provable).** `a(n) < 2n/3` infinitely often, i.e. `liminf a(n)/n ≤ 2/3`.
The point: if `a` stayed `≥ 2n/3` on a tail, reductions would be forced forever, and the
deficit `n - a(n)` would obey `d(n)=d(n-1)+d(n-2)+3`, growing past `n/3` — impossible. -/
theorem A096535_below_two_thirds_io :
    ∀ N : ℕ, ∃ n, N < n ∧ 3 * A096535 n < 2 * n := by
  intro N
  by_contra hcon
  push_neg at hcon          -- hcon : ∀ n, N < n → 2 * n ≤ 3 * A096535 n
  set M0 := N + 5 with hM0
  -- (1) Under `hcon`, a reduction is forced at every step `p ≥ M0`.
  have hred : ∀ p, M0 ≤ p → p + 2 ≤ A096535 (p + 1) + A096535 p := by
    intro p hp
    have a1 := hcon (p + 1) (by omega)
    have a2 := hcon p (by omega)
    omega
  -- (2) Hence the deficit grows by ≥ 4 every two steps, for `p ≥ M0`.
  have hgrow : ∀ p, M0 ≤ p →
      (p - A096535 p) + 4 ≤ (p + 2 - A096535 (p + 2)) := by
    intro p hp
    have hd := A096535_deficit_step p (by omega) (hred p hp)
    have h1 : A096535 (p + 1) < p + 1 := A096535_strict_lt (p + 1) (by omega)
    omega
  -- (3) Linear lower bound on the deficit at indices `M0 + 2t`.
  have hpot : ∀ t, 1 + 4 * t ≤ (M0 + 2 * t - A096535 (M0 + 2 * t)) := by
    intro t
    induction t with
    | zero =>
      simp only [Nat.mul_zero, Nat.add_zero]
      have := A096535_strict_lt M0 (by omega)
      omega
    | succ s ih =>
      have hg := hgrow (M0 + 2 * s) (by omega)
      show 1 + 4 * (s + 1) ≤ M0 + 2 * s + 2 - A096535 (M0 + 2 * s + 2)
      omega
  -- (4) But the deficit is always ≤ the index, so at `t = M0` (index `3·M0`) we get
  --     `1 + 4·M0 ≤ 3·M0`, a contradiction.
  have hp := hpot M0
  omega

/-- **Theorem (provable).** `a(n) > n/3` infinitely often, i.e. `limsup a(n)/n ≥ 1/3`.
If `a` stayed `≤ n/3` on a tail, no reduction ever occurs, so `a` is pure Fibonacci and
the consecutive-sum potential *doubles* every two steps — exponential growth that overtakes
the linear bound `2n/3`. -/
theorem A096535_above_third_io :
    ∀ N : ℕ, ∃ n, N < n ∧ n < 3 * A096535 n := by
  intro N
  by_contra hcon
  push_neg at hcon          -- hcon : ∀ n, N < n → 3 * A096535 n ≤ n
  set base := N + 1 with hbase
  -- (1) `a ≤ n/3` on the tail forces pure Fibonacci from `base` on.
  have hfib : ∀ p, base ≤ p → A096535 (p + 2) = A096535 (p + 1) + A096535 p := by
    intro p hp
    apply A096535_fib_step
    have b1 := hcon (p + 1) (by omega)
    have b2 := hcon p (by omega)
    omega
  -- (2) The consecutive-sum potential at least doubles every two steps.
  have hdouble : ∀ p, base ≤ p →
      2 * (A096535 p + A096535 (p + 1)) ≤ A096535 (p + 2) + A096535 (p + 3) := by
    intro p hp
    have f2 := hfib p hp
    have f3 : A096535 (p + 3) = A096535 (p + 2) + A096535 (p + 1) := hfib (p + 1) (by omega)
    omega
  -- (3) Exponential lower bound: potential `≥ 2^t`.
  have hpot : ∀ t, 2 ^ t ≤ A096535 (base + 2 * t) + A096535 (base + 2 * t + 1) := by
    intro t
    induction t with
    | zero =>
      simp only [pow_zero, Nat.mul_zero, Nat.add_zero]
      exact A096535_consec_pos base
    | succ s ih =>
      have hd := hdouble (base + 2 * s) (by omega)
      have hps : 2 ^ (s + 1) = 2 * 2 ^ s := by rw [pow_succ]; ring
      show 2 ^ (s + 1) ≤ A096535 (base + 2 * s + 2) + A096535 (base + 2 * s + 3)
      omega
  -- (4) But `a ≤ n/3` bounds the potential linearly; exponential beats linear ⇒ contradiction.
  have hp := hpot (N + 5)
  have c1 := hcon (base + 2 * (N + 5)) (by omega)
  have c2 := hcon (base + 2 * (N + 5) + 1) (by omega)
  have hx : N < 2 ^ N := Nat.lt_two_pow_self
  have hpow : 2 ^ (N + 5) = 32 * 2 ^ N := by rw [pow_add]; ring
  omega

/-- **Sharp upper frontier.** `2·a(n) < n + 2` (i.e. `a(n) ≤ n/2`) infinitely often.
This is the sharp form: the deficit-growth engine forces `a` below `n/2` i.o., and the
threshold `1/2` is exactly where it stops (below it, reductions are no longer forced). -/
theorem A096535_below_half_io :
    ∀ N : ℕ, ∃ n, N < n ∧ 2 * A096535 n < n + 2 := by
  intro N
  by_contra hcon
  push_neg at hcon          -- hcon : ∀ n, N < n → n + 2 ≤ 2 * A096535 n
  set M0 := N + 3 with hM0
  have hred : ∀ p, M0 ≤ p → p + 2 ≤ A096535 (p + 1) + A096535 p := by
    intro p hp
    have a1 := hcon (p + 1) (by omega)
    have a2 := hcon p (by omega)
    omega
  have hgrow : ∀ p, M0 ≤ p →
      (p - A096535 p) + 4 ≤ (p + 2 - A096535 (p + 2)) := by
    intro p hp
    have hd := A096535_deficit_step p (by omega) (hred p hp)
    have h1 : A096535 (p + 1) < p + 1 := A096535_strict_lt (p + 1) (by omega)
    omega
  have hpot : ∀ t, 1 + 4 * t ≤ (M0 + 2 * t - A096535 (M0 + 2 * t)) := by
    intro t
    induction t with
    | zero =>
      simp only [Nat.mul_zero, Nat.add_zero]
      have := A096535_strict_lt M0 (by omega)
      omega
    | succ s ih =>
      have hg := hgrow (M0 + 2 * s) (by omega)
      show 1 + 4 * (s + 1) ≤ M0 + 2 * s + 2 - A096535 (M0 + 2 * s + 2)
      omega
  have hp := hpot M0
  omega

/-- **Sharp lower frontier.** `n < 2·a(n) + 2` (i.e. `a(n) > (n−2)/2`) infinitely often.
Dual of `below_half_io`: if `a` stayed `≤ (n−2)/2`, no reduction ever occurs, the potential
*doubles* every two steps (exponential), overtaking the linear bound — contradiction. Together
with `below_half_io` this shows the elementary frontier is exactly `1/2` on both sides. -/
theorem A096535_above_half_io :
    ∀ N : ℕ, ∃ n, N < n ∧ n < 2 * A096535 n + 2 := by
  intro N
  by_contra hcon
  push_neg at hcon          -- hcon : ∀ n, N < n → 2 * A096535 n + 2 ≤ n
  set base := N + 1 with hbase
  have hfib : ∀ p, base ≤ p → A096535 (p + 2) = A096535 (p + 1) + A096535 p := by
    intro p hp
    apply A096535_fib_step
    have b1 := hcon (p + 1) (by omega)
    have b2 := hcon p (by omega)
    omega
  have hdouble : ∀ p, base ≤ p →
      2 * (A096535 p + A096535 (p + 1)) ≤ A096535 (p + 2) + A096535 (p + 3) := by
    intro p hp
    have f2 := hfib p hp
    have f3 : A096535 (p + 3) = A096535 (p + 2) + A096535 (p + 1) := hfib (p + 1) (by omega)
    omega
  have hpot : ∀ t, 2 ^ t ≤ A096535 (base + 2 * t) + A096535 (base + 2 * t + 1) := by
    intro t
    induction t with
    | zero =>
      simp only [pow_zero, Nat.mul_zero, Nat.add_zero]
      exact A096535_consec_pos base
    | succ s ih =>
      have hd := hdouble (base + 2 * s) (by omega)
      have hps : 2 ^ (s + 1) = 2 * 2 ^ s := by rw [pow_succ]; ring
      show 2 ^ (s + 1) ≤ A096535 (base + 2 * s + 2) + A096535 (base + 2 * s + 3)
      omega
  have hp := hpot (N + 5)
  have c1 := hcon (base + 2 * (N + 5)) (by omega)
  have c2 := hcon (base + 2 * (N + 5) + 1) (by omega)
  have hx : N < 2 ^ N := Nat.lt_two_pow_self
  have hpow : 2 ^ (N + 5) = 32 * 2 ^ N := by rw [pow_add]; ring
  omega

#check @A096535_consec_pos
#check @A096535_unbounded
#check @A096535_reduce_step
#check @A096535_deficit_step
#check @A096535_below_two_thirds_io
#check @A096535_below_half_io
#check @A096535_above_third_io
#check @A096535_above_half_io

#print axioms A096535_below_half_io
#print axioms A096535_above_half_io
