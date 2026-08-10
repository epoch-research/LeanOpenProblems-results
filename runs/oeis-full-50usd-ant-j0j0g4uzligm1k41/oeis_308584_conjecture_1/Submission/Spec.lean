import FormalConjectures.Util.ProblemImports

open Nat Finset

/-- The $k$-th triangular number, $T_k = k(k+1)/2$. -/
def triangular_number (k : ℕ) : ℕ := k * (k + 1) / 2

/--
A308584: Number of ways to write $n$ as $a(a+1)/2 + b(b+1)/2 + 5^c \cdot 8^d$,
where $a,b,c,d$ are nonnegative integers with $a \le b$.
-/
noncomputable def A308584 (n : ℕ) : ℕ :=
  let T := triangular_number

  -- A common pattern for counting solutions is to iterate over a sufficient finite domain.
  -- Since $T(a), T(b), 5^c, 8^d$ must all be $\le n$, $a, b, c, d$ are bounded by $n$.
  let bound := n + 1
  let R := Finset.range bound

  -- The search space is $R \times R \times R \times R$. We use the canonical nested product structure.
  let search_space : Finset (((ℕ × ℕ) × ℕ) × ℕ) :=
    ((R.product R).product R).product R

  (search_space.filter fun t =>
    -- Extract a, b, c, d from the nested tuple structure: ( ((a, b), c), d )
    let ab_pair := t.fst.fst
    let c         := t.fst.snd
    let d         := t.snd
    let a         := ab_pair.fst
    let b         := ab_pair.snd

    -- The core condition of the sequence definition
    a ≤ b ∧ T a + T b + 5^c * 8^d = n
  ).card

/-
Conjecture: $a(n) > 0$ for all $n > 0$.
Equivalently, each $n = 1,2,3,\dots$ can be written as $\text{triangular\_number}(a) + \text{triangular\_number}(b) + 5^c \cdot 8^d$
with $a,b,c,d$ nonnegative integers and $a \le b$.
The OEIS entry also states an equivalent conjecture:
each $n = 1,2,3,\dots$ can be written as $w^2 + x(x+1)/2 + 5^y \cdot 8^z$
with $w,x,y,z$ nonnegative integers.
(We formalize the direct conjecture: $a(n) > 0$.)
-/
/-- `k ≤ triangular_number k` for every `k`. -/
lemma le_triangular_number (k : ℕ) : k ≤ triangular_number k := by
  unfold triangular_number
  rcases Nat.eq_zero_or_pos k with h | h
  · simp [h]
  · rw [Nat.le_div_iff_mul_le (by norm_num)]; nlinarith

/--
**Reduction lemma.** `A308584 n > 0` holds iff `n` genuinely admits a representation
`triangular_number a + triangular_number b + 5^c * 8^d = n` with `a ≤ b`.

This shows the finite search bound `n + 1` used in the definition of `A308584` never
discards a valid representation: from the equation one derives `a, b, c, d ≤ n`
(using `k ≤ triangular_number k` and `k < 5^k`, `k < 8^k`), so every genuine
representation lies inside the searched box.
-/
lemma A308584_pos_iff (n : ℕ) :
    A308584 n > 0 ↔
      ∃ a b c d : ℕ, a ≤ b ∧ triangular_number a + triangular_number b + 5^c * 8^d = n := by
  unfold A308584
  simp only
  rw [gt_iff_lt, Finset.card_pos]
  constructor
  · rintro ⟨t, ht⟩
    rw [Finset.mem_filter] at ht
    exact ⟨t.fst.fst.fst, t.fst.fst.snd, t.fst.snd, t.snd, ht.2.1, ht.2.2⟩
  · rintro ⟨a, b, c, d, hab, heq⟩
    have hpow : 5 ^ c * 8 ^ d ≤ n := by omega
    have h5 : 5 ^ c ≤ n := le_trans (Nat.le_mul_of_pos_right _ (by positivity)) hpow
    have h8 : 8 ^ d ≤ n := le_trans (Nat.le_mul_of_pos_left _ (by positivity)) hpow
    have hb : b ≤ n := le_trans (le_triangular_number b) (by omega)
    have ha : a ≤ n := le_trans (le_triangular_number a) (by omega)
    have hc : c ≤ n := le_trans (Nat.le_of_lt (Nat.lt_pow_self (by norm_num))) h5
    have hd : d ≤ n := le_trans (Nat.le_of_lt (Nat.lt_pow_self (by norm_num))) h8
    refine ⟨(((a, b), c), d), ?_⟩
    rw [Finset.mem_filter]
    refine ⟨?_, hab, heq⟩
    refine Finset.mem_product.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩, ?_⟩
    · exact Finset.mem_range.mpr (Nat.lt_succ_of_le ha)
    · exact Finset.mem_range.mpr (Nat.lt_succ_of_le hb)
    · exact Finset.mem_range.mpr (Nat.lt_succ_of_le hc)
    · exact Finset.mem_range.mpr (Nat.lt_succ_of_le hd)

/--
The genuinely open number-theoretic core (Zhi-Wei Sun's conjecture, OEIS A308584):
every positive integer `n` is a sum of two triangular numbers and a term of the form
`5^c * 8^d`.

Equivalently (via `T a + T b = m ↔ 4 m + 1` is a sum of two squares): for every `n`,
at least one of the `~(log n)²` values `4 n + 1 − 5^c · 2^{3 d + 2}` is a sum of two
squares.  This is a *thin multiplicative-summand* additive problem — the same difficulty
class as the open question "`n = x² + y² + 2^k`" — and remains unproven.  It has been
verified computationally for all `n ≤ 2·10⁹`.
-/
lemma A308584_core (n : ℕ) (hn : n > 0) :
    ∃ a b c d : ℕ, a ≤ b ∧ triangular_number a + triangular_number b + 5^c * 8^d = n := by
  sorry

theorem oeis_308584_conjecture_1 : ∀ (n : ℕ), n > 0 → A308584 n > 0 := by
  intro n hn
  rw [A308584_pos_iff]
  exact A308584_core n hn
