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

/-!
## Reduction of the conjecture to its arithmetic core

The conjecture `a(n) > 0 for all n > 0` is equivalent to the statement that every
positive integer `n` admits a representation `n = T a + T b + 5^c * 8^d` with `a ≤ b`.
Below we formalise the (elementary) reduction of `A308584 n > 0` to the bare existence
of such a representation, and prove the auxiliary bounds that show such a representation,
if it exists, is automatically found inside the finite search space of `A308584`.

The remaining ingredient -- the *existence* of a representation for every `n` -- is exactly
Zhi-Wei Sun's conjecture A308584.
-/

/-- Auxiliary identity: a sum of two triangular numbers, scaled, is a sum of two odd squares.
This is the bridge `T a + T b = m ⟺ 8 m + 2 = (2a+1)² + (2b+1)²`, i.e. `m` is a sum of two
triangular numbers iff `4 m + 1` is a sum of two squares. -/
theorem eight_tri_add_two (a b : ℕ) :
    8 * (triangular_number a + triangular_number b) + 2 = (2 * a + 1) ^ 2 + (2 * b + 1) ^ 2 := by
  unfold triangular_number
  have ha : a * (a + 1) % 2 = 0 := by
    rcases Nat.even_or_odd a with ⟨k, hk⟩ | ⟨k, hk⟩ <;> subst hk <;> ring_nf <;> omega
  have hb : b * (b + 1) % 2 = 0 := by
    rcases Nat.even_or_odd b with ⟨k, hk⟩ | ⟨k, hk⟩ <;> subst hk <;> ring_nf <;> omega
  have e1 : a * (a + 1) / 2 * 2 = a * (a + 1) := Nat.div_mul_cancel (by omega)
  have e2 : b * (b + 1) / 2 * 2 = b * (b + 1) := Nat.div_mul_cancel (by omega)
  nlinarith [e1, e2]

/-- **Elementary bridge.** A number `m` is a sum of two triangular numbers iff `4 m + 1` is a sum
of two squares. This is purely algebraic (no analytic input) and lets one restate the open core of
A308584 in the sum-of-two-squares language used in the literature. -/
theorem tri2_iff_sq (m : ℕ) :
    (∃ a b : ℕ, triangular_number a + triangular_number b = m) ↔
    (∃ x y : ℕ, x ^ 2 + y ^ 2 = 4 * m + 1) := by
  constructor
  · rintro ⟨a, b, hm⟩
    rcases le_total a b with hab | hab
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hab
      refine ⟨2 * a + k + 1, k, ?_⟩
      have key := eight_tri_add_two a (a + k)
      rw [hm] at key
      have h2 : 2 * ((2 * a + k + 1) ^ 2 + k ^ 2) = (2 * a + 1) ^ 2 + (2 * (a + k) + 1) ^ 2 := by
        ring
      omega
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hab
      refine ⟨2 * b + k + 1, k, ?_⟩
      have key := eight_tri_add_two (b + k) b
      rw [hm] at key
      have h2 : 2 * ((2 * b + k + 1) ^ 2 + k ^ 2) = (2 * (b + k) + 1) ^ 2 + (2 * b + 1) ^ 2 := by
        ring
      omega
  · rintro ⟨x, y, hxy⟩
    have hpar : (Odd x ∧ Even y) ∨ (Even x ∧ Odd y) := by
      rcases Nat.even_or_odd x with hx | hx <;> rcases Nat.even_or_odd y with hy | hy
      · exfalso
        obtain ⟨i, rfl⟩ := hx; obtain ⟨j, rfl⟩ := hy
        have e : (i + i) ^ 2 + (j + j) ^ 2 = 4 * (i ^ 2 + j ^ 2) := by ring
        omega
      · exact Or.inr ⟨hx, hy⟩
      · exact Or.inl ⟨hx, hy⟩
      · exfalso
        obtain ⟨i, rfl⟩ := hx; obtain ⟨j, rfl⟩ := hy
        have e : (2 * i + 1) ^ 2 + (2 * j + 1) ^ 2 = 4 * (i ^ 2 + i + j ^ 2 + j) + 2 := by ring
        omega
    have build : ∀ u v : ℕ, Odd u → Even v → u ^ 2 + v ^ 2 = 4 * m + 1 →
        ∃ a b : ℕ, triangular_number a + triangular_number b = m := by
      intro u v hu hv huv
      obtain ⟨i, rfl⟩ := hu
      obtain ⟨j, rfl⟩ := hv
      rcases lt_or_ge i j with hlt | hge
      · obtain ⟨d, rfl⟩ : ∃ d, j = i + 1 + d := ⟨j - i - 1, by omega⟩
        refine ⟨2 * i + 1 + d, d, ?_⟩
        have key := eight_tri_add_two (2 * i + 1 + d) d
        have h1 : (2 * (2 * i + 1 + d) + 1) ^ 2 + (2 * d + 1) ^ 2
            = 2 * ((2 * i + 1) ^ 2 + ((i + 1 + d) + (i + 1 + d)) ^ 2) := by ring
        rw [h1, huv] at key
        omega
      · obtain ⟨d, rfl⟩ : ∃ d, i = j + d := ⟨i - j, by omega⟩
        refine ⟨2 * j + d, d, ?_⟩
        have key := eight_tri_add_two (2 * j + d) d
        have h1 : (2 * (2 * j + d) + 1) ^ 2 + (2 * d + 1) ^ 2
            = 2 * ((2 * (j + d) + 1) ^ 2 + (j + j) ^ 2) := by ring
        rw [h1, huv] at key
        omega
    rcases hpar with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · exact build x y hx hy hxy
    · exact build y x hy hx (by linarith [hxy])

/-- `T₂` is closed under `m ↦ 5m+1`: if `m` is a sum of two triangular numbers, so is `5m+1`.
Follows from `tri2_iff_sq` and `5 = 1²+2²` via closure of sums of two squares under products. -/
theorem five_tri (m : ℕ) (h : ∃ a b : ℕ, triangular_number a + triangular_number b = m) :
    ∃ a b : ℕ, triangular_number a + triangular_number b = 5 * m + 1 := by
  rw [tri2_iff_sq] at h ⊢
  obtain ⟨x, y, hxy⟩ := h
  obtain ⟨r, s, hrs⟩ :=
    Nat.sq_add_sq_mul (show (5 : ℕ) = 1 ^ 2 + 2 ^ 2 by norm_num) hxy.symm
  exact ⟨r, s, by omega⟩

/-- **Self-reducibility of A308584 under `n ↦ 5n+1`.** If `m` has a representation
`T a + T b + 5^c·8^d` (with `a ≤ b`), then so does `5m+1` (with `c` increased by one).
This is the unique rigorously-available transfer map for the conjecture; it covers only the
residue class `n ≡ 1 (mod 5)`, which is why it cannot, on its own, settle the conjecture. -/
theorem rep_five_map (m : ℕ)
    (h : ∃ a b c d : ℕ, a ≤ b ∧ triangular_number a + triangular_number b + 5 ^ c * 8 ^ d = m) :
    ∃ a b c d : ℕ, a ≤ b ∧
      triangular_number a + triangular_number b + 5 ^ c * 8 ^ d = 5 * m + 1 := by
  obtain ⟨a, b, c, d, hab, hsum⟩ := h
  obtain ⟨a', b', hab'⟩ := five_tri _ ⟨a, b, rfl⟩
  have hpow : (5 : ℕ) ^ (c + 1) * 8 ^ d = 5 * (5 ^ c * 8 ^ d) := by rw [pow_succ]; ring
  rcases le_total a' b' with hle | hle
  · exact ⟨a', b', c + 1, d, hle, by rw [hpow]; omega⟩
  · exact ⟨b', a', c + 1, d, hle, by rw [hpow]; omega⟩

/-- Any actual representation `T a + T b + 5^c * 8^d = n` has all of `a, b, c, d` bounded by `n`,
hence lies inside the finite search domain used to define `A308584`. -/
theorem bounds_of_rep (n a b c d : ℕ) (hn : 0 < n)
    (hsum : triangular_number a + triangular_number b + 5 ^ c * 8 ^ d = n) :
    a ≤ n ∧ b ≤ n ∧ c ≤ n ∧ d ≤ n := by
  have hTa : triangular_number a ≤ n := by
    have : 0 ≤ triangular_number b + 5 ^ c * 8 ^ d := by positivity
    omega
  have hTb : triangular_number b ≤ n := by omega
  have hpow : 5 ^ c * 8 ^ d ≤ n := by omega
  have han : a ≤ n := by
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · omega
    · unfold triangular_number at hTa
      have : a * 2 ≤ a * (a + 1) := by nlinarith
      have : a ≤ a * (a + 1) / 2 := by omega
      omega
  have hbn : b ≤ n := by
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · omega
    · unfold triangular_number at hTb
      have : b * 2 ≤ b * (b + 1) := by nlinarith
      have : b ≤ b * (b + 1) / 2 := by omega
      omega
  have h5 : 5 ^ c ≤ n := le_trans (Nat.le_mul_of_pos_right _ (by positivity)) hpow
  have h8 : 8 ^ d ≤ n := le_trans (Nat.le_mul_of_pos_left _ (by positivity)) hpow
  have hcn : c ≤ n := by
    have : c < 5 ^ c := lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_left (by norm_num) c)
    omega
  have hdn : d ≤ n := by
    have : d < 8 ^ d := lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_left (by norm_num) d)
    omega
  exact ⟨han, hbn, hcn, hdn⟩

/-- Reduction lemma: the existence of *any* representation `n = T a + T b + 5^c * 8^d` with
`a ≤ b` (the witnesses are automatically bounded by `bounds_of_rep`) yields `A308584 n > 0`. -/
theorem A308584_pos_of_rep (n : ℕ) (hn : n > 0)
    (h : ∃ a b c d : ℕ, a ≤ b ∧ triangular_number a + triangular_number b + 5 ^ c * 8 ^ d = n) :
    A308584 n > 0 := by
  obtain ⟨a, b, c, d, hab, hsum⟩ := h
  obtain ⟨ha, hb, hc, hd⟩ := bounds_of_rep n a b c d hn hsum
  rw [A308584, gt_iff_lt, Finset.card_pos]
  refine ⟨(((a, b), c), d), ?_⟩
  rw [Finset.mem_filter]
  refine ⟨?_, hab, hsum⟩
  refine Finset.mem_product.mpr
    ⟨Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩, ?_⟩
  · exact Finset.mem_range.mpr (by show a < n + 1; omega)
  · exact Finset.mem_range.mpr (by show b < n + 1; omega)
  · exact Finset.mem_range.mpr (by show c < n + 1; omega)
  · exact Finset.mem_range.mpr (by show d < n + 1; omega)

/--
**The arithmetic core of conjecture A308584 (Zhi-Wei Sun), reduced to its `5`-roots.**

Thanks to the verified transfer map `rep_five_map` (`G(m) ⟹ G(5m+1)`), the full conjecture
`A308584_representation` follows by strong induction from this statement restricted to the
`5`-roots `n % 5 ≠ 1`. (The class `n ≡ 1 (mod 5)` is handled inductively, with base case `n = 1`.)

By `tri2_iff_sq`, `T a + T b = m` is solvable iff `4 m + 1` is a sum of two squares, so this is
equivalent to: *for every such `n` there is a power `p = 5^c 8^d ≤ n` with `4(n - p) + 1` a sum
of two squares.* This belongs to the class of "sum of two squares plus a sparse multiplicative
set" problems and is an **open** conjecture of Zhi-Wei Sun (verified for all `n ≤ 2·10¹⁰`).
A rigorous obstruction argument shows no covering/congruence/finite-case proof can exist (the set
of sums of two squares contains no infinite arithmetic progression), so any proof must be analytic;
no such unconditional proof is currently known, nor is the requisite machinery present in Mathlib.
-/
theorem A308584_representation_roots (n : ℕ) (hn : n > 0) (hr : n % 5 ≠ 1) :
    ∃ a b c d : ℕ, a ≤ b ∧ triangular_number a + triangular_number b + 5 ^ c * 8 ^ d = n := by
  sorry

theorem A308584_representation (n : ℕ) (hn : n > 0) :
    ∃ a b c d : ℕ, a ≤ b ∧ triangular_number a + triangular_number b + 5 ^ c * 8 ^ d = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hmod : n % 5 = 1
    · rcases Nat.lt_or_ge n 2 with h1 | h2
      · have hn1 : n = 1 := by omega
        subst hn1
        exact ⟨0, 0, 0, 0, le_refl 0, by norm_num [triangular_number]⟩
      · obtain ⟨m, hm⟩ : ∃ m, n = 5 * m + 1 := ⟨n / 5, by omega⟩
        have hmlt : m < n := by omega
        have hmpos : m > 0 := by omega
        have hrep := ih m hmlt hmpos
        rw [hm]
        exact rep_five_map m hrep
    · exact A308584_representation_roots n hn hmod

/--
Conjecture: $a(n) > 0$ for all $n > 0$.
Equivalently, each $n = 1,2,3,\dots$ can be written as $\text{triangular\_number}(a) + \text{triangular\_number}(b) + 5^c \cdot 8^d$
with $a,b,c,d$ nonnegative integers and $a \le b$.
The OEIS entry also states an equivalent conjecture:
each $n = 1,2,3,\dots$ can be written as $w^2 + x(x+1)/2 + 5^y \cdot 8^z$
with $w,x,y,z$ nonnegative integers.
(We formalize the direct conjecture: $a(n) > 0$.)
-/
theorem oeis_308584_conjecture_1 : ∀ (n : ℕ), n > 0 → A308584 n > 0 :=
by
  intro n hn
  exact A308584_pos_of_rep n hn (A308584_representation n hn)
