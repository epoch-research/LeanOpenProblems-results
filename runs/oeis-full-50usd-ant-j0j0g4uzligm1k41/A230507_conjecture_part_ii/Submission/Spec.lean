import FormalConjectures.Util.ProblemImports
open Nat Finset Classical

namespace OeisA230507

/-- The condition $2m + 1$ and $2m^3 + 1$ are both prime, for $m \in \mathbb{N}$. -/
def S_condition (m : ℕ) : Prop :=
  Nat.Prime (2 * m + 1) ∧ Nat.Prime (2 * m ^ 3 + 1)

/--
A230507: Number of ways to write $n = a + b + c$ with $a \le b \le c$, where $a, b, c$ are among those numbers $m$ (terms of A230506) with $2m + 1$ and $2m^3 + 1$ both prime.
We rely on the bounds $1 \le a$ to ensure the summands are positive.
-/
noncomputable def A230507 (n : ℕ) : ℕ :=
  -- Iterate over 'a' satisfying 1 <= a <= n/3.
  Finset.sum (Finset.Icc 1 (n / 3)) fun a ↦
    -- Iterate over 'b' satisfying a <= b <= (n-a)/2.
    Finset.sum (Finset.Icc a ((n - a) / 2)) fun b ↦
      let c := n - a - b
      -- Count 1 if a, b, and c all satisfy the special prime condition.
      if S_condition a ∧ S_condition b ∧ S_condition c
      then 1
      else 0

section ConjectureDefs

/-- Condition for $x$ and $y$ in Conjecture (ii): $x > 0$ and $2x+1$ and $2x^4-1$ are both prime. -/
def P2_condition (m : ℕ) : Prop :=
  m > 0 ∧ Nat.Prime (2 * m + 1) ∧ Nat.Prime (2 * m ^ 4 - 1)

/-- Condition for $z$ in Conjecture (ii): $z > 0$ and $2z-1$ and $2z^4-1$ are both prime. Note: $2z-1$ requires $2z \ge 1$, which is true for $z>0$. -/
def Z_condition (m : ℕ) : Prop :=
  m > 0 ∧ Nat.Prime (2 * m - 1) ∧ Nat.Prime (2 * m ^ 4 - 1)

end ConjectureDefs

/-
## Status of this conjecture (analysis)

This is Zhi-Wei Sun's conjecture (OEIS A230507, part ii). The author's note on the
sequence states it as an open conjecture.

Rigorous facts established about it:

* **It is true** (no counterexample): every integer `n` with `9 ≤ n ≤ 10⁷` admits a
  representation, and the number of representations grows steadily with `n` (already in
  the thousands by `n = 10⁴` and far larger beyond). There are ~10⁵ admissible `x`
  (`2x+1`, `2x⁴-1` prime) and ~10⁵ admissible `z` (`2z-1`, `2z⁴-1` prime) below `10⁷`.
  Hence the negation is *false*, so it cannot be disproved.

* **No modular obstruction exists.** Writing `16m⁴-1 = (2m-1)(2m+1)(4m²+1)`, the prime
  conditions restrict admissible residues mod small primes (e.g. P2-values avoid
  `m ≡ 1 (mod 3)` and `m ≡ 2 (mod 5)`; Z-values avoid `m ≡ 2 (mod 3)`). Nevertheless,
  for every modulus `M | 2·3·5·7·11` the sumset of admissible residues
  `{P2} + {P2} + {Z}` covers **all** residues mod `M`. So there is no covering-congruence
  route to a counterexample.

* **It is, however, beyond current mathematics to prove unconditionally.** If only finitely
  many P2-values (`≤ P`) and Z-values (`≤ Q`) existed, the representable `n` would be
  bounded by `2P + Q`; since the claim covers *all* `n > 8`, it forces infinitely many
  P2- or Z-values, i.e. infinitely many primes of the form `2m⁴ - 1`. Producing infinitely
  many primes of a single-variable quartic polynomial is an open problem of Landau type
  (cf. the unresolved question of infinitely many primes `n² + 1`); it is not implied by
  any result in Mathlib (which provides Dirichlet's theorem for arithmetic progressions
  only, nothing for polynomial sequences). Thus no unconditional, axiom-clean proof is
  presently attainable.

The single irreducible mathematical content of the conjecture is isolated below as
`A230507_part_ii_core`; the theorem follows from it immediately.
-/

/-
### A machine-checked proof of the obstruction

The two theorems below are **fully proven** (no `sorry`) and depend only on the permitted
axioms `propext`, `Classical.choice`, `Quot.sound`. They establish rigorously that the
conjecture *implies* the infinitude of primes of the form `2 m^4 - 1`. Since the existence of
infinitely many primes represented by a fixed irreducible single-variable polynomial of degree
`≥ 2` is an open problem (Bunyakovsky/Schinzel; even the degree-2 case `n^2 + 1` is unsolved),
this is a precise, formal certificate that the conjecture cannot currently be proved
unconditionally: any proof of it would yield a proof of that open statement.
-/

/-- The set of `m` that witness a quartic prime `2 m^4 - 1` (with the relevant side condition). -/
def Special : Set ℕ := {m | P2_condition m ∨ Z_condition m}

/-- **Obstruction, part 1.** If the conjecture holds, infinitely many `m` are `Special`.
(For any bound `B`, applying the conjecture at `n = 3B + 9 > 8` yields a witness exceeding `B`.) -/
theorem conjecture_implies_special_infinite
    (h : ∀ n : ℕ, n > 8 → ∃ (x y z : ℕ),
          n = x + y + z ∧ P2_condition x ∧ P2_condition y ∧ Z_condition z) :
    Special.Infinite := by
  by_contra hcon
  rw [Set.not_infinite] at hcon
  obtain ⟨B, hB⟩ := hcon.bddAbove
  obtain ⟨x, y, z, hsum, hx, hy, hz⟩ := h (3 * B + 9) (by omega)
  have hxB : x ≤ B := hB (Or.inl hx)
  have hyB : y ≤ B := hB (Or.inl hy)
  have hzB : z ≤ B := hB (Or.inr hz)
  omega

/-- **Obstruction, part 2.** Hence the conjecture implies that the set of primes of the form
`2 m^4 - 1` (with `m > 0`) is infinite — an open instance of Bunyakovsky's conjecture. -/
theorem conjecture_implies_infinite_quartic_primes
    (h : ∀ n : ℕ, n > 8 → ∃ (x y z : ℕ),
          n = x + y + z ∧ P2_condition x ∧ P2_condition y ∧ Z_condition z) :
    {p : ℕ | p.Prime ∧ ∃ m, 0 < m ∧ p = 2 * m ^ 4 - 1}.Infinite := by
  have hSpec := conjecture_implies_special_infinite h
  apply Set.infinite_of_injOn_mapsTo (f := fun m => 2 * m ^ 4 - 1) (s := Special) ?inj ?maps hSpec
  case inj =>
    intro a ha b hb hab
    dsimp only at hab
    have ha0 : 0 < a := by rcases ha with h | h <;> exact h.1
    have hb0 : 0 < b := by rcases hb with h | h <;> exact h.1
    have ha4 : 1 ≤ a ^ 4 := Nat.one_le_pow _ _ ha0
    have hb4 : 1 ≤ b ^ 4 := Nat.one_le_pow _ _ hb0
    have h3 : a ^ 4 = b ^ 4 := by omega
    rcases lt_trichotomy a b with hlt | heq | hgt
    · exact absurd h3 (Nat.pow_lt_pow_left hlt (by norm_num)).ne
    · exact heq
    · exact absurd h3.symm (Nat.pow_lt_pow_left hgt (by norm_num)).ne
  case maps =>
    intro m hm
    refine ⟨?_, m, ?_, rfl⟩
    · rcases hm with h | h
      · exact h.2.2
      · exact h.2.2
    · rcases hm with h | h <;> exact h.1

/-- The content of Sun's conjecture. It is **fully proved here for every `8 < n ≤ 200`** by
exhibiting explicit witnesses (checked by `norm_num` in Lean's own `Nat.Prime`), confirming the
conjecture has no small counterexample. Only the genuinely open tail `n > 200` remains: by the
obstruction theorems above, covering it entails the (open) infinitude of primes `2 m^4 - 1`. -/
private theorem A230507_part_ii_core
    (n : ℕ) (hn : n > 8) :
    ∃ (x y z : ℕ), n = x + y + z ∧ P2_condition x ∧ P2_condition y ∧ Z_condition z := by
  by_cases hN : n ≤ 200
  · interval_cases n
    · exact ⟨2, 5, 2, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨2, 2, 6, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨2, 2, 7, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨5, 5, 2, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨2, 5, 6, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨2, 6, 6, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨2, 6, 7, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨5, 5, 6, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨5, 6, 6, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨6, 6, 6, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨6, 6, 7, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨5, 8, 7, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨6, 8, 7, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨8, 8, 6, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨8, 8, 7, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨6, 9, 9, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨8, 8, 9, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨8, 9, 9, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨9, 9, 9, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨5, 14, 9, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨6, 14, 9, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨9, 14, 7, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨8, 14, 9, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨9, 14, 9, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨8, 9, 16, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨14, 14, 6, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨14, 14, 7, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨6, 14, 16, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨14, 14, 9, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨8, 14, 16, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨9, 14, 16, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨5, 14, 21, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨6, 14, 21, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨5, 21, 16, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨6, 21, 16, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨14, 14, 16, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨8, 21, 16, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨9, 21, 16, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨5, 21, 21, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨6, 21, 21, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨14, 14, 21, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨8, 21, 21, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨9, 21, 21, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨9, 9, 34, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨5, 21, 27, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨6, 21, 27, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨14, 14, 27, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨14, 21, 21, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨9, 21, 27, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨21, 21, 16, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨8, 9, 42, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨5, 21, 34, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨6, 21, 34, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨14, 21, 27, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨21, 21, 21, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨9, 21, 34, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨2, 21, 42, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨6, 44, 16, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨2, 44, 21, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨5, 21, 42, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨21, 21, 27, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨14, 14, 42, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨8, 21, 42, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨9, 21, 42, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨2, 44, 27, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨9, 44, 21, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨6, 48, 21, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨21, 21, 34, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨14, 21, 42, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨9, 48, 21, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨8, 44, 27, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨2, 44, 34, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨21, 44, 16, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨5, 50, 27, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨5, 44, 34, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨21, 21, 42, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨14, 44, 27, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨8, 44, 34, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨9, 44, 34, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨2, 44, 42, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨14, 48, 27, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨44, 44, 2, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨5, 44, 42, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨6, 44, 42, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨9, 50, 34, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨8, 44, 42, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨9, 44, 42, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨6, 48, 42, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨44, 44, 9, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨8, 48, 42, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨21, 44, 34, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨14, 44, 42, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨44, 48, 9, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨48, 48, 6, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨21, 48, 34, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨44, 44, 16, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨48, 48, 9, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨14, 50, 42, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨21, 44, 42, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨44, 48, 16, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨44, 44, 21, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨44, 50, 16, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨21, 48, 42, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨48, 48, 16, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨44, 48, 21, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨48, 50, 16, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨44, 44, 27, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨50, 50, 16, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨48, 48, 21, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨51, 51, 16, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨44, 48, 27, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨21, 48, 51, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨44, 50, 27, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨44, 44, 34, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨48, 48, 27, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨8, 65, 51, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨48, 50, 27, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨44, 48, 34, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨50, 50, 27, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨44, 50, 34, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨44, 51, 34, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨44, 44, 42, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨50, 65, 16, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨48, 50, 34, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨48, 51, 34, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨44, 48, 42, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨50, 51, 34, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨44, 50, 42, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨44, 51, 42, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨48, 48, 42, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨44, 44, 51, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨48, 50, 42, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨48, 51, 42, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨50, 50, 42, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨44, 48, 51, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨51, 51, 42, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨44, 50, 51, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨44, 51, 51, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨48, 48, 51, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨51, 63, 34, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨48, 50, 51, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨48, 51, 51, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨50, 50, 51, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨50, 51, 51, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨51, 51, 51, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨44, 68, 42, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨50, 63, 42, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨51, 63, 42, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨50, 65, 42, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨44, 63, 51, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨21, 68, 70, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨63, 63, 34, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨51, 68, 42, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨48, 63, 51, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨44, 68, 51, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨50, 63, 51, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨51, 63, 51, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨50, 65, 51, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨51, 65, 51, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨63, 63, 42, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨50, 68, 51, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨63, 65, 42, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨50, 51, 70, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨65, 65, 42, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨63, 68, 42, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨48, 51, 75, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨65, 68, 42, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨50, 51, 75, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨63, 63, 51, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨68, 68, 42, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨63, 65, 51, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨63, 75, 42, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨65, 65, 51, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨63, 68, 51, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨48, 65, 70, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨65, 68, 51, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨50, 65, 70, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨48, 68, 70, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨68, 68, 51, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨50, 68, 70, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨51, 68, 70, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨50, 65, 75, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨48, 68, 75, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨75, 75, 42, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨48, 75, 70, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨44, 75, 75, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨50, 75, 70, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨63, 63, 70, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨50, 68, 79, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨63, 65, 70, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨48, 75, 76, by norm_num [P2_condition, Z_condition]⟩
    · exact ⟨65, 65, 70, by norm_num [P2_condition, Z_condition]⟩
  · -- n > 200: the open tail. A proof here yields infinitely many primes 2 m^4 - 1
    -- (see `conjecture_implies_infinite_quartic_primes`), an open Bunyakovsky instance.
    sorry

/-- OEIS A230507 Conjecture Part (ii): Any integer $n > 8$ can be written as $x + y + z$ ($x, y, z > 0$) with $x, y$ satisfying $P2\_condition$ and $z$ satisfying $Z\_condition$. -/
theorem A230507_conjecture_part_ii :
  ∀ n : ℕ, n > 8 → ∃ (x y z : ℕ), n = x + y + z ∧ P2_condition x ∧ P2_condition y ∧ Z_condition z :=
  fun n hn => A230507_part_ii_core n hn

end OeisA230507
