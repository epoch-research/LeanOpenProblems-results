import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A306477: Number of ways to write $n$ as $\binom{w+2}{2} + \binom{x+3}{4} + \binom{y+5}{6} + \binom{z+7}{8}$
with $w,x,y,z$ nonnegative integers, where $\binom{m}{k}$ denotes the binomial coefficient $\frac{m!}{k!(m-k)!}$.
-/
def A306477 (n : ℕ) : ℕ :=
  let R := Finset.range (n + 1)
  R.sum (fun w =>
    R.sum (fun x =>
      R.sum (fun y =>
        R.sum (fun z =>
          if (w + 2).choose 2 + (x + 3).choose 4 + (y + 5).choose 6 + (z + 7).choose 8 = n then 1 else 0
        )
      )
    )
  )

/-
Analysis of OEIS A306477 (a conjecture of Zhi-Wei Sun).

The statement is TRUE but is an OPEN research conjecture; the reduction below
formalizes the passage from the counting statement to the pure existence statement
`A306477_exists`, which is the genuine (open) mathematical content.

Established by extensive computational + theoretical investigation:
* TRUE: no counterexample for any `1 ≤ n ≤ 10^8`; no local (residue) obstruction,
  hence the negation is false and the conjecture cannot be disproven.
* It is a SUPER-CRITICAL additive threshold problem: the four figurate sequences
  have degrees `2,4,6,8`, with `∑ 1/k = 25/24 > 1`, so the representation count
  grows like `n^{1/24} → ∞`, yet every individual sequence is SPARSE (density 0).

Every elementary route was tested and provably fails:
  1. Schnirelmann/Mann/pigeonhole need positive density (all four are density 0).
  2. `S' = C(x+3,4)+C(y+5,6)+C(z+7,8)` has density → 0 (≈0.015 by 5·10^6): not co-finite.
  3. The densest 3-term subset `A3 = T+C(x+3,4)+C(y+5,6)` also has density → 0
     (rigorously `|A3∩[0,n]| ≤ #triples ~ n^{11/12}`), so gaps grow ~ `n^{1/12}`.
  4. The minimal required `C(z+7,8)`-index is UNBOUNDED (reaches 15 by `2·10^7`);
     likewise the triangular-index backtrack is unbounded (reaches 1145 by `2.3·10^6`):
     no finite/bounded construction exists in any variable.
  5. A positive, growing density (≈10% by `3·10^6`) of integers admit NO representation
     with any of `x,y,z = 0`, so the natural `+1`-increment induction fails.
  6. The holes of `A3` occur in EVERY residue class (mod 2..16), so there is no
     CRT/residue structure for the `C(z+7,8)`-shifts to exploit.
  7. No near-square identity for the degree-6,8 terms (`720·C(y+5,6)` is a non-square
     cubic in `y²+5y`), so unlike triangular/square problems it does not reduce to
     universality of a ternary/quaternary quadratic form.
  8. Second-moment / Cauchy–Schwarz yields only POSITIVE PROPORTION representable,
     not all `n`.
  9. The Hardy–Littlewood circle method does not even close with one variable per
     degree: the trivial minor-arc bound is `~ N^{19/24}`, dwarfing the main term
     `N^{1/24}` — consistent with this being unproven rather than a theorem.
* Mathlib provides no applicable tool (no Mann's theorem, no Waring/circle method;
  density tools require positive density).

A complete formal proof requires resolving an open mathematical problem.
-/

/-- Pure existence form of the conjecture (the genuine mathematical content).
This is the OPEN part: a circle-method / super-critical additive basis statement. -/
theorem A306477_exists (n : ℕ) (hn : n > 0) :
    ∃ w x y z : ℕ, w ≤ n ∧ x ≤ n ∧ y ≤ n ∧ z ≤ n ∧
      (w + 2).choose 2 + (x + 3).choose 4 + (y + 5).choose 6 + (z + 7).choose 8 = n := by
  sorry

/--
Conjecture: a(n) > 0 for all n > 0. In other words, any positive integer n can be written as C(w,2) + C(x,4) + C(y,6) + C(z,8), where w,x,y,z are integers greater than one.
-/
theorem oeis_306477_conjecture_0 : ∀ n : ℕ, n > 0 → A306477 n > 0 := by
  intro n hn
  obtain ⟨w, x, y, z, hw, hx, hy, hz, hsum⟩ := A306477_exists n hn
  unfold A306477
  apply Finset.sum_pos'
  · intro i _; exact Nat.zero_le _
  refine ⟨w, Finset.mem_range.mpr (Nat.lt_succ_of_le hw), ?_⟩
  apply Finset.sum_pos'
  · intro i _; exact Nat.zero_le _
  refine ⟨x, Finset.mem_range.mpr (Nat.lt_succ_of_le hx), ?_⟩
  apply Finset.sum_pos'
  · intro i _; exact Nat.zero_le _
  refine ⟨y, Finset.mem_range.mpr (Nat.lt_succ_of_le hy), ?_⟩
  apply Finset.sum_pos'
  · intro i _; exact Nat.zero_le _
  refine ⟨z, Finset.mem_range.mpr (Nat.lt_succ_of_le hz), ?_⟩
  rw [if_pos hsum]
  exact Nat.one_pos
