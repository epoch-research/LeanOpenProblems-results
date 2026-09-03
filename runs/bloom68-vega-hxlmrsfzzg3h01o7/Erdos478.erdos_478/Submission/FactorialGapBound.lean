import Submission.FactorialTwistReflection
import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# Finite gap bounds for twisted factorials

For nonzero `c : ZMod p`, with `p` prime, at most `d` indices in `range (p - d)`
satisfy `twist c (n + d) = twist c n`, for every positive natural gap `d`.
The index zero is included. No hypothesis `d < p` is needed: the index set is
empty when `p ≤ d`.

The proof uses the degree-`d` polynomial
`c^d * (X + 1) * ... * (X + d) - 1`, expressed using `ascPochhammer`.
Translation then gives the same collision bound on every interval contained
in `range p`.

These are finite auxiliary bounds only; no asymptotic or target settlement is
asserted here.
-/

open Finset Polynomial FactorialTwistReflection

noncomputable section

namespace FactorialGapBound

variable {p : ℕ}

/-- Starting indices of gap-`d` collisions, including the possible index zero. -/
def gapSet (c : ZMod p) (d : ℕ) : Finset ℕ :=
  (range (p - d)).filter fun n => twist c (n + d) = twist c n

@[simp] theorem mem_gapSet {c : ZMod p} {d n : ℕ} :
    n ∈ gapSet c d ↔ n < p - d ∧ twist c (n + d) = twist c n := by
  simp only [gapSet, mem_filter, mem_range]

/-- Gaps at least the modulus have no admissible starting indices. -/
theorem gapSet_eq_empty_of_le (c : ZMod p) {d : ℕ} (hpd : p ≤ d) :
    gapSet c d = ∅ := by
  simp [gapSet, Nat.sub_eq_zero_of_le hpd]

/-- A shifted rising-factorial polynomial whose roots encode gap collisions. -/
def gapPolynomial (c : ZMod p) (d : ℕ) : Polynomial (ZMod p) :=
  C (c ^ d) * (ascPochhammer (ZMod p) d).comp (X + 1) - 1

@[simp] theorem eval_gapPolynomial (c x : ZMod p) (d : ℕ) :
    (gapPolynomial c d).eval x =
      c ^ d * (ascPochhammer (ZMod p) d).eval (x + 1) - 1 := by
  simp only [gapPolynomial, eval_sub, eval_mul, eval_C, eval_comp,
    eval_add, eval_X, eval_one]

/-- The factorial quotient identity, with no positive-index restriction. -/
theorem twist_add (c : ZMod p) (n d : ℕ) :
    twist c (n + d) =
      twist c n * (c ^ d * (ascPochhammer (ZMod p) d).eval ((n : ZMod p) + 1)) := by
  unfold twist
  rw [pow_add, ← factorial_mul_ascPochhammer (ZMod p) n d]
  ring

/-- Local starting offsets for gap collisions inside `[start, start + N)`. -/
def localGapSet (c : ZMod p) (start N d : ℕ) : Finset ℕ :=
  (range N).filter fun n => n + d < N ∧
    twist c (start + n + d) = twist c (start + n)

@[simp] theorem mem_localGapSet {c : ZMod p} {start N d n : ℕ} :
    n ∈ localGapSet c start N d ↔ n < N ∧ n + d < N ∧
      twist c (start + n + d) = twist c (start + n) := by
  simp only [localGapSet, mem_filter, mem_range]

/-- Translating a local collision gives a collision in the full gap set. -/
theorem localGapSet_image_subset (c : ZMod p) {start N d : ℕ}
    (hN : start + N ≤ p) :
    (localGapSet c start N d).image (fun n => start + n) ⊆ gapSet c d := by
  intro m hm
  obtain ⟨n, hn, rfl⟩ := mem_image.mp hm
  obtain ⟨_, hnd, heq⟩ := mem_localGapSet.mp hn
  exact mem_gapSet.mpr ⟨by omega, heq⟩

variable [Fact p.Prime]

/-- Subtracting a constant does not change the natural degree. -/
theorem natDegree_gapPolynomial {c : ZMod p} (hc : c ≠ 0) (d : ℕ) :
    (gapPolynomial c d).natDegree = d := by
  simp only [gapPolynomial, ← C_1, natDegree_sub_C,
    natDegree_C_mul (pow_ne_zero d hc), natDegree_comp, ascPochhammer_natDegree,
    natDegree_X_add_C, Nat.mul_one]

/-- Positive gaps give a nonzero polynomial, even when `p ≤ d`. -/
theorem gapPolynomial_ne_zero {c : ZMod p} (hc : c ≠ 0) {d : ℕ} (hd : 0 < d) :
    gapPolynomial c d ≠ 0 := by
  apply ne_zero_of_natDegree_gt
  simpa only [natDegree_gapPolynomial hc] using hd

/-- The root/collision equivalence is valid at every `n < p`, including zero. -/
theorem gapPolynomial_isRoot_iff {c : ZMod p} (hc : c ≠ 0) {d n : ℕ} (hn : n < p) :
    (gapPolynomial c d).IsRoot (n : ZMod p) ↔ twist c (n + d) = twist c n := by
  rw [IsRoot.def, eval_gapPolynomial, sub_eq_zero, twist_add,
    mul_eq_left₀ (twist_ne_zero hc hn)]

/-- At most `d` full-domain collisions occur at any positive gap `d`.
There is no restriction `d < p` and no exclusion of the index zero. -/
theorem gapSet_card_le {c : ZMod p} (hc : c ≠ 0) {d : ℕ} (hd : 0 < d) :
    (gapSet c d).card ≤ d := by
  classical
  calc
    (gapSet c d).card ≤ (gapPolynomial c d).roots.toFinset.card := by
      apply card_le_card_of_injOn (fun n : ℕ => (n : ZMod p))
      · intro n hn
        obtain ⟨hn_bound, hn_eq⟩ := mem_gapSet.mp hn
        apply Multiset.mem_toFinset.mpr
        apply (Polynomial.mem_roots (gapPolynomial_ne_zero hc hd)).mpr
        exact (gapPolynomial_isRoot_iff hc (by omega)).mpr hn_eq
      · intro m hm n hn hmn
        have hm_lt : m < p := by
          have := (mem_gapSet.mp hm).1
          omega
        have hn_lt : n < p := by
          have := (mem_gapSet.mp hn).1
          omega
        have hval := congrArg ZMod.val hmn
        simpa only [ZMod.val_natCast_of_lt hm_lt, ZMod.val_natCast_of_lt hn_lt] using hval
    _ ≤ (gapPolynomial c d).roots.card := Multiset.toFinset_card_le _
    _ ≤ (gapPolynomial c d).natDegree := Polynomial.card_roots' _
    _ = d := natDegree_gapPolynomial hc d

/-- The full-domain bound is inherited by every subset of the gap set. -/
theorem card_le_of_subset_gapSet {c : ZMod p} (hc : c ≠ 0) {d : ℕ} (hd : 0 < d)
    {s : Finset ℕ} (hs : s ⊆ gapSet c d) : s.card ≤ d :=
  (card_le_card hs).trans (gapSet_card_le hc hd)

/-- At most `d` gap collisions occur within any interval contained in `range p`. -/
theorem localGapSet_card_le {c : ZMod p} (hc : c ≠ 0) {start N d : ℕ}
    (hN : start + N ≤ p) (hd : 0 < d) :
    (localGapSet c start N d).card ≤ d := by
  have hinj : Function.Injective (fun n : ℕ => start + n) :=
    fun _ _ h => Nat.add_left_cancel h
  calc
    (localGapSet c start N d).card =
        ((localGapSet c start N d).image (fun n => start + n)).card :=
      (card_image_of_injective _ hinj).symm
    _ ≤ d := card_le_of_subset_gapSet hc hd (localGapSet_image_subset c hN)

/-- The local collision bound stated directly as a filtered range. -/
theorem local_collision_count_le {c : ZMod p} (hc : c ≠ 0) {start N d : ℕ}
    (hN : start + N ≤ p) (hd : 0 < d) :
    ((range N).filter fun n => n + d < N ∧
      twist c (start + n + d) = twist c (start + n)).card ≤ d :=
  localGapSet_card_le hc hN hd

end FactorialGapBound
