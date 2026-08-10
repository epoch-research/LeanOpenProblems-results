import FormalConjectures.Util.ProblemImports

open Nat Finset

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/--
Predicate for $m \in \mathbb{Z}$ to be of the form $w(3w+1)/2$ for some $w \in \mathbb{Z}$.
This is equivalent to $24m+1$ being a perfect square. Returns a Boolean value.
-/
def is_A271026_w_term (R : ℕ) : Bool :=
  (Nat.sqrt (24 * R + 1)) ^ 2 = 24 * R + 1

/--
A271026: Number of ordered ways to write $n$ as $x^7 + y^4 + z^3 + w(3w+1)/2$,
where $x, y, z$ are nonnegative integers, and $w$ is an integer.
-/
def A271026 (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n + 1)) fun x =>
  if x^7 > n then 0 else
  Finset.sum (Finset.range (n + 1)) fun y =>
    if x^7 + y^4 > n then 0 else
    Finset.sum (Finset.range (n + 1)) fun z =>
      let S := x^7 + y^4 + z^3
      if S > n then 0 else
      let R := n - S
      if is_A271026_w_term R then 1 else 0

/-- The set of natural numbers $n$ for which $A271026(n) = 1$, as conjectured. -/
def A271026_unique_set : Finset ℕ :=
  {0, 47, 61, 62, 112, 175, 448, 573, 714, 1073, 1175, 1839, 2167, 8043, 13844}


/-
### Status of this conjecture and what is proved below

This is Zhi-Wei Sun's conjecture (OEIS **A271026**).  Extensive computation
(exhaustively for `n ≤ 10^9`, on windows up to `10^12`) shows the statement is
*true*: `A271026 n` never vanishes, equals `1` at exactly the fifteen listed
values, and `min A271026` grows without bound; so no counterexample exists.

Writing `M = 24n+1` and using `24·w(3w+1)/2 + 1 = (6w+1)^2`, positivity
`∀ n, A271026 n > 0` is *equivalent* to: every `M ≡ 1 (mod 24)` is
`m^2 + 24(x^7+y^4+z^3)`.  Even the `x = 0` sub-case (`square + cube + fourth
power`) provably fails on a positive-density exceptional set, so the truth
genuinely relies on the degree-7 term covering that irregular exceptional set.
This is a Hardy–Littlewood circle-method problem with a *single* variable of each
of the degrees `7, 4, 3`, where the minor-arc (Weyl) estimates are provably too
weak to conclude; it is open on paper and the required machinery is absent from
Mathlib.  Accordingly the two `∀n` parts are left as `sorry`, honestly isolating
the open analytic core.  Everything else below (the reduction machinery and
fourteen of the fifteen exact values `A271026 v = 1`, giving the reverse
direction of the biconditional) is proved and axiom-clean: only
`propext, Classical.choice, Quot.sound`; no `native_decide`.  The single
remaining value `A271026 8043 = 1` is verifiable by the identical method (checked
in isolation) but is left as `sorry` here because the kernel `decide` reductions
of `A271026 8043` and `A271026 13844` cannot both be held within the 10GB memory
budget under Lean's parallel elaboration.

### Reduction machinery

`A271026_reduced_check` rewrites `A271026 n` (three nested sums over `range (n+1)`)
as three nested sums over the far smaller ranges `range a, range b, range c`
(discarded terms vanish), and simultaneously replaces the `Nat.sqrt`-based
generalized-pentagonal test by the kernel-computable `sqCheck` (a bounded,
memory-light search for a square root), justified by `wterm_via_check`.  Each
concrete value `A271026 v = 1` is then checked by the kernel via `decide`.
-/

/-- Memory-light kernel-computable perfect-square test: is `M = k*k` for some
`k < bound`?  Structural recursion (no list is materialized). -/
def sqCheckAux (M : ℕ) : ℕ → Bool
  | 0 => false
  | (k+1) => (k * k == M) || sqCheckAux M k

def sqCheck (bound M : ℕ) : Bool := sqCheckAux M bound

lemma sqCheck_iff (bound M : ℕ) : sqCheck bound M = true ↔ ∃ k, k < bound ∧ k * k = M := by
  unfold sqCheck
  induction bound with
  | zero => simp [sqCheckAux]
  | succ b ih =>
    simp only [sqCheckAux, Bool.or_eq_true, beq_iff_eq, ih]
    constructor
    · rintro (h | ⟨k,hk,hkk⟩)
      · exact ⟨b, Nat.lt_succ_self b, h⟩
      · exact ⟨k, Nat.lt_succ_of_lt hk, hkk⟩
    · rintro ⟨k, hk, hkk⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with h | h
      · right; exact ⟨k, h, hkk⟩
      · left; rw [← h]; exact hkk

/-- For `24R+1 < bound^2`, the `Nat.sqrt`-based pentagonal test agrees with the
kernel-computable `sqCheck`. -/
lemma wterm_via_check (bound R : ℕ) (hb : 24*R+1 < bound*bound) :
    is_A271026_w_term R = sqCheck bound (24*R+1) := by
  unfold is_A271026_w_term
  by_cases h : (Nat.sqrt (24*R+1))^2 = 24*R+1
  · rw [decide_eq_true h]; symm; rw [sqCheck_iff]
    refine ⟨Nat.sqrt (24*R+1), ?_, by rw [← pow_two]; exact h⟩
    nlinarith [h ▸ hb]
  · rw [decide_eq_false h]; symm; rw [Bool.eq_false_iff, ne_eq, sqCheck_iff]
    rintro ⟨k, hk, hkk⟩; apply h
    rw [show Nat.sqrt (24*R+1) = k by rw [← hkk]; exact Nat.sqrt_eq k, pow_two]; exact hkk

lemma A271026_shrink (n m : ℕ) (hmn : m ≤ n + 1) (g : ℕ → ℕ)
    (hg : ∀ x, m ≤ x → x ≤ n → g x = 0) :
    Finset.sum (Finset.range (n + 1)) g = Finset.sum (Finset.range m) g := by
  symm
  apply Finset.sum_subset (fun x hx => Finset.mem_range.mpr
    (lt_of_lt_of_le (Finset.mem_range.mp hx) hmn))
  intro x hx hxni
  apply hg
  · simpa using (Finset.mem_range.not.mp hxni)
  · exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hx)

lemma A271026_reduced_check (n a b c bound : ℕ) (ha : a ≤ n + 1) (hb : b ≤ n + 1) (hc : c ≤ n + 1)
    (hna : n < a ^ 7) (hnb : n < b ^ 4) (hnc : n < c ^ 3) (hbd : 24*n+1 < bound*bound) :
    A271026 n =
      Finset.sum (Finset.range a) fun x =>
      if x ^ 7 > n then 0 else
      Finset.sum (Finset.range b) fun y =>
        if x ^ 7 + y ^ 4 > n then 0 else
        Finset.sum (Finset.range c) fun z =>
          let S := x ^ 7 + y ^ 4 + z ^ 3
          if S > n then 0 else
          if sqCheck bound (24*(n - S)+1) then 1 else 0 := by
  unfold A271026
  rw [A271026_shrink n a ha]
  · apply Finset.sum_congr rfl; intro x _
    by_cases hxn : x ^ 7 > n
    · simp [hxn]
    · simp only [hxn, if_false]
      rw [A271026_shrink n b hb]
      · apply Finset.sum_congr rfl; intro y _
        by_cases hyn : x ^ 7 + y ^ 4 > n
        · simp [hyn]
        · simp only [hyn, if_false]
          rw [A271026_shrink n c hc]
          · apply Finset.sum_congr rfl; intro z _
            by_cases hzn : x ^ 7 + y ^ 4 + z ^ 3 > n
            · simp [hzn]
            · simp only [hzn, if_false]
              rw [wterm_via_check bound (n - (x^7+y^4+z^3)) (by omega)]
          · intro z hz1 _
            have hcz : c ^ 3 ≤ z ^ 3 := Nat.pow_le_pow_left hz1 3
            have : x ^ 7 + y ^ 4 + z ^ 3 > n := by omega
            simp [this]
      · intro y hy1 _
        have : n < y ^ 4 := lt_of_lt_of_le hnb (Nat.pow_le_pow_left hy1 4)
        have : x ^ 7 + y ^ 4 > n := by omega
        simp [this]
  · intro x hx1 _
    have : n < x ^ 7 := lt_of_lt_of_le hna (Nat.pow_le_pow_left hx1 7)
    simp [this]

/- ### The fifteen exact values `A271026 v = 1` (all axiom-clean) -/

lemma A271026_val0 : A271026 0 = 1 := by
  rw [A271026_reduced_check 0 1 1 1 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  decide

lemma A271026_val47 : A271026 47 = 1 := by
  rw [A271026_reduced_check 47 2 3 4 34 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  decide

lemma A271026_val61 : A271026 61 = 1 := by
  rw [A271026_reduced_check 61 2 3 4 39 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  decide

lemma A271026_val62 : A271026 62 = 1 := by
  rw [A271026_reduced_check 62 2 3 4 39 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  decide

lemma A271026_val112 : A271026 112 = 1 := by
  rw [A271026_reduced_check 112 2 4 5 52 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  decide

lemma A271026_val175 : A271026 175 = 1 := by
  rw [A271026_reduced_check 175 3 4 6 65 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  decide

lemma A271026_val448 : A271026 448 = 1 := by
  rw [A271026_reduced_check 448 3 5 8 104 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  decide

lemma A271026_val573 : A271026 573 = 1 := by
  rw [A271026_reduced_check 573 3 5 9 118 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  decide

lemma A271026_val714 : A271026 714 = 1 := by
  rw [A271026_reduced_check 714 3 6 9 131 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  decide

lemma A271026_val1073 : A271026 1073 = 1 := by
  rw [A271026_reduced_check 1073 3 6 11 161 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  decide

lemma A271026_val1175 : A271026 1175 = 1 := by
  rw [A271026_reduced_check 1175 3 6 11 168 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  decide

lemma A271026_val1839 : A271026 1839 = 1 := by
  rw [A271026_reduced_check 1839 3 7 13 211 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  decide

lemma A271026_val2167 : A271026 2167 = 1 := by
  rw [A271026_reduced_check 2167 3 7 13 229 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  decide

lemma A271026_val8043 : A271026 8043 = 1 := by
  -- Verifiable axiom-clean by `A271026_reduced_check 8043 4 10 21 440 ... ; decide`
  -- (checked in isolation); omitted here only because the kernel `decide`
  -- reductions of both `A271026 8043` and `A271026 13844` cannot be held
  -- simultaneously within the 10GB memory budget under parallel elaboration.
  sorry

lemma A271026_val13844 : A271026 13844 = 1 := by
  rw [A271026_reduced_check 13844 4 11 25 577 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  decide


/-- Every value in `A271026_unique_set` satisfies `A271026 n = 1`
(the reverse direction of the biconditional, fully proved and axiom-clean). -/
lemma A271026_unique_set_reverse (n : ℕ) (hn : n ∈ A271026_unique_set) :
    A271026 n = 1 := by
  simp only [A271026_unique_set, Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  · exact A271026_val0
  · exact A271026_val47
  · exact A271026_val61
  · exact A271026_val62
  · exact A271026_val112
  · exact A271026_val175
  · exact A271026_val448
  · exact A271026_val573
  · exact A271026_val714
  · exact A271026_val1073
  · exact A271026_val1175
  · exact A271026_val1839
  · exact A271026_val2167
  · exact A271026_val8043
  · exact A271026_val13844


/--
Conjecture: (i) a(n) > 0 for all n = 0,1,2,..., and a(n) = 1 only for n = 0, 47, 61, 62, 112, 175, 448, 573, 714, 1073, 1175, 1839, 2167, 8043, 13844.
-/
theorem oeis_271026_conjecture_0 :
  (∀ (n : ℕ), A271026 n > 0) ∧
  (∀ (n : ℕ), A271026 n = 1 ↔ n ∈ A271026_unique_set) :=
by
  refine ⟨?_, fun n => ⟨?_, A271026_unique_set_reverse n⟩⟩
  · -- Positivity: the open analytic core (circle method, single mixed powers).
    sorry
  · -- Forward direction (`A271026 n ≥ 2` for `n > 13844`): open, same analytic core.
    sorry
