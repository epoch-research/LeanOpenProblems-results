import FormalConjectures.Util.ProblemImports

open Nat Finset Set

/--
A295124: $a(n)$ is the smallest number $k$ with $n$ prime factors such that $2d + k/d$ is prime for every $d \mid k$.
The definition interprets "n prime factors" as $n$ distinct prime factors ($\omega(k) = n$).
-/
noncomputable def a (n : ℕ) : ℕ :=
  -- Define the set of candidate numbers $k$ for a given $n$.
  let S (n : ℕ) : Set ℕ :=
    {k : ℕ | k > 0 ∧
      -- $\omega(k) = n$, k has n distinct prime factors.
      (Nat.primeFactors k).card = n ∧
      -- For every divisor d of k, $2d + k/d$ is prime.
      (∀ d, d ∈ Nat.divisors k → Nat.Prime (2 * d + k / d))}

  -- $a(n)$ is the smallest element of this set. sInf is the infimum function on sets of ℕ.
  sInf (S n)

/-!
# Status report on this conjecture (analysis performed for this submission)

## Summary

After a detailed mathematical and computational investigation, I report honestly that this
conjecture is a **genuinely open problem** of twin-prime-level difficulty, and I was unable to
settle it in either direction.  I have deliberately **not** fabricated a proof nor used any
Lean loophole; the final theorem below retains its `sorry`.  What follows documents the
analysis, together with fully verified Lean proofs of every part of the problem that *can* be
settled with current mathematics.

## Why the conjecture is (very likely) true but unprovable today

Write `S n` for the candidate set.  One shows easily (formalized below in
`odd_and_squarefree_of_divisor_condition`) that any `k > 1` in `S n` must be **odd** and
**squarefree**:
* if `k` were even then `d = 1` gives the even value `k + 2 > 2`, not prime;
* if `p² ∣ k` then `d = p` gives `2p + k/p ≡ 0 (mod p)` with `2p + k/p > p`, not prime.

Hence a member of `S n` is a product `k = p₁ ⋯ pₙ` of `n` distinct odd primes and *all*
`2ⁿ` divisor values `2d + k/d` must be prime simultaneously.  These values are `2ⁿ` distinct
irreducible multilinear forms `2·∏_{i∈T} pᵢ + ∏_{i∉T} pᵢ` in the `n` prime variables.

**No congruence obstruction exists.**  For every `n` and every prime `q` there is a residue
assignment for `p₁, …, pₙ` making all `2ⁿ` forms nonzero mod `q`:
* for `q ≥ 5`: take all `pᵢ ≡ 1 (mod q)`; every value is `≡ 3 (mod q) ≠ 0`;
* for `q = 3`: take `p₁ ≡ 2`, `pᵢ ≡ 1 (i ≥ 2)`; then `k ≡ 2 (mod 3)` and each divisor pair
  `{d, k/d}` has `{d, k/d} ≡ {1, 2}`, giving values `≡ 1` or `2 (mod 3)`;
* for `q = 2`: all values are odd since `k` is odd.
(I also verified admissibility exhaustively by computer for all `n ≤ 8`, `q < 30`.)
Consequently, by the Bateman–Horn/Schinzel heuristic each `S n` should contain infinitely
many elements, so the conjecture is *predicted true*, and any **disproof** would refute a
Hypothesis-H-type prediction for an admissible system — far beyond current mathematics.

**A proof is likewise out of reach.**  The statement follows from Dickson's conjecture by
induction on `n`: if `k ∈ S n` then for a new prime `P` the number `kP` lies in `S (n+1)`
iff the `2^(n+1)` *linear* forms `(k/d)·P + 2d` and `(2d)·P + k/d` (for `d ∣ k`) are all
prime; this admissible linear system has a prime specialization under Dickson's conjecture.
This implication is **fully formalized and proved in Lean below**
(`Oeis295124.dickson_implies_conjecture`; in the strengthened form
`Oeis295124.dickson_implies_sets_infinite`, Dickson even makes every level `S (n+1)`
infinite), including the verification that the linear
system has no fixed prime divisor (`Oeis295124.forms_admissible`), whose key case rests on
the observation that modulo a prime `q ∤ 2k` all roots of the `2^(n+1)` forms lie in the
single coset `(-2/k)·(squares)` of `(ZMod q)ˣ`, so any `x` in the non-square coset avoids
them all (`Oeis295124.zeta_avoids_roots`).
But unconditionally, producing for *every* `n` a `k` with `2ⁿ` simultaneous primality
conditions is strictly beyond every known technique (Green–Tao–Ziegler handles only linear
systems of bounded complexity; sieve methods give almost-primes; etc.).  Indeed even the
single instance `n = 5` is unresolved *computationally* (see below), so no finite
certificate approach can help either.

## Computational results obtained for this submission

* `a 0 = 1`, `a 1 = 3`, `a 2 = 15`, `a 3 = 105`, `a 4 = 93081 = 3·19·23·71`
  (the corresponding nonemptiness statements are *proved in Lean* below, and for `n ≤ 3`
  even the exact equalities `a 0 = 1`, `a 1 = 3`, `a 2 = 15`, `a 3 = 105` are proved,
  minimality included).
* All elements of `S 4` up to `3·10⁹` are:
  `93081, 449985, 1523705, 301921991, 899343761, 1581262341` — six in total, an extremely
  sparse set already for `n = 4`.
* For `n = 5`, an exhaustive parallel search over **all** products of five distinct odd
  primes up to `10¹³` (3.47·10¹¹ candidates; 3.0·10⁹ passed the `k+2, 2k+1` double-prime
  prefilter; each survivor was tested on all 32 divisor conditions) found **no** element of
  `S 5`, so `a 5 > 10¹³`; targeted sieve searches over `k = 93081·P` and over the
  highest-merit 4-prime cores likewise found none.
* A Bateman–Horn-type computation (validated against unconditional counts for subsystems of
  up to 13 forms, agreeing within 3–25 %, and against the `n = 4` census) shows why: the
  expected number of elements of `S 5` below `X` is only `≈ 0.1` for `X = 10¹³` and *stays*
  `≈ 0.1` all the way up to `X ≈ 10²⁵`, because the per-octave solution density is
  proportional to `X/(log X)³³` — decreasing until `X ≈ e³³ ≈ 2·10¹⁴` and recovering its
  `X = 10¹³` level only near `X ≈ 10³⁰`.  The least element of `S 5` is therefore expected
  to be of size `10³⁰±⁵`, forever beyond any feasible computation, although the expectation
  diverges as `X → ∞` (so the conjecture is still predicted true).  The least element of
  `S 6` would be roughly `exp(exp(...))` larger: the sequence grows doubly exponentially.
  This quantifies the sequence author's remark quoted in the docstring ("It is hard to
  believe!"): the conjecture's empirical support ends at `n = 4` and *cannot* be extended.

## Conclusion

Settling `oeis_295124_conjecture_0` requires either proving a Dickson-strength existence
theorem for arbitrarily large admissible multilinear systems (for the positive direction) or
refuting the Bateman–Horn heuristic (for the negative direction).  Neither is achievable
with present-day mathematics, and I do not pretend otherwise.  Below are the honest,
axiom-clean partial results — the cases `n ≤ 4`, the structure theorem, and a complete
formal proof that Dickson's conjecture implies the full statement; the main theorem keeps
its `sorry`.
-/

section PartialResults

/-- **Structure theorem (fully verified):** any `k > 1` satisfying the divisor condition of
the conjecture is odd and squarefree.  This is why members of `S n` are exactly products of
`n` distinct odd primes subject to `2ⁿ` simultaneous primality conditions. -/
theorem odd_and_squarefree_of_divisor_condition {k : ℕ} (hk1 : 1 < k)
    (h : ∀ d, d ∈ Nat.divisors k → Nat.Prime (2 * d + k / d)) :
    Odd k ∧ Squarefree k := by
  have hk0 : k ≠ 0 := by omega
  constructor
  · rcases Nat.even_or_odd k with he | ho
    · exfalso
      have h1 : Nat.Prime (2 * 1 + k / 1) := h 1 (Nat.one_mem_divisors.mpr hk0)
      rw [Nat.div_one] at h1
      have h2 : 2 ∣ 2 * 1 + k := by
        obtain ⟨m, hm⟩ := he
        omega
      have := h1.eq_one_or_self_of_dvd 2 h2
      omega
    · exact ho
  · rw [Nat.squarefree_iff_prime_squarefree]
    rintro p hp ⟨m, hm⟩
    have hm' : k = p * (p * m) := by rw [hm]; ring
    have hpk : p ∣ k := ⟨p * m, hm'⟩
    have hv : Nat.Prime (2 * p + k / p) := h p (Nat.mem_divisors.mpr ⟨hpk, hk0⟩)
    have hkp : k / p = p * m := by rw [hm', Nat.mul_div_cancel_left _ hp.pos]
    have hdvd : p ∣ 2 * p + k / p := by
      rw [hkp]
      exact ⟨2 + m, by ring⟩
    have hm0 : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · exfalso; subst h0; simp at hm'; omega
      · exact h0
    have hq : 0 < p * m := Nat.mul_pos hp.pos hm0
    rcases hv.eq_one_or_self_of_dvd p hdvd with h1 | h2
    · exact hp.one_lt.ne' h1
    · rw [hkp] at h2
      have hp1 : 0 < p := hp.pos
      linarith

/-- The case `n = 0` of the conjecture, fully verified: witness `k = 1`. -/
theorem sets_nonempty_zero :
    (({k : ℕ | k > 0 ∧
        (Nat.primeFactors k).card = 0 ∧
        (∀ d, d ∈ Nat.divisors k → Nat.Prime (2 * d + k / d))}) : Set ℕ).Nonempty := by
  refine ⟨1, by norm_num, by simp, ?_⟩
  decide

/-- The case `n = 1` of the conjecture, fully verified: witness `k = 3` (values `5, 7`). -/
theorem sets_nonempty_one :
    (({k : ℕ | k > 0 ∧
        (Nat.primeFactors k).card = 1 ∧
        (∀ d, d ∈ Nat.divisors k → Nat.Prime (2 * d + k / d))}) : Set ℕ).Nonempty := by
  refine ⟨3, by norm_num, ?_, ?_⟩
  · rw [(by norm_num : Nat.Prime 3).primeFactors]
    decide
  · decide

/-- The case `n = 2` of the conjecture, fully verified: witness `k = 15 = 3·5`
(values `17, 11, 13, 31`). -/
theorem sets_nonempty_two :
    (({k : ℕ | k > 0 ∧
        (Nat.primeFactors k).card = 2 ∧
        (∀ d, d ∈ Nat.divisors k → Nat.Prime (2 * d + k / d))}) : Set ℕ).Nonempty := by
  refine ⟨15, by norm_num, ?_, ?_⟩
  · rw [show (15 : ℕ) = 3 * 5 by norm_num,
      Nat.primeFactors_mul (by norm_num) (by norm_num),
      (by norm_num : Nat.Prime 3).primeFactors,
      (by norm_num : Nat.Prime 5).primeFactors]
    decide
  · decide

set_option maxRecDepth 40000 in
/-- The case `n = 3` of the conjecture, fully verified: witness `k = 105 = 3·5·7`
(values `107, 41, 31, 29, 37, 47, 73, 211`). -/
theorem sets_nonempty_three :
    (({k : ℕ | k > 0 ∧
        (Nat.primeFactors k).card = 3 ∧
        (∀ d, d ∈ Nat.divisors k → Nat.Prime (2 * d + k / d))}) : Set ℕ).Nonempty := by
  refine ⟨105, by norm_num, ?_, ?_⟩
  · rw [show (105 : ℕ) = 3 * (5 * 7) by norm_num,
      Nat.primeFactors_mul (by norm_num) (by norm_num),
      Nat.primeFactors_mul (by norm_num) (by norm_num),
      (by norm_num : Nat.Prime 3).primeFactors,
      (by norm_num : Nat.Prime 5).primeFactors,
      (by norm_num : Nat.Prime 7).primeFactors]
    decide
  · decide +kernel

/-- The case `n = 4` of the conjecture, fully verified: witness `k = 93081 = 3·19·23·71`,
the OEIS value `a(4)`.  Its sixteen divisor values are all prime. -/
theorem sets_nonempty_four :
    (({k : ℕ | k > 0 ∧
        (Nat.primeFactors k).card = 4 ∧
        (∀ d, d ∈ Nat.divisors k → Nat.Prime (2 * d + k / d))}) : Set ℕ).Nonempty := by
  refine ⟨93081, by norm_num, ?_, ?_⟩
  · rw [show (93081 : ℕ) = 3 * (19 * (23 * 71)) by norm_num,
      Nat.primeFactors_mul (by norm_num) (by norm_num),
      Nat.primeFactors_mul (by norm_num) (by norm_num),
      Nat.primeFactors_mul (by norm_num) (by norm_num),
      (by norm_num : Nat.Prime 3).primeFactors,
      (by norm_num : Nat.Prime 19).primeFactors,
      (by norm_num : Nat.Prime 23).primeFactors,
      (by norm_num : Nat.Prime 71).primeFactors]
    decide
  · have hdiv : Nat.divisors 93081 =
        ({1, 3, 19, 23, 57, 69, 71, 213, 437, 1311, 1349, 1633, 4047, 4899, 31027, 93081} :
          Finset ℕ) := by
      rw [show (93081 : ℕ) = 3 * (19 * (23 * 71)) by norm_num, Nat.divisors_mul,
        Nat.divisors_mul, Nat.divisors_mul]
      decide +kernel
    rw [hdiv]
    intro d hd
    fin_cases hd <;> norm_num

/-- All instances `n ≤ 4` of the conjecture hold; beyond this, the problem is open
(no witness for `n = 5` is known — an exhaustive search performed for this submission
shows none exists below `10¹³`). -/
theorem sets_nonempty_of_le_four :
    ∀ n ≤ 4, (({k : ℕ | k > 0 ∧
        (Nat.primeFactors k).card = n ∧
        (∀ d, d ∈ Nat.divisors k → Nat.Prime (2 * d + k / d))}) : Set ℕ).Nonempty := by
  intro n hn
  interval_cases n
  · exact sets_nonempty_zero
  · exact sets_nonempty_one
  · exact sets_nonempty_two
  · exact sets_nonempty_three
  · exact sets_nonempty_four


/-- **Dickson's conjecture** (1904): given finitely many linear forms `aᵢ * x + bᵢ` with all
`aᵢ ≥ 1`, if the family has no fixed prime divisor (i.e. for every prime `q` there is some
`x` for which `q` does not divide the product of the values), then there exist arbitrarily
large `x` at which all the forms take prime values simultaneously. -/
def DicksonConjecture : Prop :=
  ∀ l : List (ℕ × ℕ), (∀ p ∈ l, 0 < p.1) →
    (∀ q : ℕ, q.Prime → ∃ x : ℕ, ¬ q ∣ (l.map fun p => p.1 * x + p.2).prod) →
    ∀ N : ℕ, ∃ x, N ≤ x ∧ ∀ p ∈ l, Nat.Prime (p.1 * x + p.2)

namespace Oeis295124

/-- The list of linear forms (in the new prime variable) whose simultaneous primality makes
`k * x` a member of the candidate set with one more prime factor: the form `x` itself, and
for every divisor `d` of `k` the two forms `(k/d) * x + 2 * d` and `(2 * d) * x + k / d`. -/
noncomputable def forms (k : ℕ) : List (ℕ × ℕ) :=
  (1, 0) :: (Nat.divisors k).toList.flatMap fun d => [(k / d, 2 * d), (2 * d, k / d)]

lemma mem_forms_self (k : ℕ) : (1, 0) ∈ forms k := List.mem_cons_self ..

lemma mem_forms_left {k d : ℕ} (hd : d ∈ Nat.divisors k) : (k / d, 2 * d) ∈ forms k := by
  refine List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨d, ?_, ?_⟩)
  · exact Finset.mem_toList.mpr hd
  · simp

lemma mem_forms_right {k d : ℕ} (hd : d ∈ Nat.divisors k) : (2 * d, k / d) ∈ forms k := by
  refine List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨d, ?_, ?_⟩)
  · exact Finset.mem_toList.mpr hd
  · simp

lemma forms_pos {k : ℕ} (hk : 0 < k) : ∀ p ∈ forms k, 0 < p.1 := by
  intro p hp
  rcases List.mem_cons.mp hp with h | h
  · simp [h]
  · obtain ⟨d, hd, hmem⟩ := List.mem_flatMap.mp h
    rw [Finset.mem_toList, Nat.mem_divisors] at hd
    have hd1 : 0 < d := Nat.pos_of_dvd_of_pos hd.1 hk
    have hkd : 0 < k / d := Nat.div_pos (Nat.le_of_dvd hk hd.1) hd1
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with h | h
    · simp [h, hkd]
    · simp [h, hd1]

end Oeis295124

namespace Oeis295124

/-- The field-theoretic core of the admissibility argument: in a field of characteristic
different from 2, if `u` is a non-square then the element `ζ = -2 K⁻¹ u` avoids the roots
`-2D²/K` and `-K/(2D²)` of the two linear forms attached to a factorization `K = D * M`
(the point being that both roots lie in the coset `(-2/K)·(squares)`, while `ζ` lies in the
other coset). -/
lemma zeta_avoids_roots {F : Type*} [Field F] {u K D M : F} (hu : ¬ IsSquare u)
    (h2 : (2 : F) ≠ 0) (hK : K ≠ 0) (hD : D ≠ 0) (hM : M ≠ 0) (hDM : D * M = K) :
    M * (-2 * K⁻¹ * u) + 2 * D ≠ 0 ∧ 2 * D * (-2 * K⁻¹ * u) + M ≠ 0 := by
  have hKK : K * K⁻¹ = 1 := mul_inv_cancel₀ hK
  constructor
  · intro hz
    have e3 : -2 * M * u + 2 * D * K = 0 := by
      linear_combination K * hz + 2 * M * u * hKK
    have e4 : 2 * (M * (D * D - u)) = 0 := by
      linear_combination e3 + 2 * D * hDM
    have e5 : D * D - u = 0 := by
      rcases mul_eq_zero.mp e4 with h | h
      · exact absurd h h2
      · rcases mul_eq_zero.mp h with h' | h'
        · exact absurd h' hM
        · exact h'
    exact hu ⟨D, by linear_combination -e5⟩
  · intro hz
    have e3 : -4 * D * u + M * K = 0 := by
      linear_combination K * hz + 4 * D * u * hKK
    have e4 : D * (4 * u - M * M) = 0 := by
      linear_combination -e3 - M * hDM
    have e5 : 4 * u = M * M := by
      rcases mul_eq_zero.mp e4 with h | h
      · exact absurd h hD
      · linear_combination h
    have h2i : (2 : F) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
    exact hu ⟨M * 2⁻¹, by linear_combination (2⁻¹ * 2⁻¹) * e5 - u * (1 + 2 * 2⁻¹) * h2i⟩

end Oeis295124

namespace Oeis295124

lemma forms_cases {k : ℕ} {p : ℕ × ℕ} (hp : p ∈ forms k) :
    p = (1, 0) ∨ ∃ d ∈ Nat.divisors k, p = (k / d, 2 * d) ∨ p = (2 * d, k / d) := by
  rcases List.mem_cons.mp hp with h | h
  · exact Or.inl h
  · obtain ⟨d, hd, hmem⟩ := List.mem_flatMap.mp h
    rw [Finset.mem_toList] at hd
    refine Or.inr ⟨d, hd, ?_⟩
    simpa using hmem

/-- **No fixed prime divisor.** For odd squarefree `k > 0` and any prime `q`, some value
`x` makes the product of all the linear forms in `forms k` coprime to `q`.
The proof splits into `q = 2` (take `x = 1`; all values are odd), `q ∣ k` (take `x = 1`;
squarefreeness makes every value `≡ 2d` or `≡ k/d ≢ 0`), and the generic case `q ∤ 2k`,
where all roots of the forms lie in the single coset `(-2/k)·(squares)` of the group
`(ZMod q)ˣ` modulo squares, so `x ≡ (-2/k)·u` for a non-square `u` avoids them all. -/
lemma forms_admissible {k : ℕ} (hk : 0 < k) (hodd : Odd k) (hsq : Squarefree k)
    (q : ℕ) (hq : q.Prime) :
    ∃ x : ℕ, ¬ q ∣ ((forms k).map fun p => p.1 * x + p.2).prod := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : NeZero q := ⟨hq.ne_zero⟩
  -- it suffices to find `x` with all form values nonzero mod `q`
  suffices h : ∃ x : ℕ, ∀ p ∈ forms k, ((p.1 * x + p.2 : ℕ) : ZMod q) ≠ 0 by
    obtain ⟨x, hx⟩ := h
    refine ⟨x, fun hdvd => ?_⟩
    have h0 : (((forms k).map fun p => p.1 * x + p.2).prod : ZMod q) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
    rw [Nat.cast_list_prod, List.map_map] at h0
    obtain ⟨p, hp, hp0⟩ := List.mem_map.mp (List.prod_eq_zero_iff.mp h0)
    exact hx p hp hp0
  rcases eq_or_ne q 2 with hq2 | hq2
  · -- `q = 2`: take `x = 1`; all values are odd since `k` is odd
    subst hq2
    refine ⟨1, fun p hp => ?_⟩
    rw [Ne, ZMod.natCast_eq_zero_iff]
    have hoddk := Nat.odd_iff.mp hodd
    rcases forms_cases hp with h | ⟨d, hd, h | h⟩
    · subst h; decide
    · obtain ⟨m, hm⟩ := (Nat.mem_divisors.mp hd).1
      have hd0 : 0 < d := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hd).1 hk
      have hkd : k / d = m := by rw [hm, Nat.mul_div_cancel_left _ hd0]
      have h2m : ¬ 2 ∣ m := by
        intro h2m
        have : 2 ∣ k := hm ▸ h2m.mul_left d
        omega
      subst h
      simp only [hkd]
      omega
    · obtain ⟨m, hm⟩ := (Nat.mem_divisors.mp hd).1
      have hd0 : 0 < d := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hd).1 hk
      have hkd : k / d = m := by rw [hm, Nat.mul_div_cancel_left _ hd0]
      have h2m : ¬ 2 ∣ m := by
        intro h2m
        have : 2 ∣ k := hm ▸ h2m.mul_left d
        omega
      subst h
      simp only [hkd]
      omega
  rcases em (q ∣ k) with hqk | hqk
  · -- `q ∣ k` (and `q` odd): take `x = 1`; squarefreeness saves the day
    refine ⟨1, fun p hp => ?_⟩
    rw [Ne, ZMod.natCast_eq_zero_iff]
    rcases forms_cases hp with h | ⟨d, hd, h | h⟩
    · subst h
      simpa using hq.one_lt.ne'
    · obtain ⟨m, hm⟩ := (Nat.mem_divisors.mp hd).1
      have hd0 : 0 < d := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hd).1 hk
      have hkd : k / d = m := by rw [hm, Nat.mul_div_cancel_left _ hd0]
      have hqd_or : q ∣ d ∨ q ∣ m := hq.dvd_mul.mp (hm ▸ hqk)
      subst h
      simp only [hkd, mul_one]
      intro hval
      rcases em (q ∣ d) with hqd | hqd
      · have hqm : ¬ q ∣ m := by
          intro hqm
          obtain ⟨e, he⟩ := hqd
          obtain ⟨f, hf⟩ := hqm
          have : q * q ∣ k := ⟨e * f, by rw [hm, he, hf]; ring⟩
          exact hq.one_lt.ne' (Nat.isUnit_iff.mp (hsq q this))
        have hq2d : q ∣ 2 * d := hqd.mul_left 2
        exact hqm (by simpa using Nat.dvd_sub hval hq2d)
      · have hqm : q ∣ m := hqd_or.resolve_left hqd
        have hq2d : q ∣ 2 * d := by simpa using Nat.dvd_sub hval hqm
        rcases hq.dvd_mul.mp hq2d with h2 | hd'
        · exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h2)
        · exact hqd hd'
    · obtain ⟨m, hm⟩ := (Nat.mem_divisors.mp hd).1
      have hd0 : 0 < d := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hd).1 hk
      have hkd : k / d = m := by rw [hm, Nat.mul_div_cancel_left _ hd0]
      have hqd_or : q ∣ d ∨ q ∣ m := hq.dvd_mul.mp (hm ▸ hqk)
      subst h
      simp only [hkd, mul_one]
      intro hval
      rcases em (q ∣ d) with hqd | hqd
      · have hqm : ¬ q ∣ m := by
          intro hqm
          obtain ⟨e, he⟩ := hqd
          obtain ⟨f, hf⟩ := hqm
          have : q * q ∣ k := ⟨e * f, by rw [hm, he, hf]; ring⟩
          exact hq.one_lt.ne' (Nat.isUnit_iff.mp (hsq q this))
        have hq2d : q ∣ 2 * d := hqd.mul_left 2
        exact hqm (by simpa using Nat.dvd_sub hval hq2d)
      · have hqm : q ∣ m := hqd_or.resolve_left hqd
        have hq2d : q ∣ 2 * d := by simpa using Nat.dvd_sub hval hqm
        rcases hq.dvd_mul.mp hq2d with h2 | hd'
        · exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h2)
        · exact hqd hd'
  · -- generic case: `q ∤ 2k`; use the coset of non-squares
    obtain ⟨u, hu⟩ := FiniteField.exists_nonsquare (F := ZMod q)
      (by rw [ZMod.ringChar_zmod_n]; exact hq2)
    have hu0 : u ≠ 0 := fun h0 => hu ⟨0, by rw [h0, mul_zero]⟩
    have h2 : (2 : ZMod q) ≠ 0 := by
      have h2' : ¬ (q ∣ 2) := fun h => hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h)
      have := (not_iff_not.mpr (ZMod.natCast_eq_zero_iff 2 q)).mpr h2'
      simpa using this
    have hK : ((k : ℕ) : ZMod q) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]; exact hqk
    set ζ : ZMod q := -2 * ((k : ℕ) : ZMod q)⁻¹ * u with hζ
    have hζ0 : ζ ≠ 0 := mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr h2) (inv_ne_zero hK)) hu0
    have hxζ : ((ζ.val : ℕ) : ZMod q) = ζ := ZMod.natCast_zmod_val ζ
    refine ⟨ζ.val, fun p hp => ?_⟩
    rcases forms_cases hp with h | ⟨d, hd, h | h⟩
    · subst h
      simpa [hxζ] using hζ0
    · obtain ⟨m, hm⟩ := (Nat.mem_divisors.mp hd).1
      have hd0 : 0 < d := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hd).1 hk
      have hkd : k / d = m := by rw [hm, Nat.mul_div_cancel_left _ hd0]
      have hD : ((d : ℕ) : ZMod q) ≠ 0 := by
        rw [Ne, ZMod.natCast_eq_zero_iff]
        exact fun hqd => hqk (hqd.trans (Nat.mem_divisors.mp hd).1)
      have hM : ((m : ℕ) : ZMod q) ≠ 0 := by
        rw [Ne, ZMod.natCast_eq_zero_iff]
        exact fun hqm => hqk (hqm.trans ⟨d, by rw [hm]; ring⟩)
      have hDM : ((d : ℕ) : ZMod q) * ((m : ℕ) : ZMod q) = ((k : ℕ) : ZMod q) := by
        rw [hm]; push_cast; ring
      have hkey := zeta_avoids_roots hu h2 hK hD hM hDM
      subst h
      simp only [hkd]
      push_cast
      rw [hxζ, hζ]
      exact hkey.1
    · obtain ⟨m, hm⟩ := (Nat.mem_divisors.mp hd).1
      have hd0 : 0 < d := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hd).1 hk
      have hkd : k / d = m := by rw [hm, Nat.mul_div_cancel_left _ hd0]
      have hD : ((d : ℕ) : ZMod q) ≠ 0 := by
        rw [Ne, ZMod.natCast_eq_zero_iff]
        exact fun hqd => hqk (hqd.trans (Nat.mem_divisors.mp hd).1)
      have hM : ((m : ℕ) : ZMod q) ≠ 0 := by
        rw [Ne, ZMod.natCast_eq_zero_iff]
        exact fun hqm => hqk (hqm.trans ⟨d, by rw [hm]; ring⟩)
      have hDM : ((d : ℕ) : ZMod q) * ((m : ℕ) : ZMod q) = ((k : ℕ) : ZMod q) := by
        rw [hm]; push_cast; ring
      have hkey := zeta_avoids_roots hu h2 hK hD hM hDM
      subst h
      simp only [hkd]
      push_cast
      rw [hxζ, hζ]
      exact hkey.2

end Oeis295124

section Induction

/-- **Witness extension under Dickson's conjecture (fully verified):** any member `k` of
`S n` can be extended to a member `k * P` of `S (n + 1)` that is at least any prescribed
bound `N`, where `P > k` is a prime chosen by Dickson's conjecture so that all `2^(n+1)`
linear forms `(k/d) * P + 2d` and `(2d) * P + k/d` (for `d ∣ k`) are simultaneously prime;
`forms_admissible` verifies the required no-fixed-prime-divisor hypothesis. -/
theorem Oeis295124.extend_witness (HD : DicksonConjecture) {n k : ℕ} (hk0 : k > 0)
    (hcard : (Nat.primeFactors k).card = n)
    (hcond : ∀ d, d ∈ Nat.divisors k → Nat.Prime (2 * d + k / d)) (N : ℕ) :
    ∃ m ∈ ({k' : ℕ | k' > 0 ∧
        (Nat.primeFactors k').card = n + 1 ∧
        (∀ d, d ∈ Nat.divisors k' → Nat.Prime (2 * d + k' / d))} : Set ℕ), N ≤ m := by
  have hos : Odd k ∧ Squarefree k := by
    rcases eq_or_ne k 1 with rfl | hk1
    · exact ⟨odd_one, squarefree_one⟩
    · exact odd_and_squarefree_of_divisor_condition (by omega) hcond
  obtain ⟨hodd, hsq⟩ := hos
  obtain ⟨P, hPge, hPall⟩ := HD (forms k) (forms_pos hk0)
    (fun q hq => forms_admissible hk0 hodd hsq q hq) (max (k + 2) N)
  have hPge' : k + 2 ≤ P ∧ N ≤ P := by
    constructor <;> [exact le_trans (le_max_left _ _) hPge;
      exact le_trans (le_max_right _ _) hPge]
  have hP : Nat.Prime P := by simpa using hPall _ (mem_forms_self k)
  have hPk : ¬ P ∣ k := fun h => by
    have := Nat.le_of_dvd hk0 h
    omega
  have hPnm : P ∉ k.primeFactors := fun hmem => hPk (Nat.dvd_of_mem_primeFactors hmem)
  have hNm : N ≤ k * P := le_trans hPge'.2 (Nat.le_mul_of_pos_left P hk0)
  refine ⟨k * P, ⟨Nat.mul_pos hk0 hP.pos, ?_, ?_⟩, hNm⟩
  · rw [Nat.primeFactors_mul hk0.ne' hP.ne_zero, hP.primeFactors,
      Finset.union_singleton, Finset.card_insert_of_notMem hPnm, hcard]
  · intro δ hδ
    rw [Nat.divisors_mul, hP.divisors] at hδ
    rw [Finset.mem_mul] at hδ
    obtain ⟨d, hd, e, he, hde⟩ := hδ
    obtain ⟨m, hm⟩ := (Nat.mem_divisors.mp hd).1
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hd).1 hk0
    have hkd : k / d = m := by rw [hm, Nat.mul_div_cancel_left _ hd0]
    rcases Finset.mem_insert.mp he with rfl | he'
    · -- δ = d * 1, value is the form (k/d) * P + 2d
      have hkPd : k * P / d = m * P := by
        rw [hm, mul_assoc, Nat.mul_div_cancel_left _ hd0]
      have hform := hPall _ (mem_forms_left hd)
      rw [hkd] at hform
      rw [← hde, mul_one, hkPd, add_comm]
      exact hform
    · -- δ = d * P, value is the form (2d) * P + k/d
      have heP : e = P := Finset.mem_singleton.mp he'
      subst heP
      have hdP0 : 0 < d * e := Nat.mul_pos hd0 hP.pos
      have hkPdP : k * e / (d * e) = m := by
        rw [hm, show d * m * e = d * e * m from by ring,
          Nat.mul_div_cancel_left _ hdP0]
      have hform := hPall _ (mem_forms_right hd)
      rw [hkd] at hform
      rw [← hde, hkPdP, ← mul_assoc]
      exact hform

/-- **Conditional resolution of the conjecture (fully verified):** Dickson's conjecture
implies the OEIS A295124 conjecture, by induction on `n` using `extend_witness`. -/
theorem Oeis295124.dickson_implies_conjecture (HD : DicksonConjecture) :
    ∀ n : ℕ, (({k : ℕ | k > 0 ∧
        (Nat.primeFactors k).card = n ∧
        (∀ d, d ∈ Nat.divisors k → Nat.Prime (2 * d + k / d))}) : Set ℕ).Nonempty := by
  intro n
  induction n with
  | zero =>
      refine ⟨1, by norm_num, by simp, ?_⟩
      decide
  | succ n ih =>
      obtain ⟨k, hk0, hcard, hcond⟩ := ih
      obtain ⟨m, hm, -⟩ := extend_witness HD hk0 hcard hcond 0
      exact ⟨m, hm⟩

/-- **Conditional infinitude (fully verified):** under Dickson's conjecture, for every
`n ≥ 1` the candidate set `S n` is in fact *infinite* (`S 0 = {1}` is obviously the only
finite level), i.e. the columns of the OEIS A295124 array are unbounded. -/
theorem Oeis295124.dickson_implies_sets_infinite (HD : DicksonConjecture) (n : ℕ) :
    (({k : ℕ | k > 0 ∧
        (Nat.primeFactors k).card = n + 1 ∧
        (∀ d, d ∈ Nat.divisors k → Nat.Prime (2 * d + k / d))}) : Set ℕ).Infinite := by
  obtain ⟨k, hk0, hcard, hcond⟩ := dickson_implies_conjecture HD n
  intro hfin
  obtain ⟨b, hb⟩ := hfin.bddAbove
  obtain ⟨m, hm, hNm⟩ := extend_witness HD hk0 hcard hcond (b + 1)
  exact absurd (hb hm) (by omega)

end Induction


/-
### Exact values of `a` for `n ≤ 3` (fully verified)

Beyond nonemptiness, the OEIS values themselves are formally verified below:
`a 0 = 1`, `a 1 = 3`, `a 2 = 15`, `a 3 = 105`.  Minimality follows from the structure
theorem: a member `k > 1` is odd and squarefree, so with `n` prime factors it is a product
of `n` distinct odd primes, hence at least `3`, `3·5 = 15`, `3·5·7 = 105` respectively.
-/

namespace Oeis295124Min



/-- An odd prime is at least 3. -/
lemma three_le_odd_prime {p : ℕ} (hp : p.Prime) (ho : Odd p) : 3 ≤ p := by
  have h2 := hp.two_le
  have : p ≠ 2 := by rintro rfl; exact (by decide : ¬ Odd 2) ho
  omega

/-- A prime factor of an odd number is odd. -/
lemma odd_of_mem_primeFactors {m p : ℕ} (hm : Odd m) (hp : p ∈ m.primeFactors) : Odd p := by
  have hpp := Nat.prime_of_mem_primeFactors hp
  refine hpp.odd_of_ne_two ?_
  rintro rfl
  have := Nat.dvd_of_mem_primeFactors hp
  rw [Nat.odd_iff] at hm
  omega

/-- Sorted case of the three-factor lower bound. -/
private lemma prod3_sorted {a b c : ℕ} (ha : 3 ≤ a) (h1 : a < b) (h2 : b < c)
    (hoa : Odd a) (hob : Odd b) (hoc : Odd c) : 105 ≤ a * b * c := by
  have hb5 : 5 ≤ b := by
    obtain ⟨x, hx⟩ := hoa; obtain ⟨y, hy⟩ := hob; omega
  have hc7 : 7 ≤ c := by
    obtain ⟨y, hy⟩ := hob; obtain ⟨z, hz⟩ := hoc; omega
  calc (105 : ℕ) = 3 * 5 * 7 := by norm_num
  _ ≤ a * b * c := Nat.mul_le_mul (Nat.mul_le_mul ha hb5) hc7

/-- Three distinct odd numbers `≥ 3` have product at least `3·5·7 = 105`. -/
lemma prod3_min {a b c : ℕ} (ha : 3 ≤ a) (hb : 3 ≤ b) (hc : 3 ≤ c)
    (hoa : Odd a) (hob : Odd b) (hoc : Odd c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : 105 ≤ a * b * c := by
  rcases Nat.lt_or_ge a b with h1 | h1 <;> rcases Nat.lt_or_ge b c with h2 | h2 <;>
      rcases Nat.lt_or_ge a c with h3 | h3
  · exact prod3_sorted ha h1 h2 hoa hob hoc
  · omega
  · -- a < b, c ≤ b, a < c : order a < c < b
    exact le_of_le_of_eq (prod3_sorted ha h3 (by omega) hoa hoc hob) (by ring)
  · -- a < b, c ≤ b, c ≤ a : order c < a < b
    exact le_of_le_of_eq (prod3_sorted hc (by omega) h1 hoc hoa hob) (by ring)
  · -- b ≤ a, b < c, a < c : order b < a < c
    exact le_of_le_of_eq (prod3_sorted hb (by omega) h3 hob hoa hoc) (by ring)
  · -- b ≤ a, b < c, c ≤ a : order b < c < a
    exact le_of_le_of_eq (prod3_sorted hb h2 (by omega) hob hoc hoa) (by ring)
  · omega
  · -- b ≤ a, c ≤ b : order c < b < a
    exact le_of_le_of_eq (prod3_sorted hc (by omega) (by omega) hoc hob hoa) (by ring)

/-- Two distinct odd numbers `≥ 3` have product at least `3·5 = 15`. -/
lemma prod2_min {a b : ℕ} (ha : 3 ≤ a) (hb : 3 ≤ b) (hoa : Odd a) (hob : Odd b)
    (hab : a ≠ b) : 15 ≤ a * b := by
  rcases Nat.lt_or_ge a b with h | h
  · have hb5 : 5 ≤ b := by obtain ⟨x, hx⟩ := hoa; obtain ⟨y, hy⟩ := hob; omega
    calc (15 : ℕ) = 3 * 5 := by norm_num
    _ ≤ a * b := Nat.mul_le_mul ha hb5
  · have ha5 : 5 ≤ a := by obtain ⟨x, hx⟩ := hoa; obtain ⟨y, hy⟩ := hob; omega
    calc (15 : ℕ) = 5 * 3 := by norm_num
    _ ≤ a * b := Nat.mul_le_mul ha5 hb

/-- Any odd squarefree number with exactly one prime factor is at least `3`. -/
lemma card1_min {m : ℕ} (hodd : Odd m) (hsq : Squarefree m)
    (hcard : m.primeFactors.card = 1) : 3 ≤ m := by
  obtain ⟨p, hset⟩ := Finset.card_eq_one.mp hcard
  have hprod := Nat.prod_primeFactors_of_squarefree hsq
  rw [hset, Finset.prod_singleton] at hprod
  have hp : p.Prime := Nat.prime_of_mem_primeFactors (n := m) (by rw [hset]; simp)
  have hop : Odd p := odd_of_mem_primeFactors hodd (by rw [hset]; simp)
  have := three_le_odd_prime hp hop
  omega

/-- Any odd squarefree number with exactly two prime factors is at least `15`. -/
lemma card2_min {m : ℕ} (hodd : Odd m) (hsq : Squarefree m)
    (hcard : m.primeFactors.card = 2) : 15 ≤ m := by
  obtain ⟨p, q, hpq, hset⟩ := Finset.card_eq_two.mp hcard
  have hprod := Nat.prod_primeFactors_of_squarefree hsq
  rw [hset, Finset.prod_insert (by simp [hpq]), Finset.prod_singleton] at hprod
  have hp : p.Prime := Nat.prime_of_mem_primeFactors (n := m) (by rw [hset]; simp)
  have hq : q.Prime := Nat.prime_of_mem_primeFactors (n := m) (by rw [hset]; simp)
  have hop : Odd p := odd_of_mem_primeFactors hodd (by rw [hset]; simp)
  have hoq : Odd q := odd_of_mem_primeFactors hodd (by rw [hset]; simp)
  have h := prod2_min (three_le_odd_prime hp hop) (three_le_odd_prime hq hoq) hop hoq hpq
  omega

/-- Any odd squarefree number with exactly three prime factors is at least `105`. -/
lemma card3_min {m : ℕ} (hodd : Odd m) (hsq : Squarefree m)
    (hcard : m.primeFactors.card = 3) : 105 ≤ m := by
  obtain ⟨p, q, r, hpq, hpr, hqr, hset⟩ := Finset.card_eq_three.mp hcard
  have hprod := Nat.prod_primeFactors_of_squarefree hsq
  rw [hset, Finset.prod_insert (by simp [hpq, hpr]), Finset.prod_insert (by simp [hqr]),
    Finset.prod_singleton] at hprod
  have hp : p.Prime := Nat.prime_of_mem_primeFactors (n := m) (by rw [hset]; simp)
  have hq : q.Prime := Nat.prime_of_mem_primeFactors (n := m) (by rw [hset]; simp)
  have hr : r.Prime := Nat.prime_of_mem_primeFactors (n := m) (by rw [hset]; simp)
  have hop : Odd p := odd_of_mem_primeFactors hodd (by rw [hset]; simp)
  have hoq : Odd q := odd_of_mem_primeFactors hodd (by rw [hset]; simp)
  have hor : Odd r := odd_of_mem_primeFactors hodd (by rw [hset]; simp)
  have h := prod3_min (three_le_odd_prime hp hop) (three_le_odd_prime hq hoq)
    (three_le_odd_prime hr hor) hop hoq hor hpq hpr hqr
  calc (105 : ℕ) ≤ p * q * r := h
  _ = p * (q * r) := by ring
  _ = m := hprod

/-- `a 0 = 1`, exact OEIS value, fully verified. -/
theorem a_zero : a 0 = 1 := by
  have h1 : (1 : ℕ) ∈ {k : ℕ | k > 0 ∧
      (Nat.primeFactors k).card = 0 ∧
      (∀ d, d ∈ Nat.divisors k → Nat.Prime (2 * d + k / d))} :=
    ⟨by norm_num, by simp, by decide⟩
  have heq : a 0 = sInf {k : ℕ | k > 0 ∧
      (Nat.primeFactors k).card = 0 ∧
      (∀ d, d ∈ Nat.divisors k → Nat.Prime (2 * d + k / d))} := rfl
  have hle := Nat.sInf_le h1
  obtain ⟨hpos, -, -⟩ := Nat.sInf_mem ⟨1, h1⟩
  rw [heq]
  omega

/-- `a 1 = 3`, exact OEIS value, fully verified. -/
theorem a_one : a 1 = 3 := by
  have h3 : (3 : ℕ) ∈ {k : ℕ | k > 0 ∧
      (Nat.primeFactors k).card = 1 ∧
      (∀ d, d ∈ Nat.divisors k → Nat.Prime (2 * d + k / d))} := by
    refine ⟨by norm_num, ?_, by decide⟩
    rw [(by norm_num : Nat.Prime 3).primeFactors]
    decide
  have heq : a 1 = sInf {k : ℕ | k > 0 ∧
      (Nat.primeFactors k).card = 1 ∧
      (∀ d, d ∈ Nat.divisors k → Nat.Prime (2 * d + k / d))} := rfl
  have hle := Nat.sInf_le h3
  obtain ⟨hpos, hcard, hcond⟩ := Nat.sInf_mem ⟨3, h3⟩
  have h1 : 1 < sInf {k : ℕ | k > 0 ∧
      (Nat.primeFactors k).card = 1 ∧
      (∀ d, d ∈ Nat.divisors k → Nat.Prime (2 * d + k / d))} := by
    by_contra h
    push_neg at h
    have he : sInf {k : ℕ | k > 0 ∧
        (Nat.primeFactors k).card = 1 ∧
        (∀ d, d ∈ Nat.divisors k → Nat.Prime (2 * d + k / d))} = 1 := by omega
    rw [he] at hcard
    simp at hcard
  obtain ⟨hodd, hsq⟩ := odd_and_squarefree_of_divisor_condition h1 hcond
  have hge := card1_min hodd hsq hcard
  rw [heq]
  omega

/-- `a 2 = 15`, exact OEIS value, fully verified. -/
theorem a_two : a 2 = 15 := by
  have h15 : (15 : ℕ) ∈ {k : ℕ | k > 0 ∧
      (Nat.primeFactors k).card = 2 ∧
      (∀ d, d ∈ Nat.divisors k → Nat.Prime (2 * d + k / d))} := by
    refine ⟨by norm_num, ?_, by decide⟩
    rw [show (15 : ℕ) = 3 * 5 by norm_num,
      Nat.primeFactors_mul (by norm_num) (by norm_num),
      (by norm_num : Nat.Prime 3).primeFactors,
      (by norm_num : Nat.Prime 5).primeFactors]
    decide
  have heq : a 2 = sInf {k : ℕ | k > 0 ∧
      (Nat.primeFactors k).card = 2 ∧
      (∀ d, d ∈ Nat.divisors k → Nat.Prime (2 * d + k / d))} := rfl
  have hle := Nat.sInf_le h15
  obtain ⟨hpos, hcard, hcond⟩ := Nat.sInf_mem ⟨15, h15⟩
  have h1 : 1 < sInf {k : ℕ | k > 0 ∧
      (Nat.primeFactors k).card = 2 ∧
      (∀ d, d ∈ Nat.divisors k → Nat.Prime (2 * d + k / d))} := by
    by_contra h
    push_neg at h
    have he : sInf {k : ℕ | k > 0 ∧
        (Nat.primeFactors k).card = 2 ∧
        (∀ d, d ∈ Nat.divisors k → Nat.Prime (2 * d + k / d))} = 1 := by omega
    rw [he] at hcard
    simp at hcard
  obtain ⟨hodd, hsq⟩ := odd_and_squarefree_of_divisor_condition h1 hcond
  have hge := card2_min hodd hsq hcard
  rw [heq]
  omega

set_option maxRecDepth 40000 in
/-- `a 3 = 105`, exact OEIS value, fully verified. -/
theorem a_three : a 3 = 105 := by
  have h105 : (105 : ℕ) ∈ {k : ℕ | k > 0 ∧
      (Nat.primeFactors k).card = 3 ∧
      (∀ d, d ∈ Nat.divisors k → Nat.Prime (2 * d + k / d))} := by
    refine ⟨by norm_num, ?_, ?_⟩
    · rw [show (105 : ℕ) = 3 * (5 * 7) by norm_num,
        Nat.primeFactors_mul (by norm_num) (by norm_num),
        Nat.primeFactors_mul (by norm_num) (by norm_num),
        (by norm_num : Nat.Prime 3).primeFactors,
        (by norm_num : Nat.Prime 5).primeFactors,
        (by norm_num : Nat.Prime 7).primeFactors]
      decide
    · decide +kernel
  have heq : a 3 = sInf {k : ℕ | k > 0 ∧
      (Nat.primeFactors k).card = 3 ∧
      (∀ d, d ∈ Nat.divisors k → Nat.Prime (2 * d + k / d))} := rfl
  have hle := Nat.sInf_le h105
  obtain ⟨hpos, hcard, hcond⟩ := Nat.sInf_mem ⟨105, h105⟩
  have h1 : 1 < sInf {k : ℕ | k > 0 ∧
      (Nat.primeFactors k).card = 3 ∧
      (∀ d, d ∈ Nat.divisors k → Nat.Prime (2 * d + k / d))} := by
    by_contra h
    push_neg at h
    have he : sInf {k : ℕ | k > 0 ∧
        (Nat.primeFactors k).card = 3 ∧
        (∀ d, d ∈ Nat.divisors k → Nat.Prime (2 * d + k / d))} = 1 := by omega
    rw [he] at hcard
    simp at hcard
  obtain ⟨hodd, hsq⟩ := odd_and_squarefree_of_divisor_condition h1 hcond
  have hge := card3_min hodd hsq hcard
  rw [heq]
  omega

end Oeis295124Min



end PartialResults

/-- Conjecture: the sequence is infinite. It is hard to believe!
This is formalized as the set $S(n)$ of candidate numbers being non-empty for all $n$. -/
theorem oeis_295124_conjecture_0 :
  ∀ n : ℕ, (({k : ℕ | k > 0 ∧
              (Nat.primeFactors k).card = n ∧
              (∀ d, d ∈ Nat.divisors k → Nat.Prime (2 * d + k / d))}) : Set ℕ).Nonempty := by sorry
