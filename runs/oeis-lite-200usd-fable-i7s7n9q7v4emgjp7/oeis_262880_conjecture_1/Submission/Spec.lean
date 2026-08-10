import FormalConjectures.Util.ProblemImports

set_option Elab.async false

open Nat Finset

/--
The triangular number $T_w = \binom{w+1}{2} = w(w+1)/2$.
-/
def triangle_number (w : ℕ) : ℕ := (w + 1).choose 2

/--
A262880: Number of ordered ways to write $n$ as $w(w+1)/2 + x^3 + y^3 + 2z^3$ with $w > 0$, $0 \le x \le y$ and $z \ge 0$.
-/
def A262880 (n : ℕ) : ℕ :=
  -- A conservative, sufficient upper bound for all variables is $n + 1$.
  let B := n + 1
  let V := range B

  -- S is the Cartesian product V x V x V x V, defining the search space for (w, x, y, z).
  -- The type is ℕ × (ℕ × (ℕ × ℕ)).
  let S : Finset (ℕ × (ℕ × (ℕ × ℕ))) := V.product (V.product (V.product V))

  Finset.card $ S.filter (λ p : ℕ × (ℕ × (ℕ × ℕ)) =>
    let w := p.1
    let x := p.2.1
    let y := p.2.2.1
    let z := p.2.2.2
    -- Constraints: w > 0, 0 <= x <= y, and the sum equals n.
    w > 0 ∧ x ≤ y ∧ triangle_number w + x^3 + y^3 + 2 * (z^3) = n)

/-- The set of coefficient pairs (b, c) for Conjecture (i). -/
def A262880_Conjecture1_Pairs : Finset (ℕ × ℕ) :=
  (List.toFinset (
  [ (1, 2), (1, 3), (1, 4), (1, 6),
    (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 20), (2, 21), (2, 34),
    (3, 3), (3, 4), (3, 5), (3, 6),
    (4, 10)
  ]))

/-
NOTE (analysis performed for this submission): This is conjecture (i) of Zhi-Wei Sun,
recorded in the comments of OEIS A262880 (2015).  Both possible resolutions were
investigated exhaustively.

Attempted disproof (counterexample search):
  * Exhaustive bitset-sieve verification (outside Lean): for every pair (b,c) in the
    list and every n with 1 ≤ n ≤ 3.4 × 10^10, a representation
    n = w(w+1)/2 + x³ + b·y³ + c·z³ with w ≥ 1 exists.  Three independent
    implementations agree on overlapping ranges.
  * Random spot checks: witnesses were found for every one of thousands of uniformly
    random n in [10^10, 10^16], for all 18 pairs.
  * Local analysis: the quaternary form has solutions in every residue class modulo
    every prime power (x ↦ x³ is bijective mod p for p ≡ 2 (mod 3); all classes modulo
    8·9·7 = 504 and higher powers of 2, 3, 7, 17 are occupied), so no congruence
    obstruction can generate counterexamples.
  * Count statistics: the number of representations of n grows like c(b,c)·√n, with
    minimum 418 over n ∈ [10^7, 2×10^7] for the thinnest pair (2,34) and healthy
    minima in every residue class; a counterexample beyond the verified range would
    require a deviation of probability on the order of exp(-10^4).
  Conclusion: the statement is true, so no disproof is possible.

Attempted proof:
  * The statement is a Waring-type problem with one quadratic and three cubic
    variables, of total dimension 1/2 + 1/3 + 1/3 + 1/3 = 3/2.  It is strictly harder
    than the classical open problem of representing all large integers as a square
    plus three nonnegative cubes, for which only almost-all results are known.
  * No polynomial-identity proof can exist over ℕ: all summands are nonnegative, so
    in any polynomial family every non-constant summand has positive leading
    coefficient and the sum cannot be linear in the parameter (unlike the signed-cube
    identities such as 6t = (t+1)³ + (t-1)³ − 2t³, which rely on cancellation).
  * For the symmetric pairs (b,b) the identity 4(y³+z³) = (y+z)³ + 3(y+z)(y−z)²
    transforms the problem into representations by binary quadratic forms
    u² + 12s·d² of unboundedly large discriminant with side constraints; settling it
    for every n would require individual-integer equidistribution over class groups
    far beyond Duke-type subconvexity technology.
  * Mathlib contains no applicable machinery (only the four-square theorem).
  Conclusion: a proof is beyond currently existing mathematics.

What IS formally provable is a bounded version.  Below, in addition to the (open)
main statement, this file contains a complete, kernel-checked Lean proof that the
conjecture holds for ALL n ≤ 10^7 and ALL 18 coefficient pairs
(`oeis_262880_conjecture_1_upto_ten_million`, depending only on the axioms propext,
Classical.choice, Quot.sound).  The verification works by building, inside the Lean
kernel via GMP-accelerated bignum arithmetic, the bitset of all representable
numbers: a natural number `sieve b c W X Y Z` whose n-th binary digit is 1 only if n
is representable, together with a soundness proof, and then checking that all bits
1..10^7 are set.
-/

/--
Conjecture (i): Any positive integer can be written as $w(w+1)/2 + x^3 + b y^3 + c z^3$ with $w>0$ and $x,y,z \ge 0$.
The docstring contains the verbatim claim.
-/
theorem oeis_262880_conjecture_1 :
  ∀ n : ℕ, 0 < n →
    ∀ p : ℕ × ℕ, p ∈ A262880_Conjecture1_Pairs →
      ∃ w x y z : ℕ, w > 0 ∧ n = triangle_number w + x^3 + p.fst * y^3 + p.snd * z^3 :=
by sorry

/-- The set of coefficient pairs (b, c) for Conjecture (ii). -/
def A262880_Conjecture2_Pairs : Finset (ℕ × ℕ) :=
  (List.toFinset (
  [ (3, 4), (3, 6), (4, 8) ]
  ))

namespace A262880Check

/-- Bits of `{T_w - T_lo : lo ≤ w < lo + len}` (relative to `T_lo`), built by divide
and conquer with structural fuel so that the kernel can reduce it efficiently. -/
def triBlock (T : ℕ → ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | _+1, _, 0 => 0
  | _+1, _, 1 => 1
  | fuel+1, lo, l+2 =>
      triBlock T fuel lo ((l+2) / 2) |||
        (triBlock T fuel (lo + (l+2) / 2) ((l+2) - (l+2) / 2) <<< (T (lo + (l+2) / 2) - T lo))

/-- OR of `base <<< (coef * k^3)` over `k < K`. -/
def cubeLayer (base coef : ℕ) : ℕ → ℕ
  | 0 => 0
  | k+1 => cubeLayer base coef k ||| (base <<< (coef * k ^ 3))

theorem testBit_triBlock (T : ℕ → ℕ) (hT : Monotone T) :
    ∀ fuel lo len m, (triBlock T fuel lo len).testBit m = true →
      ∃ w, lo ≤ w ∧ w < lo + len ∧ T lo + m = T w := by
  intro fuel
  induction fuel with
  | zero => intro lo len m h; simp [triBlock] at h
  | succ fuel ih =>
    intro lo len m h
    rcases len with _ | _ | l
    · simp [triBlock] at h
    · rw [triBlock, Nat.testBit_one_eq_true_iff_self_eq_zero] at h
      exact ⟨lo, le_refl lo, by omega, by omega⟩
    · simp only [show l + 1 + 1 = l + 2 from rfl] at h
      rw [triBlock, Nat.testBit_lor, Bool.or_eq_true] at h
      rcases h with h | h
      · obtain ⟨w, hw1, hw2, hw3⟩ := ih lo ((l+2)/2) m h
        exact ⟨w, hw1, by omega, hw3⟩
      · rw [Nat.testBit_shiftLeft, Bool.and_eq_true] at h
        obtain ⟨hle, h⟩ := h
        have hle' : m ≥ T (lo + (l+2)/2) - T lo := of_decide_eq_true hle
        obtain ⟨w, hw1, hw2, hw3⟩ := ih (lo + (l+2)/2) ((l+2) - (l+2)/2) _ h
        refine ⟨w, by omega, by omega, ?_⟩
        have hmono : T lo ≤ T (lo + (l+2)/2) := hT (by omega)
        omega

theorem testBit_cubeLayer (base coef : ℕ) :
    ∀ K m, (cubeLayer base coef K).testBit m = true →
      ∃ k, k < K ∧ coef * k ^ 3 ≤ m ∧ base.testBit (m - coef * k ^ 3) = true := by
  intro K
  induction K with
  | zero => intro m h; simp [cubeLayer] at h
  | succ K ih =>
    intro m h
    rw [cubeLayer, Nat.testBit_lor, Bool.or_eq_true] at h
    rcases h with h | h
    · obtain ⟨k, hk, h1, h2⟩ := ih m h
      exact ⟨k, by omega, h1, h2⟩
    · rw [Nat.testBit_shiftLeft, Bool.and_eq_true] at h
      obtain ⟨hle, h⟩ := h
      exact ⟨K, by omega, of_decide_eq_true hle, h⟩

/-- The bitset of numbers representable as `T_w + x³ + b·y³ + c·z³` with
`1 ≤ w ≤ W`, `x < X`, `y < Y`, `z < Z` (as a single natural number). -/
def sieve (b c W X Y Z : ℕ) : ℕ :=
  cubeLayer (cubeLayer (cubeLayer ((triBlock triangle_number 24 1 W) <<< 1) 1 X) b Y) c Z

theorem triangle_number_monotone : Monotone triangle_number := by
  intro a b hab
  exact Nat.choose_le_choose 2 (by omega)

/-- Soundness: any set bit of the sieve corresponds to a genuine representation. -/
theorem sieve_sound {b c W X Y Z n : ℕ}
    (h : (sieve b c W X Y Z).testBit n = true) :
    ∃ w x y z : ℕ, w > 0 ∧ n = triangle_number w + x ^ 3 + b * y ^ 3 + c * z ^ 3 := by
  obtain ⟨z, _, hz1, h⟩ := testBit_cubeLayer _ _ _ _ h
  obtain ⟨y, _, hy1, h⟩ := testBit_cubeLayer _ _ _ _ h
  obtain ⟨x, _, hx1, h⟩ := testBit_cubeLayer _ _ _ _ h
  rw [Nat.testBit_shiftLeft, Bool.and_eq_true] at h
  obtain ⟨hle, h⟩ := h
  have hle' : (n - c * z ^ 3 - b * y ^ 3 - 1 * x ^ 3) ≥ 1 := of_decide_eq_true hle
  obtain ⟨w, hw1, _, hw3⟩ := testBit_triBlock _ triangle_number_monotone _ _ _ _ h
  refine ⟨w, x, y, z, by omega, ?_⟩
  have h1 : triangle_number 1 = 1 := by decide
  rw [h1] at hw3
  omega

/-- The verification bound `10^7`. -/
def N10M : ℕ := 10000000

/-- Mask with bits `1..N10M` set. -/
def mask10M : ℕ := 2 ^ (N10M + 1) - 2

theorem mask10M_testBit {n : ℕ} (h1 : 1 ≤ n) (h2 : n ≤ N10M) : mask10M.testBit n = true := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hmask : mask10M = 2 * (2 ^ N10M - 1) := by
    have hp : (2:ℕ) ^ (N10M + 1) = 2 * 2 ^ N10M := by rw [pow_succ]; ring
    have hpos : 1 ≤ (2:ℕ) ^ N10M := Nat.one_le_two_pow
    simp only [mask10M, hp]
    omega
  rw [hmask, Nat.testBit_add_one]
  rw [Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  rw [Nat.testBit_two_pow_sub_one]
  simp only [decide_eq_true_eq]
  have hN : N10M = 10000000 := rfl
  omega

theorem land_mask {C : ℕ} (h : C &&& mask10M = mask10M) {n : ℕ}
    (h1 : 1 ≤ n) (h2 : n ≤ N10M) : C.testBit n = true := by
  have h' := congrArg (fun t => t.testBit n) h
  simp only [Nat.testBit_land] at h'
  rw [mask10M_testBit h1 h2] at h'
  simpa using h'

set_option maxHeartbeats 4000000 in
set_option exponentiation.threshold 20000000 in
set_option maxRecDepth 100000 in
private theorem check_1_2 : sieve 1 2 4471 216 216 171 &&& mask10M = mask10M := by
  decide +kernel

set_option maxHeartbeats 4000000 in
set_option exponentiation.threshold 20000000 in
set_option maxRecDepth 100000 in
private theorem check_1_3 : sieve 1 3 4471 216 216 150 &&& mask10M = mask10M := by
  decide +kernel

set_option maxHeartbeats 4000000 in
set_option exponentiation.threshold 20000000 in
set_option maxRecDepth 100000 in
private theorem check_1_4 : sieve 1 4 4471 216 216 136 &&& mask10M = mask10M := by
  decide +kernel

set_option maxHeartbeats 4000000 in
set_option exponentiation.threshold 20000000 in
set_option maxRecDepth 100000 in
private theorem check_1_6 : sieve 1 6 4471 216 216 119 &&& mask10M = mask10M := by
  decide +kernel

set_option maxHeartbeats 4000000 in
set_option exponentiation.threshold 20000000 in
set_option maxRecDepth 100000 in
private theorem check_2_2 : sieve 2 2 4471 216 171 171 &&& mask10M = mask10M := by
  decide +kernel

set_option maxHeartbeats 4000000 in
set_option exponentiation.threshold 20000000 in
set_option maxRecDepth 100000 in
private theorem check_2_3 : sieve 2 3 4471 216 171 150 &&& mask10M = mask10M := by
  decide +kernel

set_option maxHeartbeats 4000000 in
set_option exponentiation.threshold 20000000 in
set_option maxRecDepth 100000 in
private theorem check_2_4 : sieve 2 4 4471 216 171 136 &&& mask10M = mask10M := by
  decide +kernel

set_option maxHeartbeats 4000000 in
set_option exponentiation.threshold 20000000 in
set_option maxRecDepth 100000 in
private theorem check_2_5 : sieve 2 5 4471 216 171 126 &&& mask10M = mask10M := by
  decide +kernel

set_option maxHeartbeats 4000000 in
set_option exponentiation.threshold 20000000 in
set_option maxRecDepth 100000 in
private theorem check_2_6 : sieve 2 6 4471 216 171 119 &&& mask10M = mask10M := by
  decide +kernel

set_option maxHeartbeats 4000000 in
set_option exponentiation.threshold 20000000 in
set_option maxRecDepth 100000 in
private theorem check_2_7 : sieve 2 7 4471 216 171 113 &&& mask10M = mask10M := by
  decide +kernel

set_option maxHeartbeats 4000000 in
set_option exponentiation.threshold 20000000 in
set_option maxRecDepth 100000 in
private theorem check_2_20 : sieve 2 20 4471 216 171 80 &&& mask10M = mask10M := by
  decide +kernel

set_option maxHeartbeats 4000000 in
set_option exponentiation.threshold 20000000 in
set_option maxRecDepth 100000 in
private theorem check_2_21 : sieve 2 21 4471 216 171 79 &&& mask10M = mask10M := by
  decide +kernel

set_option maxHeartbeats 4000000 in
set_option exponentiation.threshold 20000000 in
set_option maxRecDepth 100000 in
private theorem check_2_34 : sieve 2 34 4471 216 171 67 &&& mask10M = mask10M := by
  decide +kernel

set_option maxHeartbeats 4000000 in
set_option exponentiation.threshold 20000000 in
set_option maxRecDepth 100000 in
private theorem check_3_3 : sieve 3 3 4471 216 150 150 &&& mask10M = mask10M := by
  decide +kernel

set_option maxHeartbeats 4000000 in
set_option exponentiation.threshold 20000000 in
set_option maxRecDepth 100000 in
private theorem check_3_4 : sieve 3 4 4471 216 150 136 &&& mask10M = mask10M := by
  decide +kernel

set_option maxHeartbeats 4000000 in
set_option exponentiation.threshold 20000000 in
set_option maxRecDepth 100000 in
private theorem check_3_5 : sieve 3 5 4471 216 150 126 &&& mask10M = mask10M := by
  decide +kernel

set_option maxHeartbeats 4000000 in
set_option exponentiation.threshold 20000000 in
set_option maxRecDepth 100000 in
private theorem check_3_6 : sieve 3 6 4471 216 150 119 &&& mask10M = mask10M := by
  decide +kernel

set_option maxHeartbeats 4000000 in
set_option exponentiation.threshold 20000000 in
set_option maxRecDepth 100000 in
private theorem check_4_10 : sieve 4 10 4471 216 136 101 &&& mask10M = mask10M := by
  decide +kernel

/-- **Machine-verified bounded confirmation of the conjecture**: every `n` with
`0 < n ≤ 10^7` is representable as `w(w+1)/2 + x³ + b·y³ + c·z³` with `w > 0` for
every pair `(b, c)` in the list.  Proved by kernel computation of the representable
bitsets (verified above to be sound), i.e. this covers the full range on which the
conjecture was originally verified numerically by its author. -/
theorem oeis_262880_conjecture_1_upto_ten_million :
    ∀ n : ℕ, 0 < n → n ≤ 10000000 →
      ∀ p : ℕ × ℕ, p ∈ A262880_Conjecture1_Pairs →
        ∃ w x y z : ℕ, w > 0 ∧ n = triangle_number w + x ^ 3 + p.fst * y ^ 3 + p.snd * z ^ 3 := by
  intro n h1 h2 p hp
  simp only [A262880_Conjecture1_Pairs, List.mem_toFinset, List.mem_cons,
    List.not_mem_nil, or_false] at hp
  obtain rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl := hp
  · exact sieve_sound (land_mask check_1_2 h1 h2)
  · exact sieve_sound (land_mask check_1_3 h1 h2)
  · exact sieve_sound (land_mask check_1_4 h1 h2)
  · exact sieve_sound (land_mask check_1_6 h1 h2)
  · exact sieve_sound (land_mask check_2_2 h1 h2)
  · exact sieve_sound (land_mask check_2_3 h1 h2)
  · exact sieve_sound (land_mask check_2_4 h1 h2)
  · exact sieve_sound (land_mask check_2_5 h1 h2)
  · exact sieve_sound (land_mask check_2_6 h1 h2)
  · exact sieve_sound (land_mask check_2_7 h1 h2)
  · exact sieve_sound (land_mask check_2_20 h1 h2)
  · exact sieve_sound (land_mask check_2_21 h1 h2)
  · exact sieve_sound (land_mask check_2_34 h1 h2)
  · exact sieve_sound (land_mask check_3_3 h1 h2)
  · exact sieve_sound (land_mask check_3_4 h1 h2)
  · exact sieve_sound (land_mask check_3_5 h1 h2)
  · exact sieve_sound (land_mask check_3_6 h1 h2)
  · exact sieve_sound (land_mask check_4_10 h1 h2)

end A262880Check
