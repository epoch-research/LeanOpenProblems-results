import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A308734: Number of ordered ways to write $n$ as $(2^a \cdot 3^b)^2 + (2^c \cdot 5^d)^2 + x^2 + y^2$,
where $a,b,c,d,x,y$ are nonnegative integers with $x \le y$.

Note: The provided definition uses a computationally convenient, but potentially insufficient, range `M` for the exponents $a, b, c, d$.
A mathematically precise definition would use unbounded natural numbers for $a, b, c, d, x, y$ and count the size of the resulting set.
We proceed with the definition as given in the prompt.
-/
def A308734 (n : ℕ) : ℕ :=
  -- We use a six-fold nested summation over a range $M$.
  let M := Nat.sqrt n + 1

  Finset.sum (range M) fun a =>
  Finset.sum (range M) fun b =>
  Finset.sum (range M) fun c =>
  Finset.sum (range M) fun d =>
  Finset.sum (range M) fun x =>
  Finset.sum (range M) fun y =>
    let term1 := (2^a * 3^b)^2
    let term2 := (2^c * 5^d)^2

    if term1 + term2 + x^2 + y^2 = n ∧ x ≤ y
    then 1
    else 0

/-!
### Analysis and reduction

The following development reduces the conjecture to its genuine mathematical core.

`HasRep n` is the (unbounded, order-free) representability predicate: `n` can be written
as `(2^a·3^b)² + (2^c·5^d)² + x² + y²`.  The two facts we prove rigorously are:

* `count_pos_of_HasRep`: **the bounded range `M = Nat.sqrt n + 1` used in `A308734` is
  always sufficient.**  Any (unbounded) representation of `n` has all its data below `M`,
  and, after ordering `x ≤ y`, it contributes a `1` to the sum.  Hence
  `HasRep n → 0 < A308734 n`.  This settles the concern raised in the docstring: the
  computationally convenient definition does **not** lose any solutions.

* `hasRep_mul_four`: the property is preserved under multiplication by `4`
  (scale every summand by `2`), giving a `mod 4` descent.

Consequently the conjecture is equivalent to `∀ n ≥ 2, HasRep n`, and the descent reduces
it to the case `n ≥ 8` with `4 ∤ n`.

That remaining case is exactly **Sun's four-square conjecture** (OEIS A308734).  It is a
well-known *open* problem: see S. Banerjee, *On a Conjecture of Sun about sums of restricted
squares* (arXiv:2202.04057), which states this very conjecture
(`n = x² + y² + (2^a3^b)² + (2^c5^d)²`) and remarks that it "seems to be out of reach with
current techniques".  Only ineffective / almost-prime approximations are known
(via Brüdern–Fouvry sieve methods), none of which yields the exact statement.
The obstruction is that whether `n − A² − B²` is a sum of two squares depends on the
multiplicative structure (primes `≡ 3 (mod 4)` to odd power), which cannot be controlled by
the finitely many logarithmically-sparse smooth choices via any elementary argument.
-/

/-- The unbounded, order-free representability predicate underlying `A308734`. -/
def HasRep (n : ℕ) : Prop :=
  ∃ a b c d x y : ℕ, (2^a * 3^b)^2 + (2^c * 5^d)^2 + x^2 + y^2 = n

/-- **Range sufficiency.** If `n` is representable at all (with unbounded exponents),
then it is representable within the bounded search of `A308734`, so `A308734 n > 0`.
This rigorously discharges the docstring's concern that the range `M` might be insufficient. -/
theorem count_pos_of_HasRep {n : ℕ} (h : HasRep n) : 0 < A308734 n := by
  obtain ⟨a, b, c, d, x, y, heq⟩ := h
  -- We may assume `x ≤ y` (the equation is symmetric in `x` and `y`).
  wlog hxy : x ≤ y generalizing x y
  · exact this y x (by rw [← heq]; ring) ((not_le.mp hxy).le)
  set s := Nat.sqrt n with hs
  -- Each square is `≤ n`.
  have hterm1 : (2^a * 3^b)^2 ≤ n := by omega
  have hterm2 : (2^c * 5^d)^2 ≤ n := by omega
  have hx2 : x^2 ≤ n := by nlinarith [sq_nonneg y, sq_nonneg x]
  have hy2 : y^2 ≤ n := by nlinarith [sq_nonneg y, sq_nonneg x]
  -- Hence each base is `≤ Nat.sqrt n`.
  have hAB : 2^a * 3^b ≤ s := by rw [hs, Nat.le_sqrt]; nlinarith [hterm1]
  have hCD : 2^c * 5^d ≤ s := by rw [hs, Nat.le_sqrt]; nlinarith [hterm2]
  have hxs : x ≤ s := by rw [hs, Nat.le_sqrt]; nlinarith [hx2]
  have hys : y ≤ s := by rw [hs, Nat.le_sqrt]; nlinarith [hy2]
  have h3b : 1 ≤ 3^b := Nat.one_le_pow _ _ (by norm_num)
  have h5d : 1 ≤ 5^d := Nat.one_le_pow _ _ (by norm_num)
  have h2a : 1 ≤ 2^a := Nat.one_le_pow _ _ (by norm_num)
  have h2c : 1 ≤ 2^c := Nat.one_le_pow _ _ (by norm_num)
  -- The exponents are below `s + 1 = M` since `k < base^k ≤ base^k · (…) ≤ s`.
  have ha : a < s + 1 := by
    have : 2^a ≤ 2^a * 3^b := Nat.le_mul_of_pos_right _ (by omega)
    have := Nat.lt_two_pow_self (n := a)
    omega
  have hb : b < s + 1 := by
    have h1 : 3^b ≤ 2^a * 3^b := Nat.le_mul_of_pos_left _ (by omega)
    have h2 : b < 3^b := Nat.lt_pow_self (by norm_num)
    omega
  have hc : c < s + 1 := by
    have : 2^c ≤ 2^c * 5^d := Nat.le_mul_of_pos_right _ (by omega)
    have := Nat.lt_two_pow_self (n := c)
    omega
  have hd : d < s + 1 := by
    have h1 : 5^d ≤ 2^c * 5^d := Nat.le_mul_of_pos_left _ (by omega)
    have h2 : d < 5^d := Nat.lt_pow_self (by norm_num)
    omega
  have hxlt : x < s + 1 := by omega
  have hylt : y < s + 1 := by omega
  -- Exhibit the contributing summand.
  unfold A308734
  simp only
  rw [← hs]
  refine Finset.sum_pos' (fun _ _ => Nat.zero_le _) ⟨a, Finset.mem_range.mpr ha, ?_⟩
  refine Finset.sum_pos' (fun _ _ => Nat.zero_le _) ⟨b, Finset.mem_range.mpr hb, ?_⟩
  refine Finset.sum_pos' (fun _ _ => Nat.zero_le _) ⟨c, Finset.mem_range.mpr hc, ?_⟩
  refine Finset.sum_pos' (fun _ _ => Nat.zero_le _) ⟨d, Finset.mem_range.mpr hd, ?_⟩
  refine Finset.sum_pos' (fun _ _ => Nat.zero_le _) ⟨x, Finset.mem_range.mpr hxlt, ?_⟩
  refine Finset.sum_pos' (fun _ _ => Nat.zero_le _) ⟨y, Finset.mem_range.mpr hylt, ?_⟩
  dsimp only
  rw [if_pos ⟨heq, hxy⟩]
  norm_num

/-- **Converse of range sufficiency.** If the bounded count is positive, then `n` is
representable (some contributing tuple witnesses `HasRep n`). -/
theorem hasRep_of_count_pos {n : ℕ} (h : 0 < A308734 n) : HasRep n := by
  unfold A308734 at h
  dsimp only at h
  obtain ⟨a, -, h⟩ := Finset.exists_ne_zero_of_sum_ne_zero h.ne'
  obtain ⟨b, -, h⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  obtain ⟨c, -, h⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  obtain ⟨d, -, h⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  obtain ⟨x, -, h⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  obtain ⟨y, -, h⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  by_cases hcond : (2 ^ a * 3 ^ b) ^ 2 + (2 ^ c * 5 ^ d) ^ 2 + x ^ 2 + y ^ 2 = n ∧ x ≤ y
  · exact ⟨a, b, c, d, x, y, hcond.1⟩
  · rw [if_neg hcond] at h; exact absurd rfl h

/-- **Full characterization.** The bounded search of `A308734` detects representability
exactly: `A308734 n > 0 ↔ HasRep n`. This makes the conjecture `∀ n > 1, A308734 n > 0`
provably equivalent to Sun's four-square conjecture `∀ n ≥ 2, HasRep n`. -/
theorem count_pos_iff_hasRep {n : ℕ} : 0 < A308734 n ↔ HasRep n :=
  ⟨hasRep_of_count_pos, count_pos_of_HasRep⟩

/-- **Mod-4 descent.** Representability is preserved under multiplication by `4`
(scale each of the four summands by `2`; the smooth structure is preserved since
`2·2^a·3^b = 2^{a+1}·3^b` and `2·2^c·5^d = 2^{c+1}·5^d`). -/
theorem hasRep_mul_four {m : ℕ} (h : HasRep m) : HasRep (4 * m) := by
  obtain ⟨a, b, c, d, x, y, heq⟩ := h
  refine ⟨a + 1, b, c + 1, d, 2 * x, 2 * y, ?_⟩
  have e1 : (2^(a+1) * 3^b)^2 = 4 * (2^a * 3^b)^2 := by ring
  have e2 : (2^(c+1) * 5^d)^2 = 4 * (2^c * 5^d)^2 := by ring
  rw [e1, e2]; ring_nf; ring_nf at heq; omega

/-- Base cases `2 ≤ n < 8`, by explicit witnesses. -/
theorem hasRep_small (n : ℕ) (h1 : 2 ≤ n) (h2 : n < 8) : HasRep n := by
  interval_cases n
  · exact ⟨0, 0, 0, 0, 0, 0, by norm_num⟩            -- 2 = 1 + 1 + 0 + 0
  · exact ⟨0, 0, 0, 0, 0, 1, by norm_num⟩            -- 3 = 1 + 1 + 0 + 1
  · exact ⟨0, 0, 0, 0, 1, 1, by norm_num⟩            -- 4 = 1 + 1 + 1 + 1
  · exact ⟨0, 0, 1, 0, 0, 0, by norm_num⟩            -- 5 = 1 + 4 + 0 + 0
  · exact ⟨0, 0, 0, 0, 0, 2, by norm_num⟩            -- 6 = 1 + 1 + 0 + 4
  · exact ⟨0, 0, 0, 0, 1, 2, by norm_num⟩            -- 7 = 1 + 1 + 1 + 4

/-- Every `n ≥ 2` is representable. Base cases and the `mod 4` descent are proven;
the remaining case (`n ≥ 8`, `4 ∤ n`) is exactly **Sun's four-square conjecture**
(OEIS A308734), an open problem "out of reach with current techniques"
(cf. Banerjee, arXiv:2202.04057). -/
theorem hasRep_all : ∀ n, 2 ≤ n → HasRep n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro hn
    rcases Nat.lt_or_ge n 8 with hsmall | hbig
    · exact hasRep_small n hn hsmall
    · by_cases hmod : n % 4 = 0
      · -- `4 ∣ n` and `n ≥ 8`: descend to `n / 4`.
        have hdvd : 4 ∣ n := Nat.dvd_of_mod_eq_zero hmod
        have hlt : n / 4 < n := Nat.div_lt_self (by omega) (by norm_num)
        have hge : 2 ≤ n / 4 := by
          rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 4)]; omega
        have hrec : HasRep (n / 4) := IH (n / 4) hlt hge
        have := hasRep_mul_four hrec
        rwa [Nat.mul_div_cancel' hdvd] at this
      · -- OPEN CORE: `n ≥ 8`, `4 ∤ n`. This is Sun's four-square conjecture (A308734),
        -- currently open ("out of reach with current techniques", Banerjee 2022).
        sorry

/--
Four-square Conjecture: a(n) > 0 for all n > 1.
This is much stronger than Lagrange's four-square theorem.
(OEIS A308734, Comment C2)
-/
theorem oeis_a308734_conjecture_0 : ∀ n : ℕ, 1 < n → A308734 n > 0 := by
  intro n hn
  exact count_pos_of_HasRep (hasRep_all n (by omega))
