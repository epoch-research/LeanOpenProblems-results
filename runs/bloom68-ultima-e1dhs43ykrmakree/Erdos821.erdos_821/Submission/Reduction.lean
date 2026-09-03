import FormalConjecturesUtil

/-!
# Verified partial results and a reduction for Erdős 821

This is a development file, not a solution of `Submission/Spec.lean`.
There are no admitted lemmas or added axioms.

Main results in namespace `Erdos821Counting`:
* `infinite_large_fibers_of_one_le` proves the desired infinitude for `ε ≥ 1`.
* `erdos821_of_smooth_prime_hypothesis` proves the entire requested conclusion
  under the explicitly defined `SmoothPrimeHypothesis`.
* `large_fiber_of_many_smooth_shifted_primes` is the finite counting construction.

The unresolved arithmetic input is `SmoothPrimeHypothesis`: for every natural
`r`, at arbitrarily large natural `y`, there are at least `y ^ r` primes at most
`y ^ (r + 1)` whose predecessors have no prime factor greater than `y`.
This hypothesis is not asserted as a theorem here.
-/

/-
# A finite conditional counting theorem for inverse totients

For a finite set `P` of primes, distinct subsets give distinct squarefree products,
and the totient of such a product is the product of the shifted primes.  Thus if
all shifted products from `k`-element subsets land in a finite target set `T`, the
inequality `T.card * K < Nat.choose P.card k` forces a totient fiber of size greater
than `K`.  The resulting target lies between `2 ^ (k - 1)` and `X ^ k` when all
primes are at most `X`; the lower bound improves to `2 ^ k` if all primes exceed 2.

This is a conditional finite combinatorial theorem, not a proof of the open
Erdős 821 conjecture.  In particular, no existence of suitably small target sets
or of an infinite family satisfying the counting hypothesis is asserted.

The positive-fiber finiteness argument is the independent prime-support argument
from `/tmp/Erdos821Research.lean`, reproduced here so this file depends only on
Mathlib.  No problem specification is imported or modified.
-/

set_option autoImplicit false

namespace Erdos821Counting

open Finset

/- ## Finiteness of the full inverse-totient fibers -/

/-- A natural number is determined by its totient and its set of prime factors. -/
theorem eq_of_totient_eq_of_primeFactors_eq {a b : ℕ}
    (ht : a.totient = b.totient) (hs : a.primeFactors = b.primeFactors) : a = b := by
  have ha := Nat.totient_mul_prod_primeFactors a
  have hb := Nat.totient_mul_prod_primeFactors b
  rw [← hs, ← ht] at hb
  have hp : 0 < ∏ p ∈ a.primeFactors, (p - 1) := by
    apply Finset.prod_pos
    intro p hpa
    exact Nat.sub_pos_of_lt (Nat.prime_of_mem_primeFactors hpa).one_lt
  exact Nat.eq_of_mul_eq_mul_right hp (ha.symm.trans hb)

/-- Every shifted prime factor of `m` divides `m.totient`. -/
theorem prime_sub_one_dvd_of_totient_eq {m n p : ℕ}
    (ht : m.totient = n) (hp : p ∈ m.primeFactors) : p - 1 ∣ n := by
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hdvd := Nat.dvd_of_mem_primeFactors hp
  have h := Nat.totient_dvd_of_dvd hdvd
  simpa [ht, Nat.totient_prime hprime] using h

/-- A positive totient fiber injects into a finite collection of prime supports. -/
theorem totient_fiber_finite_of_pos {n : ℕ} (hn : 0 < n) :
    {m : ℕ | Nat.totient m = n}.Finite := by
  refine Set.Finite.of_injOn (f := Nat.primeFactors)
    (t := (↑(Finset.range (n + 2)).powerset : Set (Finset ℕ))) ?_ ?_
    (Finset.finite_toSet _)
  · intro m hm
    change m.totient = n at hm
    simp only [Finset.mem_coe, Finset.mem_powerset]
    intro p hp
    have hd := prime_sub_one_dvd_of_totient_eq hm hp
    have hl := Nat.le_of_dvd hn hd
    have hprime := Nat.prime_of_mem_primeFactors hp
    simp only [Finset.mem_range]
    omega
  · intro a ha b hb hs
    exact eq_of_totient_eq_of_primeFactors_eq (ha.trans hb.symm) hs

/-- All totient fibers are finite, including the fiber at zero. -/
theorem totient_fiber_finite (n : ℕ) :
    {m : ℕ | Nat.totient m = n}.Finite := by
  by_cases hn : n = 0
  · subst n
    simp [Nat.totient_eq_zero]
  · exact totient_fiber_finite_of_pos (Nat.pos_of_ne_zero hn)

/- ## Distinct squarefree inputs and their totients -/

/-- Products of distinct primes determine the finset of primes. -/
theorem prime_product_injective {S R : Finset ℕ}
    (hS : ∀ p ∈ S, Nat.Prime p) (hR : ∀ p ∈ R, Nat.Prime p)
    (h : (∏ p ∈ S, p) = ∏ p ∈ R, p) : S = R := by
  calc
    S = (∏ p ∈ S, p).primeFactors := (Nat.primeFactors_prod hS).symm
    _ = (∏ p ∈ R, p).primeFactors := congrArg Nat.primeFactors h
    _ = R := Nat.primeFactors_prod hR

/-- Euler's formula specialized to a product of distinct primes. -/
theorem totient_prime_product (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p) :
    Nat.totient (∏ p ∈ S, p) = ∏ p ∈ S, (p - 1) := by
  have hp : 0 < ∏ p ∈ S, p := Finset.prod_pos fun p hp => (hS p hp).pos
  rw [Nat.totient_eq_div_primeFactors_mul, Nat.primeFactors_prod hS,
    Nat.div_self hp, one_mul]

/-- The number of `k`-subsets producing `n` is bounded by the full inverse-totient
fiber, because their distinct prime products are distinct preimages of `n`. -/
theorem card_shift_product_fiber_le_totient_fiber
    (P : Finset ℕ) (k n : ℕ) (hP : ∀ p ∈ P, Nat.Prime p) :
    ((P.powersetCard k).filter (fun S => (∏ p ∈ S, (p - 1)) = n)).card ≤
      {m : ℕ | Nat.totient m = n}.ncard := by
  classical
  let F := (P.powersetCard k).filter (fun S => (∏ p ∈ S, (p - 1)) = n)
  have hsub : ∀ S ∈ F, S ⊆ P := by
    intro S hS
    exact (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hS).1).1
  have hle := Set.ncard_le_ncard_of_injOn
    (s := (↑F : Set (Finset ℕ))) (t := {m : ℕ | Nat.totient m = n})
    (fun S : Finset ℕ => ∏ p ∈ S, p)
    (by
      intro S hS
      change Nat.totient (∏ p ∈ S, p) = n
      rw [totient_prime_product S (fun p hp => hP p (hsub S hS hp))]
      exact (Finset.mem_filter.mp hS).2)
    (by
      intro S hS R hR h
      exact prime_product_injective
        (fun p hp => hP p (hsub S hS hp))
        (fun p hp => hP p (hsub R hR hp)) h)
    (totient_fiber_finite n)
  simpa only [Set.ncard_coe_finset] using hle

/- ## Pigeonhole principle with binomially many inputs -/

/-- Finite conditional counting, retaining a subset witnessing the target value.
The strict inequality automatically handles empty sets and the case `k = 0`. -/
theorem exists_large_totient_fiber_witness
    (P T : Finset ℕ) (k K : ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p)
    (hT : ∀ S : Finset ℕ, S ⊆ P → S.card = k → (∏ p ∈ S, (p - 1)) ∈ T)
    (hcount : T.card * K < Nat.choose P.card k) :
    ∃ (n : ℕ) (S : Finset ℕ), n ∈ T ∧ S ⊆ P ∧ S.card = k ∧
      (∏ p ∈ S, (p - 1)) = n ∧ K < {m : ℕ | Nat.totient m = n}.ncard := by
  classical
  have hmaps : ∀ S ∈ P.powersetCard k, (∏ p ∈ S, (p - 1)) ∈ T := by
    intro S hS
    exact hT S (Finset.mem_powersetCard.mp hS).1 (Finset.mem_powersetCard.mp hS).2
  obtain ⟨n, hnT, hn⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    hmaps (by simpa only [Finset.card_powersetCard] using hcount)
  have hnonempty :
      ((P.powersetCard k).filter (fun S => (∏ p ∈ S, (p - 1)) = n)).Nonempty :=
    Finset.card_pos.mp (lt_of_le_of_lt (Nat.zero_le K) hn)
  obtain ⟨S, hS⟩ := hnonempty
  obtain ⟨hSP, hSn⟩ := Finset.mem_filter.mp hS
  obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hSP
  exact ⟨n, S, hnT, hsub, hcard, hSn,
    lt_of_lt_of_le hn (card_shift_product_fiber_le_totient_fiber P k n hP)⟩

/- ## Quantitative bounds for the chosen target -/

/-- An upper bound requiring only a common upper bound for the elements. -/
theorem shift_product_le_pow (S : Finset ℕ) (X : ℕ)
    (hX : ∀ p ∈ S, p ≤ X) : (∏ p ∈ S, (p - 1)) ≤ X ^ S.card := by
  apply Finset.prod_le_pow_card
  intro p hp
  exact (Nat.sub_le p 1).trans (hX p hp)

/-- If every prime exceeds 2, every shifted factor is at least 2. -/
theorem two_pow_card_le_shift_product (S : Finset ℕ)
    (hS : ∀ p ∈ S, 2 < p) : 2 ^ S.card ≤ ∏ p ∈ S, (p - 1) := by
  apply Finset.pow_card_le_prod
  intro p hp
  have := hS p hp
  omega

/-- Allowing the prime 2 loses at most one factor of 2 in the lower bound.
The exponent is natural subtraction, so this also covers the empty finset. -/
theorem two_pow_card_sub_one_le_shift_product (S : Finset ℕ)
    (hS : ∀ p ∈ S, Nat.Prime p) : 2 ^ (S.card - 1) ≤ ∏ p ∈ S, (p - 1) := by
  have hcard : S.card - 1 ≤ (S.erase 2).card := by
    by_cases h2 : 2 ∈ S
    · rw [Finset.card_erase_of_mem h2]
    · rw [Finset.erase_eq_of_notMem h2]
      exact Nat.sub_le _ _
  calc
    2 ^ (S.card - 1) ≤ 2 ^ (S.erase 2).card :=
      Nat.pow_le_pow_right (by decide) hcard
    _ ≤ ∏ p ∈ S.erase 2, (p - 1) := by
      apply two_pow_card_le_shift_product
      intro p hp
      have hmem := Finset.mem_erase.mp hp
      have hprime := (hS p hmem.2).two_le
      omega
    _ = ∏ p ∈ S, (p - 1) :=
      Finset.prod_erase S (f := fun p : ℕ => p - 1) (a := 2) (by decide)

/-- **Main finite counting theorem.** There are `Nat.choose P.card k` distinct
squarefree inputs.  If their totients land in `T` and `T.card * K` is smaller than
this binomial count, some target in the stated range has more than `K` preimages.
This statement permits 2 in `P` and makes no asymptotic existence assertion. -/
theorem exists_large_totient_fiber
    (P T : Finset ℕ) (k K X : ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p)
    (hX : ∀ p ∈ P, p ≤ X)
    (hT : ∀ S : Finset ℕ, S ⊆ P → S.card = k → (∏ p ∈ S, (p - 1)) ∈ T)
    (hcount : T.card * K < Nat.choose P.card k) :
    ∃ n ∈ T, 2 ^ (k - 1) ≤ n ∧ n ≤ X ^ k ∧
      K < {m : ℕ | Nat.totient m = n}.ncard := by
  obtain ⟨n, S, hnT, hsub, hcard, hSn, hKn⟩ :=
    exists_large_totient_fiber_witness P T k K hP hT hcount
  refine ⟨n, hnT, ?_, ?_, hKn⟩
  · rw [← hSn, ← hcard]
    exact two_pow_card_sub_one_le_shift_product S (fun p hp => hP p (hsub hp))
  · rw [← hSn, ← hcard]
    exact shift_product_le_pow S X (fun p hp => hX p (hsub hp))

/-- The stronger lower bound when every prime in `P` exceeds 2. -/
theorem exists_large_totient_fiber_of_two_lt
    (P T : Finset ℕ) (k K X : ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p)
    (hodd : ∀ p ∈ P, 2 < p)
    (hX : ∀ p ∈ P, p ≤ X)
    (hT : ∀ S : Finset ℕ, S ⊆ P → S.card = k → (∏ p ∈ S, (p - 1)) ∈ T)
    (hcount : T.card * K < Nat.choose P.card k) :
    ∃ n ∈ T, 2 ^ k ≤ n ∧ n ≤ X ^ k ∧
      K < {m : ℕ | Nat.totient m = n}.ncard := by
  obtain ⟨n, S, hnT, hsub, hcard, hSn, hKn⟩ :=
    exists_large_totient_fiber_witness P T k K hP hT hcount
  refine ⟨n, hnT, ?_, ?_, hKn⟩
  · rw [← hSn, ← hcard]
    exact two_pow_card_le_shift_product S (fun p hp => hodd p (hsub hp))
  · rw [← hSn, ← hcard]
    exact shift_product_le_pow S X (fun p hp => hX p (hsub hp))


end Erdos821Counting

/-
# An elementary finite output bound for smooth numbers

For natural numbers `y` and `a`, the positive integers `n ≤ y ^ a` whose prime
factors are all at most `y` lie in an explicit finset of cardinality at most
`(a * y + 1) ^ y`. The finset is the image of all exponent vectors
`Fin y → Fin (a * y + 1)` under `e ↦ ∏ i, (i + 1) ^ e i`.

No estimates for the distribution of primes or smooth numbers are used.
The statements work for all natural `y`, and hence in particular for `2 ≤ y`.
The empty factorization includes `n = 1`, including when `a = 0`.

This independent auxiliary file imports only Mathlib. It neither imports nor
modifies a problem specification, and makes no claim to prove Erdős 821.
-/

set_option autoImplicit false

namespace Erdos821Counting

open Finset

/-- A finite target formed by allowing each base `1, ..., y` an exponent at most
`a * y`. The target is allowed to contain numbers larger than `y ^ a`. -/
def smoothOutputSet (y a : ℕ) : Finset ℕ :=
  Finset.univ.image (fun e : Fin y → Fin (a * y + 1) =>
    ∏ i : Fin y, ((i : ℕ) + 1) ^ (e i : ℕ))

/-- Counting exponent vectors gives the elementary cardinality bound. -/
theorem card_smoothOutputSet_le (y a : ℕ) :
    (smoothOutputSet y a).card ≤ (a * y + 1) ^ y := by
  classical
  calc
    (smoothOutputSet y a).card ≤
        (Finset.univ : Finset (Fin y → Fin (a * y + 1))).card :=
      Finset.card_image_le
    _ = (a * y + 1) ^ y := by simp

/-- Every prime-factorization exponent of `n ≤ y ^ a` is at most `a * y`.
For prime `p`, use `y ≤ 2 ^ y ≤ p ^ y` and compare powers of `p`;
for nonprime `p` the exponent is zero. Positivity of `n` is not needed here. -/
theorem factorization_le_mul_of_le_pow {n y a : ℕ} (hn : n ≤ y ^ a) (p : ℕ) :
    n.factorization p ≤ a * y := by
  by_cases hp : p.Prime
  · apply Nat.factorization_le_of_le_pow
    calc
      n ≤ y ^ a := hn
      _ ≤ (2 ^ y) ^ a := Nat.pow_le_pow_left (Nat.le_of_lt Nat.lt_two_pow_self) a
      _ ≤ (p ^ y) ^ a := Nat.pow_le_pow_left (Nat.pow_le_pow_left hp.two_le y) a
      _ = p ^ (a * y) := by rw [← pow_mul, Nat.mul_comm y a]
  · simp [Nat.factorization_eq_zero_of_not_prime n hp]

/-- If all prime factors of a nonzero number are at most `y`, extending its
prime-power product to all bases `1, ..., y` leaves the product unchanged. -/
theorem prod_factorization_fin_eq {n y : ℕ} (hn : n ≠ 0)
    (hsmooth : ∀ p ∈ n.primeFactors, p ≤ y) :
    (∏ i : Fin y, ((i : ℕ) + 1) ^ n.factorization ((i : ℕ) + 1)) = n := by
  have hs : n.factorization.support ⊆ Finset.range (y + 1) := by
    intro p hp
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hsmooth p hp))
  calc
    (∏ i : Fin y, ((i : ℕ) + 1) ^ n.factorization ((i : ℕ) + 1)) =
        ∏ p ∈ Finset.range y, (p + 1) ^ n.factorization (p + 1) :=
      Fin.prod_univ_eq_prod_range (fun p => (p + 1) ^ n.factorization (p + 1)) y
    _ = ∏ p ∈ Finset.range (y + 1), p ^ n.factorization p := by
      rw [Finset.prod_range_succ']
      simp
    _ = n.factorization.prod (fun p e => p ^ e) :=
      (n.factorization.prod_of_support_subset hs (fun p e => p ^ e)
        (by intros; simp)).symm
    _ = n := Nat.factorization_prod_pow_eq_self hn

/-- The explicit target contains every positive `y`-smooth number at most `y ^ a`.
Here `y`-smooth means that all prime factors are `≤ y`, not strictly less. -/
theorem mem_smoothOutputSet {n y a : ℕ} (hn : 0 < n) (hbound : n ≤ y ^ a)
    (hsmooth : ∀ p ∈ n.primeFactors, p ≤ y) : n ∈ smoothOutputSet y a := by
  classical
  let e : Fin y → Fin (a * y + 1) := fun i =>
    ⟨n.factorization ((i : ℕ) + 1),
      Nat.lt_succ_of_le (factorization_le_mul_of_le_pow hbound ((i : ℕ) + 1))⟩
  refine Finset.mem_image.mpr ⟨e, Finset.mem_univ _, ?_⟩
  exact prod_factorization_fin_eq hn.ne' hsmooth

/-- The all-zero exponent vector represents `1`, for every choice of parameters. -/
theorem one_mem_smoothOutputSet (y a : ℕ) : 1 ∈ smoothOutputSet y a := by
  classical
  refine Finset.mem_image.mpr ⟨fun _ => (0 : Fin (a * y + 1)), Finset.mem_univ _, ?_⟩
  simp

/-- Elementary output bound, stated with a single exponent parameter. -/
theorem exists_smooth_output_set_of_pow (y a : ℕ) :
    ∃ T : Finset ℕ, T.card ≤ (a * y + 1) ^ y ∧
      ∀ n : ℕ, 0 < n → n ≤ y ^ a →
        (∀ p ∈ n.primeFactors, p ≤ y) → n ∈ T := by
  exact ⟨smoothOutputSet y a, card_smoothOutputSet_le y a,
    fun _ hn hbound hsmooth => mem_smoothOutputSet hn hbound hsmooth⟩

/-- The requested elementary bound with exponent `r * k`. It holds even without
assuming `2 ≤ y`; in particular there is no loss from `y` to `y + 1`. -/
theorem exists_smooth_output_set (y r k : ℕ) :
    ∃ T : Finset ℕ, T.card ≤ (r * k * y + 1) ^ y ∧
      ∀ n : ℕ, 0 < n → n ≤ y ^ (r * k) →
        (∀ p ∈ n.primeFactors, p ≤ y) → n ∈ T :=
  exists_smooth_output_set_of_pow y (r * k)

/- ## Products of shifted primes -/

/-- A product of `p - 1` over primes bounded by `y ^ a` belongs to the explicit
smooth target with exponent parameter `a * S.card`, provided each prime divisor
of each `p - 1` is at most `y`. This includes the prime `2` and the empty product. -/
theorem shift_product_mem_smoothOutputSet (S : Finset ℕ) (y a : ℕ)
    (hS : ∀ p ∈ S, Nat.Prime p)
    (hbound : ∀ p ∈ S, p ≤ y ^ a)
    (hsmooth : ∀ p ∈ S, ∀ q : ℕ, Nat.Prime q → q ∣ p - 1 → q ≤ y) :
    (∏ p ∈ S, (p - 1)) ∈ smoothOutputSet y (a * S.card) := by
  apply mem_smoothOutputSet
  · exact Finset.prod_pos fun p hp => Nat.sub_pos_of_lt (hS p hp).one_lt
  · calc
      (∏ p ∈ S, (p - 1)) ≤ (y ^ a) ^ S.card :=
        Finset.prod_le_pow_card S (fun p => p - 1) (y ^ a)
          (fun p hp => (Nat.sub_le p 1).trans (hbound p hp))
      _ = y ^ (a * S.card) := (pow_mul y a S.card).symm
  · intro q hq
    have hqprime := Nat.prime_of_mem_primeFactors hq
    obtain ⟨p, hp, hdiv⟩ :=
      (hqprime.prime.dvd_finset_prod_iff (fun p : ℕ => p - 1)).mp
        (Nat.dvd_of_mem_primeFactors hq)
    exact hsmooth p hp q hqprime hdiv

/-- A common finite target for all shifted products over `k`-subsets of `P`,
assuming a general prime bound `p ≤ y ^ a`. The target depends only on `y, a, k`.
The conclusion is in the form required by the finite pigeonhole theorem. -/
theorem exists_shift_product_output_set_of_pow (P : Finset ℕ) (y a k : ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p)
    (hbound : ∀ p ∈ P, p ≤ y ^ a)
    (hsmooth : ∀ p ∈ P, ∀ q : ℕ, Nat.Prime q → q ∣ p - 1 → q ≤ y) :
    ∃ T : Finset ℕ, T.card ≤ (a * k * y + 1) ^ y ∧
      ∀ S : Finset ℕ, S ⊆ P → S.card = k → (∏ p ∈ S, (p - 1)) ∈ T := by
  refine ⟨smoothOutputSet y (a * k), card_smoothOutputSet_le y (a * k), ?_⟩
  intro S hsub hcard
  simpa only [hcard] using shift_product_mem_smoothOutputSet S y a
    (fun p hp => hP p (hsub hp))
    (fun p hp => hbound p (hsub hp))
    (fun p hp => hsmooth p (hsub hp))

/-- The requested shifted-prime corollary for primes `p ≤ y ^ (r + 1)`.
No assumption `2 ≤ y` is needed, and the outer exponent remains exactly `y`. -/
theorem exists_shift_product_output_set (P : Finset ℕ) (y r k : ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p)
    (hbound : ∀ p ∈ P, p ≤ y ^ (r + 1))
    (hsmooth : ∀ p ∈ P, ∀ q : ℕ, Nat.Prime q → q ∣ p - 1 → q ≤ y) :
    ∃ T : Finset ℕ, T.card ≤ ((r + 1) * k * y + 1) ^ y ∧
      ∀ S : Finset ℕ, S ⊆ P → S.card = k → (∏ p ∈ S, (p - 1)) ∈ T :=
  exists_shift_product_output_set_of_pow P y (r + 1) k hP hbound hsmooth

/-- The same corollary, with smoothness expressed using `Nat.primeFactors`. -/
theorem exists_shift_product_output_set_of_primeFactors (P : Finset ℕ) (y r k : ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p)
    (hbound : ∀ p ∈ P, p ≤ y ^ (r + 1))
    (hsmooth : ∀ p ∈ P, ∀ q ∈ (p - 1).primeFactors, q ≤ y) :
    ∃ T : Finset ℕ, T.card ≤ ((r + 1) * k * y + 1) ^ y ∧
      ∀ S : Finset ℕ, S ⊆ P → S.card = k → (∏ p ∈ S, (p - 1)) ∈ T := by
  apply exists_shift_product_output_set P y r k hP hbound
  intro p hp q hq hdiv
  exact hsmooth p hp q (Nat.mem_primeFactors.mpr
    ⟨hq, hdiv, (Nat.sub_pos_of_lt (hP p hp).one_lt).ne'⟩)

/-- Consequently, the actual image of the `k`-subsets under shifted product
satisfies the same bound. No existence or density of such prime sets is asserted. -/
theorem card_shift_product_image_le (P : Finset ℕ) (y r k : ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p)
    (hbound : ∀ p ∈ P, p ≤ y ^ (r + 1))
    (hsmooth : ∀ p ∈ P, ∀ q : ℕ, Nat.Prime q → q ∣ p - 1 → q ≤ y) :
    ((P.powersetCard k).image (fun S => ∏ p ∈ S, (p - 1))).card ≤
      ((r + 1) * k * y + 1) ^ y := by
  obtain ⟨T, hcard, hmem⟩ := exists_shift_product_output_set P y r k hP hbound hsmooth
  apply le_trans (Finset.card_le_card (show
    (P.powersetCard k).image (fun S => ∏ p ∈ S, (p - 1)) ⊆ T from ?_)) hcard
  intro n hn
  obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hn
  obtain ⟨hsub, hsize⟩ := Finset.mem_powersetCard.mp hS
  exact hmem S hsub hsize


end Erdos821Counting

/-
# Conditional finite counting inequalities

These elementary inequalities compare a binomial coefficient with powers of
natural numbers. The hypothesis `y ^ r ≤ N` is an explicit assumption; this
file makes no assertion about actual prime counts or about Erdős 821.

Only Mathlib is imported. No problem specification is imported or modified.
-/

set_option autoImplicit false

namespace Erdos821Counting

/-- A crude binomial lower bound for `k = y ^ 2`. In fact, `y ≥ 2` suffices;
neither `y ≥ 6` nor `r + 1 ≤ y` is needed for this inequality. -/
theorem choose_square_lower_bound {N r y : ℕ} (hr : 4 ≤ r) (hy : 2 ≤ y)
    (hN : y ^ r ≤ N) :
    y ^ ((r - 3) * y ^ 2) ≤ Nat.choose N (y ^ 2) := by
  have hypos : 0 < y := by omega
  have hsquare : y ^ 2 ≤ y ^ (r - 1) :=
    Nat.pow_le_pow_right hypos (by omega)
  have hsum : y ^ (r - 1) + y ^ 2 ≤ N + 1 := by
    calc
      y ^ (r - 1) + y ^ 2 ≤ y ^ (r - 1) + y ^ (r - 1) :=
        Nat.add_le_add_left hsquare _
      _ = y ^ (r - 1) * 2 := by ring
      _ ≤ y ^ (r - 1) * y := Nat.mul_le_mul_left _ hy
      _ = y ^ r := by
        rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ r)]
      _ ≤ N + 1 := Nat.le_succ_of_le hN
  have hbase : y ^ (r - 1) ≤ N + 1 - y ^ 2 :=
    Nat.le_sub_of_add_le hsum
  have hdesc : y ^ ((r - 1) * y ^ 2) ≤
      (y ^ 2).factorial * Nat.choose N (y ^ 2) := by
    calc
      y ^ ((r - 1) * y ^ 2) = (y ^ (r - 1)) ^ (y ^ 2) := pow_mul _ _ _
      _ ≤ (N + 1 - y ^ 2) ^ (y ^ 2) := Nat.pow_le_pow_left hbase _
      _ ≤ N.descFactorial (y ^ 2) := Nat.pow_sub_le_descFactorial _ _
      _ = (y ^ 2).factorial * Nat.choose N (y ^ 2) :=
        Nat.descFactorial_eq_factorial_mul_choose _ _
  have hfactorial : (y ^ 2).factorial ≤ y ^ (2 * y ^ 2) := by
    calc
      (y ^ 2).factorial ≤ (y ^ 2) ^ (y ^ 2) := Nat.factorial_le_pow _
      _ = y ^ (2 * y ^ 2) := (pow_mul _ _ _).symm
  have hexp : 2 + (r - 3) = r - 1 := by omega
  have hmul : y ^ (2 * y ^ 2) * y ^ ((r - 3) * y ^ 2) ≤
      y ^ (2 * y ^ 2) * Nat.choose N (y ^ 2) := by
    calc
      y ^ (2 * y ^ 2) * y ^ ((r - 3) * y ^ 2) =
          y ^ ((r - 1) * y ^ 2) := by
        rw [← pow_add, ← Nat.add_mul, hexp]
      _ ≤ (y ^ 2).factorial * Nat.choose N (y ^ 2) := hdesc
      _ ≤ y ^ (2 * y ^ 2) * Nat.choose N (y ^ 2) :=
        Nat.mul_le_mul_right _ hfactorial
  exact Nat.le_of_mul_le_mul_left hmul (Nat.pow_pos hypos)

/-- The base of the finite-output estimate is at most `y ^ 5`. -/
theorem output_base_le_pow_five {r y : ℕ} (hry : r + 1 ≤ y) (hy : 2 ≤ y) :
    (r + 1) * y ^ 2 * y + 1 ≤ y ^ 5 := by
  have hypos : 0 < y := by omega
  have hfour : 1 ≤ y ^ 4 := Nat.pow_pos hypos
  have hcoeff : (r + 1) * y ^ 2 * y ≤ y ^ 4 := by
    calc
      (r + 1) * y ^ 2 * y ≤ y * y ^ 2 * y :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hry)
      _ = y ^ 4 := by ring
  calc
    (r + 1) * y ^ 2 * y + 1 ≤ y ^ 4 + 1 := Nat.add_le_add_right hcoeff _
    _ ≤ y ^ 4 + y ^ 4 := Nat.add_le_add_left hfour _
    _ = y ^ 4 * 2 := by ring
    _ ≤ y ^ 4 * y := Nat.mul_le_mul_left _ hy
    _ = y ^ 5 := by ring

/-- Raising the base estimate to the `y`-th power gives the output bound. -/
theorem output_bound_le_pow {r y : ℕ} (hry : r + 1 ≤ y) (hy : 2 ≤ y) :
    ((r + 1) * y ^ 2 * y + 1) ^ y ≤ y ^ (5 * y) := by
  calc
    ((r + 1) * y ^ 2 * y + 1) ^ y ≤ (y ^ 5) ^ y :=
      Nat.pow_le_pow_left (output_base_le_pow_five hry hy) _
    _ = y ^ (5 * y) := (pow_mul _ _ _).symm

/-- For `y ≥ 6`, the exponent gap is strict, including at `y = 6`. -/
theorem five_mul_lt_square {y : ℕ} (hy : 6 ≤ y) : 5 * y < y ^ 2 := by
  calc
    5 * y < 6 * y := Nat.mul_lt_mul_of_pos_right (by decide) (by omega)
    _ ≤ y * y := Nat.mul_le_mul_right _ hy
    _ = y ^ 2 := (pow_two _).symm

/-- The final strict counting inequality, conditional on `y ^ r ≤ N`. -/
theorem output_bound_mul_pow_lt_choose {N r y : ℕ} (hr : 4 ≤ r)
    (hy : 6 ≤ y) (hry : r + 1 ≤ y) (hN : y ^ r ≤ N) :
    (((r + 1) * y ^ 2 * y + 1) ^ y) * y ^ ((r - 4) * y ^ 2) <
      Nat.choose N (y ^ 2) := by
  have hypos : 0 < y := by omega
  have hexp : 1 + (r - 4) = r - 3 := by omega
  calc
    (((r + 1) * y ^ 2 * y + 1) ^ y) * y ^ ((r - 4) * y ^ 2) ≤
        y ^ (5 * y) * y ^ ((r - 4) * y ^ 2) :=
      Nat.mul_le_mul_right _ (output_bound_le_pow hry (by omega))
    _ < y ^ (y ^ 2) * y ^ ((r - 4) * y ^ 2) :=
      Nat.mul_lt_mul_of_pos_right
        (Nat.pow_lt_pow_right (by omega) (five_mul_lt_square hy))
        (Nat.pow_pos hypos)
    _ = y ^ ((r - 3) * y ^ 2) := by
      rw [← pow_add]
      congr 1
      calc
        y ^ 2 + (r - 4) * y ^ 2 = (1 + (r - 4)) * y ^ 2 := by ring
        _ = (r - 3) * y ^ 2 := by rw [hexp]
    _ ≤ Nat.choose N (y ^ 2) := choose_square_lower_bound hr (by omega) hN

/-- The same final bound using the single hypothesis `max (r + 1) 6 ≤ y`. -/
theorem output_bound_mul_pow_lt_choose_of_max {N r y : ℕ} (hr : 4 ≤ r)
    (hy : max (r + 1) 6 ≤ y) (hN : y ^ r ≤ N) :
    (((r + 1) * y ^ 2 * y + 1) ^ y) * y ^ ((r - 4) * y ^ 2) <
      Nat.choose N (y ^ 2) :=
  output_bound_mul_pow_lt_choose hr ((le_max_right _ _).trans hy)
    ((le_max_left _ _).trans hy) hN

end Erdos821Counting

/-
A fully formal reduction of the exact Erdős 821 conclusion to an explicit
prime-counting hypothesis. The hypothesis is not asserted or admitted here.
This file neither imports nor changes Submission/Spec.lean.
-/

set_option autoImplicit false

namespace Erdos821Counting

/-- For each fixed power parameter there are arbitrarily large scales with
many primes having smooth predecessors. This is an explicit hypothesis,
not an unconditional theorem. -/
def SmoothPrimeHypothesis : Prop :=
  ∀ r B : ℕ, ∃ y : ℕ, B ≤ y ∧ ∃ P : Finset ℕ,
    (∀ p ∈ P, Nat.Prime p) ∧
    (∀ p ∈ P, p ≤ y ^ (r + 1)) ∧
    (∀ p ∈ P, ∀ q ∈ (p - 1).primeFactors, q ≤ y) ∧
    y ^ r ≤ P.card

/-- The elementary combinatorial construction at a single scale. -/
theorem large_fiber_of_many_smooth_shifted_primes
    {P : Finset ℕ} {y r : ℕ}
    (hr : 4 ≤ r) (hy : 6 ≤ y) (hry : r + 1 ≤ y)
    (hP : ∀ p ∈ P, Nat.Prime p)
    (hbound : ∀ p ∈ P, p ≤ y ^ (r + 1))
    (hsmooth : ∀ p ∈ P, ∀ q ∈ (p - 1).primeFactors, q ≤ y)
    (hcount : y ^ r ≤ P.card) :
    ∃ n : ℕ, 2 ^ (y ^ 2 - 1) ≤ n ∧ n ≤ y ^ ((r + 1) * y ^ 2) ∧
      y ^ ((r - 4) * y ^ 2) < {m : ℕ | Nat.totient m = n}.ncard := by
  obtain ⟨T, hTcard, hT⟩ :=
    exists_shift_product_output_set_of_primeFactors P y r (y ^ 2) hP hbound hsmooth
  have hnum : T.card * y ^ ((r - 4) * y ^ 2) < P.card.choose (y ^ 2) :=
    (Nat.mul_le_mul_right _ hTcard).trans_lt
      (output_bound_mul_pow_lt_choose hr hy hry hcount)
  obtain ⟨n, _, hnlow, hnup, hng⟩ := exists_large_totient_fiber
    P T (y ^ 2) (y ^ ((r - 4) * y ^ 2)) (y ^ (r + 1)) hP hbound hT hnum
  exact ⟨n, hnlow, by simpa only [← pow_mul] using hnup, hng⟩

/-- Real-power comparison used to turn the discrete exponent into the requested
exponent `1 - ε`. -/
theorem target_rpow_le_counting_power {ε : ℝ} {r y n : ℕ}
    (hr : 4 ≤ r) (hy : 1 ≤ y) (hε : ε ≤ 1)
    (hexp : 5 ≤ ((r : ℝ) + 1) * ε)
    (hn : n ≤ y ^ ((r + 1) * y ^ 2)) :
    (n : ℝ) ^ (1 - ε) ≤ (y ^ ((r - 4) * y ^ 2) : ℕ) := by
  have hbase : 1 ≤ (y : ℝ) := by exact_mod_cast hy
  have hcoeff : ((r : ℝ) + 1) * (1 - ε) ≤ (r : ℝ) - 4 := by nlinarith
  have hpower : (((r + 1) * y ^ 2 : ℕ) : ℝ) * (1 - ε) ≤
      (((r - 4) * y ^ 2 : ℕ) : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hr]
    push_cast
    nlinarith [mul_le_mul_of_nonneg_right hcoeff (sq_nonneg (y : ℝ))]
  calc
    (n : ℝ) ^ (1 - ε) ≤ ((y ^ ((r + 1) * y ^ 2) : ℕ) : ℝ) ^ (1 - ε) :=
      Real.rpow_le_rpow (Nat.cast_nonneg n) (by exact_mod_cast hn) (by linarith)
    _ = (y : ℝ) ^ ((((r + 1) * y ^ 2 : ℕ) : ℝ) * (1 - ε)) := by
      rw [Nat.cast_pow, Real.rpow_natCast_mul (Nat.cast_nonneg y)]
    _ ≤ (y : ℝ) ^ ((((r - 4) * y ^ 2 : ℕ) : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hbase hpower
    _ = (y ^ ((r - 4) * y ^ 2) : ℕ) := by
      rw [Real.rpow_natCast, Nat.cast_pow]

/-- The exact quantified conclusion of Erdős 821 follows from the displayed
hypothesis. No statement about that hypothesis's truth is used or proved. -/
theorem erdos821_of_smooth_prime_hypothesis (h : SmoothPrimeHypothesis) :
    ∀ ε > (0 : ℝ),
      {n : ℕ | ({m : ℕ | Nat.totient m = n}.ncard : ℝ) >
        (n : ℝ) ^ (1 - ε)}.Infinite := by
  intro ε hε
  obtain ⟨r, hr⟩ := exists_nat_gt (max (4 : ℝ) (5 / ε))
  have hr4 : 4 ≤ r := by
    have : (4 : ℝ) < r := (le_max_left _ _).trans_lt hr
    exact_mod_cast this.le
  have hexp : 5 ≤ ((r : ℝ) + 1) * ε := by
    have hdiv : 5 / ε < (r : ℝ) := (le_max_right _ _).trans_lt hr
    have hmul := (div_lt_iff₀ hε).mp hdiv
    nlinarith
  apply Set.infinite_of_forall_exists_gt
  intro B
  obtain ⟨y, hy, P, hP, hbound, hsmooth, hcount⟩ := h r (max (max (r + 1) 6) B)
  have hy6 : 6 ≤ y := (le_max_right (r + 1) 6).trans
    ((le_max_left _ B).trans hy)
  have hry : r + 1 ≤ y := (le_max_left (r + 1) 6).trans
    ((le_max_left _ B).trans hy)
  have hBy : B ≤ y := (le_max_right _ _).trans hy
  obtain ⟨n, hnlow, hnup, hng⟩ :=
    large_fiber_of_many_smooth_shifted_primes hr4 hy6 hry hP hbound hsmooth hcount
  have hyn : y < n := by
    have hysquare : y ≤ y ^ 2 - 1 := by
      have : y + 1 ≤ y ^ 2 := by nlinarith
      omega
    exact (Nat.lt_two_pow_self.trans_le
      ((Nat.pow_le_pow_right (by decide) hysquare).trans hnlow))
  refine ⟨n, ?_, hBy.trans_lt hyn⟩
  change (n : ℝ) ^ (1 - ε) < ({m : ℕ | Nat.totient m = n}.ncard : ℝ)
  have hng' : ((y ^ ((r - 4) * y ^ 2) : ℕ) : ℝ) <
      ({m : ℕ | Nat.totient m = n}.ncard : ℝ) := by exact_mod_cast hng
  apply lt_of_le_of_lt _ hng'
  by_cases hε1 : ε ≤ 1
  · exact target_rpow_le_counting_power hr4 (by omega) hε1 hexp hnup
  · have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
    have hK : (1 : ℝ) ≤ ((y ^ ((r - 4) * y ^ 2) : ℕ) : ℝ) := by
      exact_mod_cast Nat.one_le_pow ((r - 4) * y ^ 2) y (by omega)
    exact (Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith)).trans hK


end Erdos821Counting

set_option autoImplicit false

namespace Erdos821Counting

/-- A completely explicit pair of distinct preimages of every positive power
of two. This is an unconditional lower bound, not a near-linear one. -/
theorem two_le_fiber_of_power_two (b : ℕ) :
    2 ≤ {m : ℕ | Nat.totient m = 2 ^ (b + 1)}.ncard := by
  have h₁ : Nat.totient (2 ^ (b + 2)) = 2 ^ (b + 1) := by
    simp only [show b + 2 = (b + 1) + 1 by omega,
      Nat.totient_prime_pow_succ Nat.prime_two, Nat.reduceSub, mul_one]
  have h₂ : Nat.totient (3 * 2 ^ (b + 1)) = 2 ^ (b + 1) := by
    rw [Nat.totient_mul ((by decide : Nat.Coprime 3 2).pow_right (b + 1)),
      Nat.totient_prime Nat.prime_three, Nat.totient_prime_pow_succ Nat.prime_two]
    simp [pow_succ, Nat.mul_comm]
  have hne : 2 ^ (b + 2) ≠ 3 * 2 ^ (b + 1) := by
    have hpos : 0 < 2 ^ (b + 1) := by positivity
    rw [show b + 2 = (b + 1) + 1 by omega, pow_succ]
    nlinarith
  have hsub : ({2 ^ (b + 2), 3 * 2 ^ (b + 1)} : Set ℕ) ⊆
      {m : ℕ | Nat.totient m = 2 ^ (b + 1)} := by
    intro m hm
    rcases Set.mem_insert_iff.mp hm with rfl | hm
    · exact h₁
    · have hm' : m = 3 * 2 ^ (b + 1) := Set.mem_singleton_iff.mp hm
      simpa only [hm'] using h₂
  have hcard := Set.ncard_le_ncard hsub (totient_fiber_finite (2 ^ (b + 1)))
  simpa only [Set.ncard_pair hne] using hcard

/-- The conjecture's conclusion for the elementary range `ε ≥ 1`.
The unresolved part requires every arbitrarily small positive `ε`. -/
theorem infinite_large_fibers_of_one_le {ε : ℝ} (hε : 1 ≤ ε) :
    {n : ℕ | ({m : ℕ | Nat.totient m = n}.ncard : ℝ) >
      (n : ℝ) ^ (1 - ε)}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro B
  refine ⟨2 ^ (B + 1), ?_, ?_⟩
  · change ((2 ^ (B + 1) : ℕ) : ℝ) ^ (1 - ε) <
      ({m : ℕ | Nat.totient m = 2 ^ (B + 1)}.ncard : ℝ)
    have hbase : (1 : ℝ) ≤ ((2 ^ (B + 1) : ℕ) : ℝ) := by
      exact_mod_cast Nat.one_le_pow (B + 1) 2 (by decide)
    have hcard : (2 : ℝ) ≤
        ({m : ℕ | Nat.totient m = 2 ^ (B + 1)}.ncard : ℝ) := by
      exact_mod_cast two_le_fiber_of_power_two B
    exact (Real.rpow_le_one_of_one_le_of_nonpos hbase (by linarith)).trans_lt
      (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) hcard)
  · exact (Nat.lt_succ_self B).trans Nat.lt_two_pow_self


end Erdos821Counting

#print axioms Erdos821Counting.erdos821_of_smooth_prime_hypothesis
#print axioms Erdos821Counting.infinite_large_fibers_of_one_le
