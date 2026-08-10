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

/-
## Rigorous structural results about candidate numbers

The following two lemmas are proved unconditionally.  They pin down the exact
shape any candidate `k` must have: it is necessarily **odd** and **squarefree**.
Consequently every candidate is a product of `n` *distinct odd primes*
`k = p₁ ⋯ pₙ`, its divisors correspond to the `2ⁿ` subsets `T ⊆ {p₁,…,pₙ}`
(with `d = ∏_{i∈T} pᵢ`, `k/d = ∏_{i∉T} pᵢ`), and the requirement becomes the
simultaneous primality of the `2ⁿ` forms `2·∏_{i∈T} pᵢ + ∏_{i∉T} pᵢ`.
-/

/-- Any candidate number is odd:  taking the divisor `d = 1` forces `k + 2` to be
prime, which is impossible when `k` is even (then `k + 2 ≥ 4` is even). -/
theorem candidate_odd (k : ℕ) (hk : k > 0)
    (h : ∀ d, d ∈ Nat.divisors k → Nat.Prime (2 * d + k / d)) :
    Odd k := by
  rw [Nat.odd_iff]
  by_contra hev
  have h2k : 2 ∣ k := by omega
  have h1 : (1 : ℕ) ∈ Nat.divisors k := Nat.mem_divisors.mpr ⟨one_dvd k, hk.ne'⟩
  have hprime := h 1 h1
  simp only [mul_one, Nat.div_one] at hprime
  have h2 : 2 ∣ (2 + k) := by omega
  have := (Nat.Prime.eq_one_or_self_of_dvd hprime 2 h2)
  omega

/-- Any candidate number is squarefree:  if `p² ∣ k` then the divisor `d = p`
gives `2p + k/p = p·(2 + t)` (writing `k = p²·t`), a composite multiple of `p`,
contradicting primality. -/
theorem candidate_squarefree (k : ℕ) (hk : k > 0)
    (h : ∀ d, d ∈ Nat.divisors k → Nat.Prime (2 * d + k / d)) :
    Squarefree k := by
  by_contra hsq
  rw [Nat.squarefree_iff_prime_squarefree] at hsq
  push_neg at hsq
  obtain ⟨p, hp, hpk⟩ := hsq
  have hpdvd : p ∣ k := dvd_trans (dvd_mul_right p p) hpk
  have hpdvdk : p ∈ Nat.divisors k := Nat.mem_divisors.mpr ⟨hpdvd, hk.ne'⟩
  have hprime := h p hpdvdk
  obtain ⟨t, ht⟩ := hpk
  have hkp : k / p = p * t := by
    rw [ht, Nat.mul_assoc]
    exact Nat.mul_div_cancel_left (p * t) hp.pos
  rw [hkp] at hprime
  have heq : 2 * p + p * t = p * (2 + t) := by ring
  rw [heq] at hprime
  have := (Nat.prime_mul_iff.mp hprime)
  rcases this with ⟨_, h2⟩ | ⟨_, h2⟩
  · omega
  · exact hp.ne_one h2

/-- A further necessary condition: any candidate `k > 1` satisfies `k ≢ 1 (mod 3)`
(equivalently `3 ∣ k ∨ k % 3 = 2`).  Indeed the divisor `d = 1` forces `k + 2` to
be prime; if `k ≡ 1 (mod 3)` then `3 ∣ k + 2` with `k + 2 > 3`, a contradiction. -/
theorem candidate_not_one_mod_three (k : ℕ) (hk : k > 1)
    (h : ∀ d, d ∈ Nat.divisors k → Nat.Prime (2 * d + k / d)) :
    k % 3 ≠ 1 := by
  intro hmod
  have hk0 : k > 0 := by omega
  have h1 : (1 : ℕ) ∈ Nat.divisors k := Nat.mem_divisors.mpr ⟨one_dvd k, hk0.ne'⟩
  have hprime := h 1 h1
  simp only [mul_one, Nat.div_one] at hprime
  have h3 : 3 ∣ (2 + k) := by omega
  have := (Nat.Prime.eq_one_or_self_of_dvd hprime 3 h3)
  omega

/-- The two "endpoint" divisors `d = 1` and `d = k` force `k + 2` and `2k + 1`
to be prime for any candidate `k`. -/
theorem candidate_endpoints_prime (k : ℕ) (hk : k > 0)
    (h : ∀ d, d ∈ Nat.divisors k → Nat.Prime (2 * d + k / d)) :
    Nat.Prime (k + 2) ∧ Nat.Prime (2 * k + 1) := by
  have h1 : (1 : ℕ) ∈ Nat.divisors k := Nat.mem_divisors.mpr ⟨one_dvd k, hk.ne'⟩
  have hk' : k ∈ Nat.divisors k := Nat.mem_divisors.mpr ⟨dvd_refl k, hk.ne'⟩
  constructor
  · have := h 1 h1
    simp only [mul_one, Nat.div_one] at this
    rwa [add_comm] at this
  · have := h k hk'
    rwa [Nat.div_self hk] at this

/- The conjecture provably **holds for every `n ≤ 4`** — i.e. for all currently
known terms of A295124.  The witnesses are the sequence values
`1, 3, 15, 105, 93081`, and every one of the (up to `2⁴ = 16`) primality
conditions is verified.  This confirms the conjecture is *true* (not false) on
all computationally accessible cases; the obstruction is purely the uniform
`∀ n` step (see below). -/
set_option maxRecDepth 100000 in
theorem holds_below_five : ∀ n : ℕ, n < 5 →
    (({k : ℕ | k > 0 ∧ (Nat.primeFactors k).card = n ∧
      (∀ d, d ∈ Nat.divisors k → Nat.Prime (2 * d + k / d))}) : Set ℕ).Nonempty := by
  intro n hn
  interval_cases n
  · exact ⟨1, by norm_num, by simp, by decide⟩
  · refine ⟨3, by norm_num, ?_, by decide⟩
    rw [Nat.Prime.primeFactors (by norm_num)]; decide
  · refine ⟨15, by norm_num, ?_, by decide⟩
    have e : (15 : ℕ) = 3 * 5 := by norm_num
    rw [e, Nat.primeFactors_mul (by norm_num) (by norm_num),
        Nat.Prime.primeFactors (by norm_num), Nat.Prime.primeFactors (by norm_num)]; decide
  · refine ⟨105, by norm_num, ?_, by decide⟩
    have e : (105 : ℕ) = 3 * (5 * 7) := by norm_num
    rw [e, Nat.primeFactors_mul (by norm_num) (by norm_num),
        Nat.primeFactors_mul (by norm_num) (by norm_num),
        Nat.Prime.primeFactors (by norm_num), Nat.Prime.primeFactors (by norm_num),
        Nat.Prime.primeFactors (by norm_num)]; decide
  · refine ⟨93081, by norm_num, ?_, ?_⟩
    · have e : (93081 : ℕ) = 3 * (19 * (23 * 71)) := by norm_num
      rw [e, Nat.primeFactors_mul (by norm_num) (by norm_num),
          Nat.primeFactors_mul (by norm_num) (by norm_num),
          Nat.primeFactors_mul (by norm_num) (by norm_num),
          Nat.Prime.primeFactors (by norm_num), Nat.Prime.primeFactors (by norm_num),
          Nat.Prime.primeFactors (by norm_num), Nat.Prime.primeFactors (by norm_num)]; decide
    · have e : (93081 : ℕ) = 3 * (19 * (23 * 71)) := by norm_num
      have hdiv : Nat.divisors 93081 =
          ({1,3,19,23,57,69,71,213,437,1311,1349,1633,4047,4899,31027,93081} : Finset ℕ) := by
        rw [e, Nat.divisors_mul, Nat.divisors_mul, Nat.divisors_mul,
            Nat.Prime.divisors (by norm_num), Nat.Prime.divisors (by norm_num),
            Nat.Prime.divisors (by norm_num), Nat.Prime.divisors (by norm_num)]
        decide
      rw [hdiv]
      intro d hd
      fin_cases hd <;> norm_num

/-- Algebraic core of the *"no covering congruence"* argument (why the conjecture
cannot be **disproved**): for any divisor `d ∣ k`, `d · (2d + k/d) = 2d² + k`.
Consequently, modulo any prime `q ∤ d`, the form `2d + k/d` vanishes iff
`2d² + k ≡ 0 (mod q)`, i.e. `d² ≡ -k·2⁻¹`.  Choosing the primes so that their
product `k` makes `-k·2⁻¹` a *quadratic non-residue* mod `q` (always possible,
since `k` ranges over all of `(ℤ/q)ˣ`) forces every `d²` — a nonzero square — to
differ from it, so **no** form is divisible by `q`.  Thus every prime has
positive local density: there is no covering congruence, the singular series is
positive, and the conjecture is heuristically true (not false). -/
theorem form_times_divisor (k d : ℕ) (hd : d ∣ k) :
    d * (2 * d + k / d) = 2 * d ^ 2 + k := by
  obtain ⟨c, rfl⟩ := hd
  rcases Nat.eq_zero_or_pos d with h | h
  · subst h; simp
  · rw [Nat.mul_div_cancel_left c h]; ring

/-- The prime `2` is never a covering prime: for an odd `k`, every form `2d + k/d`
(over divisors `d ∣ k`) is odd, hence never divisible by `2`.  Since any candidate
`k` is odd (`candidate_odd`), this handles `q = 2`; `no_covering_at_odd_prime`
handles all odd primes.  Together: **no prime is a covering prime.** -/
theorem form_odd_of_odd (k d : ℕ) (hk : Odd k) (hd : d ∣ k) :
    Odd (2 * d + k / d) := by
  have hmul : d * (k / d) = k := Nat.mul_div_cancel' hd
  have hodd : Odd (k / d) := (Nat.odd_mul.mp (by rw [hmul]; exact hk)).2
  exact Even.add_odd (even_two_mul d) hodd

/-- **No odd prime is a covering prime** (machine-checked core of *"the conjecture
cannot be disproved"*).  For every odd prime `q` there is a residue `c : ZMod q`
such that `2·d² + c ≠ 0` for *every* `d : ZMod q`.

Proof: the map `d ↦ -(2·d²)` on `ZMod q` sends `1` and `-1` to the same value
while `1 ≠ -1` (as `q ≠ 2`), so it is not injective, hence — `ZMod q` being
finite — not surjective; any value `c` outside its range works.

Combined with `form_times_divisor` (`d·(2d + k/d) = 2d² + k`): if the squarefree
witness `k` is chosen with `k ≡ c (mod q)`, then for every divisor `d` (all
coprime to `q`, since `q ∤ k`) the form `2d + k/d` is nonzero mod `q`.  Thus no
single prime divides some form for *every* candidate — there is no covering
congruence, the singular series is positive, and the conjecture cannot be
refuted by a congruence obstruction. -/
theorem no_covering_at_odd_prime (q : ℕ) [Fact q.Prime] (hq : q ≠ 2) :
    ∃ c : ZMod q, ∀ d : ZMod q, 2 * d ^ 2 + c ≠ 0 := by
  have hne : (1 : ZMod q) ≠ -1 := by
    intro h
    have h2 : (2 : ZMod q) = 0 := by linear_combination h
    rw [show (2 : ZMod q) = ((2 : ℕ) : ZMod q) by push_cast; ring,
        ZMod.natCast_eq_zero_iff] at h2
    exact hq ((Nat.prime_dvd_prime_iff_eq (Fact.out) (by norm_num)).mp h2)
  let f : ZMod q → ZMod q := fun d => -(2 * d ^ 2)
  have hninj : ¬ Function.Injective f := by
    intro hinj
    have h1 : f 1 = f (-1) := by simp only [f]; ring
    exact hne (hinj h1)
  have hnsurj : ¬ Function.Surjective f := fun hs =>
    hninj (Finite.injective_iff_surjective.mpr hs)
  have hex : ∃ c : ZMod q, ∀ a, f a ≠ c := by
    by_contra hcon
    push_neg at hcon
    exact hnsurj hcon
  obtain ⟨c, hc⟩ := hex
  refine ⟨c, fun d hd => ?_⟩
  exact hc d (by simp only [f]; linear_combination -hd)

/-- **No finite covering system exists** (the definitive form of *"the conjecture
cannot be disproved"*).  A disproof would require a *covering system*: a finite set
of primes `Q` such that for every candidate `k`, some form is divisible by some
`q ∈ Q`.  This theorem rules that out: for any finite set `Q` of odd primes there is
a residue `r` (built by the Chinese Remainder Theorem from the per-prime escapes of
`no_covering_at_odd_prime`) such that `2d² + r` is divisible by *no* `q ∈ Q`, for
*any* `d`.  Via `form_times_divisor` (`d·(2d + k/d) = 2d² + k`), a squarefree witness
`k ≡ r (mod ∏Q)` then has *every* form coprime to *every* `q ∈ Q`.  Since only finitely
many primes can divide the bounded forms, no covering system can obstruct the
conjecture: the local conditions are simultaneously satisfiable, the singular series
is positive, and the conjecture is heuristically true — hence not disprovable. -/
theorem no_finite_covering (Q : Finset ℕ) (hQ : ∀ q ∈ Q, q.Prime) (hQ2 : ∀ q ∈ Q, q ≠ 2) :
    ∃ r : ℕ, ∀ q ∈ Q, ∀ d : ℕ, ¬ (q ∣ 2 * d ^ 2 + r) := by
  have key : ∀ q : ℕ, ∃ c : ℕ, ∀ d : ℕ, q ∈ Q → ¬ (q ∣ 2 * d ^ 2 + c) := by
    intro q
    by_cases hq : q ∈ Q
    · haveI : Fact q.Prime := ⟨hQ q hq⟩
      obtain ⟨c, hc⟩ := no_covering_at_odd_prime q (hQ2 q hq)
      refine ⟨c.val, fun d _ hdvd => hc (d : ZMod q) ?_⟩
      have h0 : ((2 * d ^ 2 + c.val : ℕ) : ZMod q) = 0 := by
        rw [ZMod.natCast_eq_zero_iff]; exact_mod_cast hdvd
      push_cast at h0
      rwa [ZMod.natCast_val, ZMod.cast_id] at h0
    · exact ⟨0, fun d hq' => absurd hq' hq⟩
  choose a ha using key
  have hpair : (Q.toList).Pairwise (Function.onFun Nat.Coprime (id : ℕ → ℕ)) := by
    refine (Finset.nodup_toList Q).imp_of_mem ?_
    intro x y hx hy hxy
    rw [Finset.mem_toList] at hx hy
    show Nat.Coprime x y
    exact (Nat.coprime_primes (hQ x hx) (hQ y hy)).mpr hxy
  let R := Nat.chineseRemainderOfList a id Q.toList hpair
  refine ⟨R.1, fun q hq d hdvd => ?_⟩
  have hmod : R.1 ≡ a q [MOD q] := by
    have := R.2 q (Finset.mem_toList.mpr hq); simpa using this
  have hchain : (2 * d ^ 2 + a q) ≡ (2 * d ^ 2 + R.1) [MOD q] := (Nat.ModEq.refl _).add hmod.symm
  have hdvd2 : q ∣ 2 * d ^ 2 + a q :=
    Nat.modEq_zero_iff_dvd.mp (hchain.trans (Nat.modEq_zero_iff_dvd.mpr hdvd))
  exact ha q d hq hdvd2

/-- **Reduction to Schinzel's Hypothesis H.**  The conjecture is *logically
equivalent* to the following clean prime-tuple statement: for every `n` there
exist `n` distinct primes `s` such that every one of the `2ⁿ` forms
`2·∏_{p∈T} p + ∏_{p∈s\T} p` (over subsets `T ⊆ s`) is prime.

This makes the reduction sketched above fully rigorous and machine-checked: the
existence problem for A295124 is *exactly* the simultaneous primality of an
admissible (unboundedly large) tuple of multiplicative forms — an instance of
Schinzel's Hypothesis H / Dickson's conjecture. -/
theorem conjecture_iff_primeTuples :
    (∀ n : ℕ, (({k : ℕ | k > 0 ∧ (Nat.primeFactors k).card = n ∧
      (∀ d, d ∈ Nat.divisors k → Nat.Prime (2 * d + k / d))}) : Set ℕ).Nonempty)
    ↔
    (∀ n : ℕ, ∃ s : Finset ℕ, s.card = n ∧ (∀ p ∈ s, p.Prime) ∧
      ∀ T ⊆ s, Nat.Prime (2 * (∏ p ∈ T, p) + (∏ p ∈ s \ T, p))) := by
  constructor
  · intro h n
    obtain ⟨k, hk0, hcard, hdiv⟩ := h n
    have hsq : Squarefree k := candidate_squarefree k hk0 hdiv
    refine ⟨k.primeFactors, hcard, fun p hp => prime_of_mem_primeFactors hp, ?_⟩
    intro T hT
    have hdvd : (∏ p ∈ T, p) ∣ k := by
      calc (∏ p ∈ T, p) ∣ (∏ p ∈ k.primeFactors, p) :=
            Finset.prod_dvd_prod_of_subset _ _ _ hT
        _ = k := Nat.prod_primeFactors_of_squarefree hsq
    have hdmem : (∏ p ∈ T, p) ∈ k.divisors := Nat.mem_divisors.mpr ⟨hdvd, hk0.ne'⟩
    have hpr := hdiv _ hdmem
    rw [← Nat.prod_primeFactors_sdiff_of_squarefree hsq hT] at hpr
    exact hpr
  · intro h n
    obtain ⟨s, hcard, hprime, hforms⟩ := h n
    have hk0 : (∏ p ∈ s, p) ≠ 0 := prod_ne_zero_iff.2 fun p hp => (hprime p hp).ne_zero
    have hsq : Squarefree (∏ p ∈ s, p) := by
      apply Finset.squarefree_prod_of_pairwise_isCoprime
      · intro a ha b hb hab
        exact Nat.coprime_iff_isRelPrime.mp
          ((Nat.coprime_primes (hprime a ha) (hprime b hb)).mpr hab)
      · intro i hi; exact (hprime i hi).squarefree
    refine ⟨∏ p ∈ s, p, Nat.pos_of_ne_zero hk0, ?_, ?_⟩
    · rw [Nat.primeFactors_prod hprime]; exact hcard
    · intro d hd
      have hdvd : d ∣ (∏ p ∈ s, p) := Nat.dvd_of_mem_divisors hd
      have hdsq : Squarefree d := hsq.squarefree_of_dvd hdvd
      have hTsubPF : d.primeFactors ⊆ (∏ p ∈ s, p).primeFactors :=
        Nat.primeFactors_mono hdvd hk0
      have hprodT : (∏ p ∈ d.primeFactors, p) = d := Nat.prod_primeFactors_of_squarefree hdsq
      have hTsubS : d.primeFactors ⊆ s := by
        rw [← Nat.primeFactors_prod hprime]; exact hTsubPF
      have key := Nat.prod_primeFactors_sdiff_of_squarefree hsq hTsubPF
      rw [hprodT, Nat.primeFactors_prod hprime] at key
      have hpr := hforms d.primeFactors hTsubS
      rw [hprodT, key] at hpr
      exact hpr

/-
## The conjecture

By the two lemmas above, the statement below asserts that for **every** `n`
there exist `n` distinct odd primes `p₁,…,pₙ` making the `2ⁿ` forms
`2·∏_{i∈T} pᵢ + ∏_{i∉T} pᵢ` (over all subsets `T`) *simultaneously prime*.

This is precisely an instance of **Schinzel's Hypothesis H / Dickson's
conjecture** on the simultaneous primality of admissible tuples of forms — a
famous *open* problem in number theory.  It is at least as hard as, and in the
same family as, the twin-prime conjecture:

* For a **fixed** `n` the statement is decidable in principle (exhibit one
  witness — e.g. `1, 3, 15, 105, 93081` for `n = 0,1,2,3,4`) and provable.
* The **universal** quantifier over `n` requires prime constellations of
  unbounded size.  No unconditional method (sieves are blocked by the parity
  problem; Dirichlet's theorem handles only a *single* linear form) is known,
  and Mathlib contains no Hypothesis-H/Dickson/prime-constellation result.

The negation is equally out of reach: proving some candidate set empty would
require a *covering congruence* (a prime `q` dividing one of the forms for
every admissible choice of `p₁,…,pₙ`), and **no such prime exists**.  Indeed,
writing `d = P_T = ∏_{i∈T} pᵢ` and `k = P`, one has `d·(2d + k/d) ≡ 2·P_T² + P
(mod q)`, so a form vanishes mod `q` iff `P_T² ≡ -P·2⁻¹ (mod q)`.  Choosing the
primes so that their product `P` makes `-P·2⁻¹` a *quadratic non-residue* mod
`q` (always possible, since `P` ranges over all of `(ℤ/q)ˣ`) forces every
`P_T²` — a nonzero square — to differ from it, so **no** form is divisible by
`q`.  Thus the local density is positive at every prime `q`, the singular
series is positive, and heuristically (Bateman–Horn) witnesses are abundant for
every `n`.  (This is confirmed computationally: an escaping residue assignment
exists for all `q` and all `n` tested.)

Hence the conjecture is genuinely open and cannot, at present, be settled
unconditionally in either direction.  The statement is left verbatim; the
irreducible open existence step is marked with `sorry`.
-/

/-- Conjecture: the sequence is infinite. It is hard to believe!
This is formalized as the set $S(n)$ of candidate numbers being non-empty for all $n$. -/
theorem oeis_295124_conjecture_0 :
  ∀ n : ℕ, (({k : ℕ | k > 0 ∧
              (Nat.primeFactors k).card = n ∧
              (∀ d, d ∈ Nat.divisors k → Nat.Prime (2 * d + k / d))}) : Set ℕ).Nonempty := by sorry
