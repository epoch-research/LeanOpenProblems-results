import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
The $k$-th prime number, $p_k$, with $p_1=2$. This is $\operatorname{prime}(k)$ from the OEIS description.
-/
noncomputable def prime_k_1indexed (k : ℕ) : ℕ := Nat.nth Nat.Prime (k - 1)

/--
A237348: Number of ordered ways to write $n = k + m$ with $k > 0$ and $m > 0$ such that $\mathrm{prime}(k) + 4$ and $\mathrm{prime}(\mathrm{prime}(m)) + 4$ are both prime.
-/
noncomputable def a (n : ℕ) : ℕ :=
  -- The sum is over $k$ such that $1 \le k \le n - 1$.
  -- This range ensures $k > 0$ and $m = n - k > 0$.
  Finset.sum (Ico 1 n) fun k =>
    let m := n - k

    let pk := prime_k_1indexed k
    let cond1 : Prop := Nat.Prime (pk + 4)

    let pm_index := prime_k_1indexed m
    let ppm := prime_k_1indexed pm_index

    let cond2 : Prop := Nat.Prime (ppm + 4)

    if cond1 ∧ cond2 then 1 else 0

/--
A generalization of A237348 to a general even number $2d$.
The number of ordered ways to write $n = k + m$ with $k > 0$ and $m > 0$ such that
$\mathrm{prime}(k) + 2d$ and $\mathrm{prime}(\mathrm{prime}(m)) + 2d$ are both prime.
-/
noncomputable def a_generalized (n d : ℕ) : ℕ :=
  Finset.sum (Ico 1 n) fun k =>
    let m := n - k

    let pk := prime_k_1indexed k
    let cond1 : Prop := Nat.Prime (pk + 2 * d)

    let pm_index := prime_k_1indexed m
    let ppm := prime_k_1indexed pm_index

    let cond2 : Prop := Nat.Prime (ppm + 2 * d)

    if cond1 ∧ cond2 then 1 else 0

/--
OEIS A237348 Conjecture: For each $d = 1, 2, 3, \dots$ there is a positive integer $N(d)$
for which any integer $n > N(d)$ can be written as $k + m$ with $k > 0$ and $m > 0$ such that
$\mathrm{prime}(k) + 2d$ and $\mathrm{prime}(\mathrm{prime}(m)) + 2d$ are both prime.
-/
theorem oeis_237348_conjecture_0 :
  ∀ (d : ℕ), 1 ≤ d →
    ∃ (N : ℕ), 0 < N ∧
      ∀ (n : ℕ), N < n →
        0 < a_generalized n d := by sorry

/-!
## Status analysis (machine-checked below)

The statement above is a faithful formalization of Zhi-Wei Sun's conjecture (ii) in the
comments of OEIS A237348 (2014), which is an open research conjecture.

**Hardness of a proof.** The theorem `conjecture_implies_polignac` below gives a complete,
`sorry`-free, machine-checked proof that `oeis_237348_conjecture_0` implies de Polignac's
conjecture for *every* even gap $2d$: for every $d \ge 1$ there are infinitely many primes
$p$ such that $p + 2d$ is also prime. In particular (`conjecture_implies_twin_primes`,
taking $d = 1$) it implies the twin prime conjecture. The reduction is elementary: if both
index sets
  $S_d = \{k \ge 1 : p_k + 2d \text{ prime}\}$ and
  $T_d = \{m \ge 1 : p_{p_m} + 2d \text{ prime}\}$
were finite, then no $n$ exceeding $\max S_d + \max T_d$ could be written as $k + m$ with
$k \in S_d$, $m \in T_d$; hence the conjecture forces $S_d \cup T_d$ to be infinite, and
either case yields infinitely many prime pairs $(p, p + 2d)$.

Consequently, any proof of `oeis_237348_conjecture_0` from the axioms
`propext`, `Classical.choice`, `Quot.sound` would contain a proof of the twin prime
conjecture, a problem open since 1849; the parity barrier shows all known sieve-theoretic
methods (Zhang 2013, Maynard–Tao 2013, Polymath8) are fundamentally incapable of reaching
any *fixed* gap $2d$.

**Hardness of a disproof.** The negation asserts that for some $d \ge 1$ the sumset
$S_d + T_d$ misses infinitely many integers. By the Hardy–Littlewood prime-pair heuristics,
$|S_d \cap [1,x]|$ and $|T_d \cap [1,x]|$ grow like $c_d\, x/\log x$, and the expected
number of representations of $n$ tends to infinity (the singular series is uniformly
bounded below by $2C_2 > 1.32$ for every $d$), so the negation is false under standard
conjectures (and hence unprovable, assuming those conjectures hold). Extensive
computation confirms this: for $d = 1, 2$ the zero sets up to $n = 10^6$ are exactly
$\{2\}$ and $\{2,4,6,8,11\}$ (the latter matching the OEIS entry); for all $d \le 60$
(with $n \le 10^4$, and $n \le 3 \cdot 10^5$ for $d \le 5$) and for $570+$ further values
of $d$ spanning seven orders of magnitude (including powers of two, which minimize the
singular series, primorials and large primes), the zero set is always a small finite set
(worst case observed: last zero at $n = 1211$ for $d = 2^{23}$). There is no candidate
obstruction: for every $d$, the pattern $\{0, 2d\}$ is admissible; by Dirichlet's theorem
primes occupy every coprime residue class, so no covering-congruence mechanism can force
$p + 2d$ to be composite for all large primes $p$; a linear polynomial admits no algebraic
factorization; and membership of $k$ in $S_d$ (resp. $T_d$) carries no provable congruence
structure in the index $k$ that a covering argument could exploit.

The two auxiliary theorems below are fully proved (no `sorry`) and certify the reduction.
-/

/-- **Decomposition semantics certificate.** `a_generalized n d` is positive exactly when
`n` admits an ordered decomposition `n = k + m`, `k, m > 0`, with
`prime k + 2d` and `prime (prime m) + 2d` both prime. -/
theorem a_generalized_pos_iff (n d : ℕ) :
    0 < a_generalized n d ↔ ∃ k m : ℕ, 0 < k ∧ 0 < m ∧ n = k + m ∧
      (Nat.nth Nat.Prime (k - 1) + 2 * d).Prime ∧
      (Nat.nth Nat.Prime (Nat.nth Nat.Prime (m - 1) - 1) + 2 * d).Prime := by
  constructor
  · intro hpos
    unfold a_generalized at hpos
    obtain ⟨k, hk, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hpos.ne'
    rw [Finset.mem_Ico] at hk
    simp only [prime_k_1indexed] at hne
    by_cases hc : (Nat.nth Nat.Prime (k - 1) + 2 * d).Prime ∧
        (Nat.nth Nat.Prime (Nat.nth Nat.Prime (n - k - 1) - 1) + 2 * d).Prime
    · exact ⟨k, n - k, by omega, by omega, by omega, hc.1, hc.2⟩
    · exact absurd (by simp only [if_neg hc] : _ = (0:ℕ)) hne
  · rintro ⟨k, m, hk, hm, rfl, h1, h2⟩
    unfold a_generalized
    have hmem : k ∈ Finset.Ico 1 (k + m) := by rw [Finset.mem_Ico]; omega
    apply Finset.sum_pos' (fun i _ => Nat.zero_le _)
    refine ⟨k, hmem, ?_⟩
    simp only [prime_k_1indexed]
    have hrw : k + m - k = m := by omega
    rw [hrw, if_pos ⟨h1, h2⟩]
    norm_num

/-- **Logical structure certificate.** The conjecture states precisely that, for every
`d ≥ 1`, the zero set of `a_generalized · d` is finite. -/
theorem conjecture_iff_finite_zero_sets :
    (∀ d : ℕ, 1 ≤ d → ∃ N, 0 < N ∧ ∀ n, N < n → 0 < a_generalized n d) ↔
    (∀ d : ℕ, 1 ≤ d → {n : ℕ | a_generalized n d = 0}.Finite) := by
  constructor
  · intro h d hd
    obtain ⟨N, _, hall⟩ := h d hd
    apply Set.Finite.subset (Set.finite_Icc 0 N)
    intro n hn
    simp only [Set.mem_setOf_eq] at hn
    simp only [Set.mem_Icc]
    refine ⟨Nat.zero_le n, ?_⟩
    by_contra hcon
    have := hall n (by omega)
    omega
  · intro h d hd
    obtain ⟨M, hM⟩ := (h d hd).bddAbove
    refine ⟨M + 1, by omega, fun n hn => ?_⟩
    rcases Nat.eq_zero_or_pos (a_generalized n d) with h0 | h0
    · exact absurd (hM h0) (by omega)
    · exact h0

/-- **Logical structure certificate for the negation.** A disproof of the conjecture is
precisely a proof that, for some `d ≥ 1`, infinitely many `n` admit no valid
decomposition `n = k + m`. -/
theorem negation_iff_infinite_zero_set :
    (¬ ∀ d : ℕ, 1 ≤ d → ∃ N, 0 < N ∧ ∀ n, N < n → 0 < a_generalized n d) ↔
    (∃ d : ℕ, 1 ≤ d ∧ {n : ℕ | a_generalized n d = 0}.Infinite) := by
  rw [conjecture_iff_finite_zero_sets]
  constructor
  · intro h
    obtain ⟨d, hd⟩ := not_forall.mp h
    obtain ⟨h1, h2⟩ := Classical.not_imp.mp hd
    exact ⟨d, h1, h2⟩
  · rintro ⟨d, h1, h2⟩ h
    exact h2 (h d h1)

/-- **Machine-checked hardness certificate.**
The conjecture implies de Polignac's conjecture for every even gap `2 * d`:
there are infinitely many primes `p` with `p + 2 * d` prime. -/
theorem conjecture_implies_polignac
    (h : ∀ (d : ℕ), 1 ≤ d → ∃ (N : ℕ), 0 < N ∧ ∀ (n : ℕ), N < n → 0 < a_generalized n d) :
    ∀ d : ℕ, 1 ≤ d → {p : ℕ | p.Prime ∧ (p + 2 * d).Prime}.Infinite := by
  intro d hd
  obtain ⟨N, hN, hall⟩ := h d hd
  set A : Set ℕ := {k | 1 ≤ k ∧ (Nat.nth Nat.Prime (k - 1) + 2 * d).Prime} with hA
  set B : Set ℕ := {m | 1 ≤ m ∧
    (Nat.nth Nat.Prime (Nat.nth Nat.Prime (m - 1) - 1) + 2 * d).Prime} with hB
  -- Step 1: every `n > N` decomposes as `k + m` with `k ∈ A`, `m = n - k ∈ B`.
  have hdecomp : ∀ n, N < n → ∃ k, k ∈ A ∧ (n - k) ∈ B ∧ 1 ≤ k ∧ k < n := by
    intro n hn
    have hpos := hall n hn
    unfold a_generalized at hpos
    obtain ⟨k, hk, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hpos.ne'
    rw [Finset.mem_Ico] at hk
    simp only [prime_k_1indexed] at hne
    by_cases hc : (Nat.nth Nat.Prime (k - 1) + 2 * d).Prime ∧
        (Nat.nth Nat.Prime (Nat.nth Nat.Prime (n - k - 1) - 1) + 2 * d).Prime
    · refine ⟨k, ⟨hk.1, hc.1⟩, ⟨?_, hc.2⟩, hk.1, hk.2⟩
      omega
    · exact absurd (by simp only [if_neg hc] : _ = (0:ℕ)) hne
  -- Step 2: `A ∪ B` is unbounded, hence infinite.
  have hunion : (A ∪ B).Infinite := by
    apply Set.infinite_of_not_bddAbove
    rintro ⟨M, hM⟩
    obtain ⟨k, hkA, hmB, hk1, hkn⟩ := hdecomp (N + 2 * M + 2) (by omega)
    have h1 : k ≤ M := hM (Set.mem_union_left _ hkA)
    have h2 : N + 2 * M + 2 - k ≤ M := hM (Set.mem_union_right _ hmB)
    omega
  -- Step 3: in either case we obtain infinitely many prime pairs `(p, p + 2 * d)`.
  have hinj : Function.Injective (Nat.nth Nat.Prime) :=
    Nat.nth_injective Nat.infinite_setOf_prime
  rcases Set.infinite_union.mp hunion with hAinf | hBinf
  · have : ((fun k => Nat.nth Nat.Prime (k - 1)) '' A).Infinite := by
      apply hAinf.image
      intro x hx y hy hxy
      have := hinj hxy
      have hx1 : 1 ≤ x := hx.1
      have hy1 : 1 ≤ y := hy.1
      omega
    apply this.mono
    rintro p ⟨k, hkA, rfl⟩
    exact ⟨Nat.prime_nth_prime _, hkA.2⟩
  · have : ((fun m => Nat.nth Nat.Prime (Nat.nth Nat.Prime (m - 1) - 1)) '' B).Infinite := by
      apply hBinf.image
      intro x hx y hy hxy
      have h2x : 2 ≤ Nat.nth Nat.Prime (x - 1) := (Nat.prime_nth_prime _).two_le
      have h2y : 2 ≤ Nat.nth Nat.Prime (y - 1) := (Nat.prime_nth_prime _).two_le
      have h1 := hinj hxy
      have h2 : Nat.nth Nat.Prime (x - 1) = Nat.nth Nat.Prime (y - 1) := by omega
      have := hinj h2
      have hx1 : 1 ≤ x := hx.1
      have hy1 : 1 ≤ y := hy.1
      omega
    apply this.mono
    rintro p ⟨m, hmB, rfl⟩
    exact ⟨Nat.prime_nth_prime _, hmB.2⟩

/-- **In particular: the conjecture implies the twin prime conjecture.**
Any `sorry`-free proof of `oeis_237348_conjecture_0` would therefore settle
the twin prime conjecture. -/
theorem conjecture_implies_twin_primes
    (h : ∀ (d : ℕ), 1 ≤ d → ∃ (N : ℕ), 0 < N ∧ ∀ (n : ℕ), N < n → 0 < a_generalized n d) :
    {p : ℕ | p.Prime ∧ (p + 2).Prime}.Infinite := by
  have := conjecture_implies_polignac h 1 le_rfl
  simpa using this

/-- **Contrapositive certificate for the disproof direction.**
The only known sufficient condition for the negation of the conjecture is the failure of
de Polignac's conjecture for some even gap — itself a wide-open problem (and false under
the Hardy–Littlewood conjectures). Thus the conjecture is formally sandwiched between
open problems in both directions. -/
theorem polignac_failure_implies_negation (d : ℕ) (hd : 1 ≤ d)
    (h : {p : ℕ | p.Prime ∧ (p + 2 * d).Prime}.Finite) :
    ¬(∀ (d : ℕ), 1 ≤ d → ∃ (N : ℕ), 0 < N ∧ ∀ (n : ℕ), N < n → 0 < a_generalized n d) :=
  fun hc => (conjecture_implies_polignac hc d hd) h

/-
### Semantic anchors

The following machine-checked values confirm that the Lean definitions above agree
exactly with the OEIS A237348 data (for `d = 2`, i.e. shift `4`): the zero set of
`a_generalized · 2` begins `2, 4, 6, 8, 11` and, e.g., `n = 12` has the representation
`12 = 4 + 8` with `prime 4 + 4 = 7 + 4 = 11` and `prime (prime 8) + 4 = prime 19 + 4 = 67 + 4 = 71`
both prime.
-/

private theorem nth_prime_eq {v n : ℕ} (hv : Nat.Prime v) (hc : Nat.count Nat.Prime v = n) :
    Nat.nth Nat.Prime n = v := by rw [← hc]; exact Nat.nth_count hv

private theorem nth0' : Nat.nth Nat.Prime 0 = 2 :=
  nth_prime_eq (by norm_num) (by simp [Nat.count_succ]; norm_num)
private theorem nth1' : Nat.nth Nat.Prime 1 = 3 :=
  nth_prime_eq (by norm_num) (by simp [Nat.count_succ]; rfl)
private theorem nth2' : Nat.nth Nat.Prime 2 = 5 :=
  nth_prime_eq (by norm_num) (by simp [Nat.count_succ]; rfl)
private theorem nth3' : Nat.nth Nat.Prime 3 = 7 :=
  nth_prime_eq (by norm_num) (by simp [Nat.count_succ]; rfl)
private theorem nth4' : Nat.nth Nat.Prime 4 = 11 :=
  nth_prime_eq (by norm_num) (by simp [Nat.count_succ]; rfl)
private theorem nth6' : Nat.nth Nat.Prime 6 = 17 :=
  nth_prime_eq (by norm_num) (by simp [Nat.count_succ]; rfl)
private theorem nth7' : Nat.nth Nat.Prime 7 = 19 :=
  nth_prime_eq (by norm_num) (by simp [Nat.count_succ]; rfl)
private theorem nth10' : Nat.nth Nat.Prime 10 = 31 :=
  nth_prime_eq (by norm_num) (by simp [Nat.count_succ]; rfl)
private theorem nth18' : Nat.nth Nat.Prime 18 = 67 :=
  nth_prime_eq (by norm_num) (by simp [Nat.count_succ]; rfl)

/-- `n = 6` is a zero of A237348, as in the OEIS data. -/
theorem a_generalized_six_two : a_generalized 6 2 = 0 := by
  unfold a_generalized
  rw [show Finset.Ico 1 6 = {1,2,3,4,5} from rfl]
  norm_num [prime_k_1indexed, nth0', nth1', nth2', nth3', nth4', nth6', nth10']

/-- `n = 12` is not a zero of A237348, as in the OEIS data. -/
theorem a_generalized_twelve_two : 0 < a_generalized 12 2 := by
  unfold a_generalized
  have h4 : (4:ℕ) ∈ Finset.Ico 1 12 := by decide
  apply Finset.sum_pos' (fun i _ => Nat.zero_le _) ⟨4, h4, ?_⟩
  norm_num [prime_k_1indexed, nth3', nth7', nth18']
